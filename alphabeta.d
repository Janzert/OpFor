
import std.conv;
import std.stdio;

import position;
import trapmoves;

static const int WIN_SCORE = 64000;
static const int MAX_SCORE = 65000;
static const int MIN_SCORE = -MAX_SCORE;

enum SType { EXACT, ALPHA, BETA }

struct TTNode
{
    ulong zobrist;
    int depth;
    int score;
    SType type;
    Step beststep;
    bool aged;

    void set(Position pos, int newdepth, int newscore, SType newtype, Step newbstep)
    {
        if (aged 
                || depth < newdepth
                || zobrist == pos.zobrist)
        {
            zobrist = pos.zobrist;
            depth = newdepth;
            score = newscore;
            type = newtype;
            beststep = newbstep;
            aged = false;
        }
    }
}

class TransTable
{
    TTNode[] store;

    this (int size)
    {
        set_size(size);
    }

    void set_size(int size)
    {
        store.length = 0;
        store.length = (size*1024*1024) / TTNode.sizeof;
    }

    TTNode* get(Position pos)
    {
        int key = pos.zobrist % store.length;
        TTNode* node = &store[key];
        if (store[key].zobrist != pos.zobrist)
        {
            key = (key + 1) % store.length;
            if (store[key].zobrist == pos.zobrist)
            {
                node = &store[key];
            } else {
                if (!node.aged && node.depth > store[key].depth)
                {
                    node = &store[key];
                }
                key = (key + 1) % store.length;
                if (store[key].zobrist == pos.zobrist)
                {
                    node = &store[key];
                } else {
                    if (!node.aged && node.depth > store[key].depth)
                    {
                        node = &store[key];
                    }
                    key = (key + 1) % store.length;
                    if (node.aged
                            || store[key].zobrist == pos.zobrist
                            || node.depth > store[key].depth)
                    {
                        node = &store[key];
                    }
                }
            }
        }
        return node;
    }

    void age()
    {
        for (int i=0; i < store.length; i++)
        {
            store[i].aged = true;
        }
    }
}

class HistoryHeuristic
{
    uint[64][64][2] score;

    uint get_score(Position pos, Step step)
    {
        return score[pos.side][step.fromix][step.toix];
    }

    void update(Position pos, Step step, int depth)
    {
        score[pos.side][step.fromix][step.toix] += depth + 1;
    }

    void age()
    {
        for (int s=0; s < 2; s++)
        {
            for (int f=0; f < 64; f++)
            {
                for (int t=0; t < 64; t++)
                {
                    score[s][f][t] /= 2;
                }
            }
        }
    }
}

class StepSorter
{
    private static StepSorter[] reserve;
    private static int reservesize;

    static StepSorter allocate(Position p, Step* b)
    {
        if (reservesize)
        {
            reservesize--;
            StepSorter ss = reserve[reservesize];
            reserve[reservesize] = null;
            ss.init(p, b);
            return ss;
        }

        return new StepSorter(p, b);
    }

    static void free(StepSorter s)
    {
        if (reserve.length == reservesize)
        {
            reserve.length = (reserve.length+1) * 2;
        }

        StepList.free(s.steps);
        s.steps = null;
        reserve[reservesize++] = s;
    }

    static HistoryHeuristic cuthistory;
    TrapGenerator trap_search;

    static bool use_history = true;
    static bool capture_first = false;

    Position pos;
    StepList steps;
    Step best;
    int num;

    this(Position p, Step* b)
    {
        init(p, b);
    }

    void init(Position p, Step* b)
    {
        pos = p;
        steps = StepList.allocate();
        p.get_steps(steps);
        if (b !is null)
        {
            best = *b;
        } else {
            best.clear();
        }
        num = 0;
    }

    Step* next_step()
    {
        Step* step;
        if (num >= steps.numsteps)
        {
            step = null;
        } else if (num == 0 && (best.frombit != 0 || best.tobit != 0))
        {
            int bix = 0;
            while (bix < steps.numsteps && steps.steps[bix] != best)
            {
                bix++;
            }
            
            assert (bix < steps.numsteps, "Did not find best step in step list");

            if (bix < steps.numsteps)
            {
                steps.steps[bix].copy(steps.steps[0]);
                steps.steps[0] = best;
            }
            num++;
            step = &best;
        } else if (use_history)
        {
            uint score = cuthistory.get_score(pos, steps.steps[num]);
            int bix = num;
            for (int i = num+1; i < steps.numsteps; i++)
            {
                int t = cuthistory.get_score(pos, steps.steps[i]);
                if (t > score)
                {
                    score = t;
                    bix = i;
                }
            }

            Step tmp = steps.steps[num];
            steps.steps[num] = steps.steps[bix];
            steps.steps[bix] = tmp;

            step = &steps.steps[num++];
        } else {
            step = &steps.steps[num++];
        }
        
        return step;
    }
}

class ABSearch
{
    TransTable ttable;
    HistoryHeuristic cuthistory;
    TrapGenerator trap_search;

    Position nullmove;

    ulong nodes_searched;
    ulong tthits;

    bool tournament_rules = true;

    this()
    {
        ttable = new TransTable(10);
        cuthistory = new HistoryHeuristic();
        StepSorter.cuthistory = cuthistory;
        trap_search = new TrapGenerator();
        nodes_searched = 0;
        tthits = 0;
    }

    bool set_option(char[] option, char[] value)
    {
        bool handled = true;
        switch (option)
        {
            case "hash":
                try
                {
                    ttable.set_size(toInt(value));
                } catch (ConvError e) { }
                break;
            case "history":
                StepSorter.use_history = cast(bool)(toInt(value));
                break;
            default:
                handled = false;
                break;
        }
        return handled;
    }

    int eval(Position pos, int alpha, int beta)
    {
        throw new Exception("eval must be implemented");
    }

    int alphabeta(Position pos, int depth, int alpha, int beta)
    {
        int score = MIN_SCORE;
        if (pos.is_endstate())
        {
            if (tournament_rules || pos.is_goal())
            {
                // This is actually technically incorrect as it disallows 
                // pushing a rabbit onto then back off of the goal line
                score = pos.endscore() * WIN_SCORE;
                if (pos.side == Side.BLACK)
                {
                    score = -score;
                }
                return score;
            }
        }

        SType sflag = SType.ALPHA;
        TTNode* node = ttable.get(pos);
        Step* prev_best;
        if (node.zobrist == pos.zobrist)
        {
            node.aged = false;
            if (node.depth >= depth)
            {
                if (node.type == SType.EXACT
                    || (node.type == SType.ALPHA && node.score <= alpha)
                    || (node.type == SType.BETA && node.score >= beta))
                {
                    tthits++;
                    return node.score;
                }
            }
            prev_best = &node.beststep;
        }

        Step new_best;
        if (depth < 1 && !pos.inpush)
        {
            score = eval(pos, alpha, beta);
            if (score > alpha)
            {
                alpha = score;
                sflag = SType.EXACT;

                if (score >= beta)
                {
                    sflag = SType.BETA;
                }
            }
            
            new_best.clear();
        } else {
            StepSorter sorted_steps = StepSorter.allocate(pos, prev_best);
            if (sorted_steps.steps.numsteps == 0)
            {
                // immobilized
                return -WIN_SCORE;
            }
            Step* curstep;
            while ((curstep = sorted_steps.next_step()) !is null)
            {
                nodes_searched++;
                int cal;

                Position npos = pos.dup;
                npos.do_step(*curstep);

                if (npos == nullmove)
                {
                    cal = -(WIN_SCORE+1);   // Make this worse than a normal
                                            // loss since it's actually an illegal move
                } else if (npos.stepsLeft == 4)
                {
                    Position mynull = nullmove;
                    nullmove = npos.dup;
                    nullmove.do_step(NULL_STEP);

                    cal = -alphabeta(npos, depth-1, -beta, -alpha);

                    Position.free(nullmove);
                    nullmove = mynull;
                } else {
                    cal = alphabeta(npos, depth-1, alpha, beta);
                }

                Position.free(npos);

                if (cal > score)
                {
                    score = cal;
                    new_best = *curstep;

                    if (cal > alpha)
                    {
                        alpha = cal;
                        sflag = SType.EXACT;

                        if (cal >= beta)
                        {
                            sflag = SType.BETA;
                            break;
                        }
                    }
                }
            }

            if (sflag != SType.ALPHA)
            {
                cuthistory.update(pos, new_best, depth);
            }
            
            StepSorter.free(sorted_steps);
        }

        node.set(pos, depth, score, sflag, new_best);

        return score;
    }

    void prepare()
    {
        nodes_searched = 0;
        tthits = 0;
    }

    void cleanup()
    {
        ttable.age();
        cuthistory.age();
    }
}

