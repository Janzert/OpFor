
import std.conv;
import std.stdio;

import tango.core.Memory;

import logging;
import position;
import trapmoves;

static const int MAX_EVAL_SCORE = 63979;
static const int MIN_WIN_SCORE = 63980;
static const int WIN_SCORE = 64000;
static const int MAX_SCORE = 65000;
static const int MIN_SCORE = -MAX_SCORE;
static const int ABORT_SCORE = MAX_SCORE+100;

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
    Logger log;
    TTNode[] store;

    this (Logger l, int size)
    {
        log = l;
        set_size(size);
    }

    void set_size(int size)
    {
        store.length = 0;
        store.length = (size*1024*1024) / TTNode.sizeof;
        GC.setAttr(cast(void*)store, GC.BlkAttr.NO_SCAN);
        log.log("Set transposition table size to %dMB (%d entries)", size, store.length);
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
                    score[s][f][t] /= 10;
                }
            }
        }
    }
}

class KillerHeuristic
{
    const static int MAX_HEIGHT = 20;
    Step[2][2][MAX_HEIGHT] steps;
    uint[64][64][2][MAX_HEIGHT] history;
    uint[2][2][MAX_HEIGHT] max_history;

    void set_killer(int height, Side side, Step step)
    {
        int step_history = history[height][side][step.fromix][step.toix]++;
        if (step_history > max_history[height][side][0])
        {
            Step* first = &steps[height][side][0];
            if (*first != step)
            {
                if (first.frombit != 0 || first.tobit != 0)
                {
                    steps[height][side][1] = *first;
                    max_history[height][side][1] = max_history[height][side][0];
                }
                *first = step;
            }
            max_history[height][side][0] = step_history;
        } else if (step_history > max_history[height][side][1])
        {
            if (steps[height][side][1] != step)
            {
                steps[height][side][1] = step;
            }
            max_history[height][side][1] = step_history;
        }
    }

    void age()
    {
        for (int d=0; d < MAX_HEIGHT; d++)
        {
            for (int s=0; s < 2; s++)
            {
                for (int n=0; n < 2; n++)
                {
                    max_history[d][s][n] = 0;
                    steps[d][s][n].clear();
                }

                for (int f=0; f < 64; f++)
                {
                    for (int t=0; t < 64; t++)
                    {
                        history[d][s][f][t] = 0;
                    }
                }
            }
        }
    }
}

class StepSorter
{
    private static StepSorter[] reserve;
    private static int reservesize;

    static StepSorter allocate(int d, Position p, Step* b)
    {
        if (reservesize)
        {
            reservesize--;
            StepSorter ss = reserve[reservesize];
            reserve[reservesize] = null;
            ss.init(d, p, b);
            return ss;
        }

        return new StepSorter(d, p, b);
    }

    static void free(StepSorter s)
    {
        if (reserve.length == reservesize)
        {
            reserve.length = (reserve.length+1) * 2;
        }

        StepList.free(s.steps);
        s.steps = null;
        if (s.capture_steps !is null)
        {
            StepList.free(s.capture_steps);
            s.capture_steps = null;
        }
        reserve[reservesize++] = s;
    }

    static Logger logger;

    static KillerHeuristic killers;
    static HistoryHeuristic cuthistory;
    static TrapGenerator trap_search;

    static bool use_killers = true;
    static bool use_history = true;
    static bool capture_first = true;

    int height;
    Position pos;
    StepList steps;
    Step best;

    StepList capture_steps;
    bool captures_generated;
    int capture_num;

    int num;
    int stage;
    int history_num;

    int sub_ix;

    this(int d, Position p, Step* b)
    {
        init(d, p, b);
    }

    void init(int h, Position p, Step* b)
    {
        height = h;
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
        stage = 0;
        captures_generated = 0;
        history_num = 0;
        sub_ix = 0;
    }

    Step* next_step()
    {
        if (num >= steps.numsteps)
        {
            return null;
        }

        Step* step;
        switch (stage)
        {
            case 0:
                if (best.frombit != 0 || best.tobit != 0)
                {
                    int bix = 0;
                    while (bix < steps.numsteps && steps.steps[bix] != best)
                    {
                        bix++;
                    }

                    if (bix < steps.numsteps)
                    {
                        steps.steps[bix] = steps.steps[0];
                        steps.steps[0] = best;
                        num++;
                        step = &best;
                        stage++;
                        break;
                    }
                    logger.warn("Did not find hash step in step list");
                }
                stage++;
            case 1:
                if (capture_first && !pos.inpush)
                {
                    if (!captures_generated)
                    {
                        trap_search.find_captures(pos, pos.side);
                        capture_steps = StepList.allocate();
                        for (int i=0; i < trap_search.num_captures; i++)
                        {
                            if (trap_search.captures[i].length <= pos.stepsLeft
                                        && trap_search.captures[i].first_step != best)
                            {
                                bool duplicate = false;
                                for (int cix=0; cix < capture_steps.numsteps; cix++)
                                {
                                    if (trap_search.captures[i].first_step == capture_steps.steps[cix])
                                    {
                                        duplicate = true;
                                        break;
                                    }
                                }
                                if (!duplicate)
                                {
                                    Step* nstep = capture_steps.newstep();
                                    *nstep = trap_search.captures[i].first_step;
                                }
                            }
                        }
                        capture_num = 0;
                        captures_generated = true;
                    }

                    if (capture_num < capture_steps.numsteps)
                    {
                        while (capture_num < capture_steps.numsteps)
                        {
                            int bix = 0;
                            while ((bix < steps.numsteps)
                                    && (steps.steps[bix] != capture_steps.steps[capture_num]))
                            {
                                bix++;
                            }
                            if (bix < num)
                            {
                                capture_num++;
                                continue;
                            }

                            if (bix < steps.numsteps)
                            {
                                Step tmp = steps.steps[num];
                                steps.steps[num] = steps.steps[bix];
                                steps.steps[bix] = tmp;
                                break;
                            } else {
                                bool had_pull = false; // had the move as a pull or already used in previous step
                                for (int i=0; i < steps.numsteps; i++)
                                {
                                    if (capture_steps.steps[capture_num].frombit == steps.steps[i].frombit
                                            && (capture_steps.steps[capture_num].tobit == steps.steps[i].tobit))
                                    {
                                        had_pull = true;
                                        break;
                                    }
                                }

                                if (!had_pull)
                                {
                                    debug
                                    {
                                        writefln("%s\n%s", "wb"[pos.side], pos.to_long_str());
                                        writefln("step %s, cnum %d, num %d, stepsleft %d lf %s%s",
                                                        capture_steps.steps[capture_num].toString(true),
                                                        capture_num, num, pos.stepsLeft,
                                                        "xRCDHMErcdhme"[pos.lastpiece], ix_to_alg(pos.lastfrom));
                                        if (best.frombit != 0 || best.tobit != 0)
                                            writefln("Have previous best");
                                        else
                                            writefln("No previous best");

                                        writefln("Move steps:");
                                        int sn = 0;
                                        while (sn < steps.numsteps)
                                        {
                                            for (int i=0; i < 10; i++)
                                            {
                                                if (sn < steps.numsteps)
                                                    writef("%s ", steps.steps[sn++].toString(true));
                                                else
                                                    break;
                                            }
                                            writef("\n");
                                        }
                                        writefln("Capture steps:");
                                        sn = 0;
                                        while (sn < capture_steps.numsteps)
                                        {
                                            for (int i=0; i < 10; i++)
                                            {
                                                if (sn < capture_steps.numsteps)
                                                    writef("%s ", capture_steps.steps[sn++].toString(true));
                                                else
                                                    break;
                                            }
                                            writef("\n");
                                        }
                                        writefln("Did not find capture step in list");
                                        assert (0);
                                    }
                                    logger.warn("Did not find capture step in legal step list.");
                                }

                                capture_num++;
                            }
                        }
                        capture_num++;
                        step = &steps.steps[num++];
                        break;
                    } else {
                        StepList.free(capture_steps);
                        capture_steps = null;
                    }
                }
                stage++;
            case 2:
                if (use_killers && !pos.inpush && height < killers.MAX_HEIGHT)
                {
                    bool foundkiller = false;
                    while (sub_ix < 2)
                    {
                        Step* possible = &killers.steps[height][pos.side][sub_ix++];
                        if (possible.frombit != 0 || possible.tobit != 0)
                        {
                            int bix = 0;
                            while (bix < steps.numsteps && steps.steps[bix] != *possible)
                            {
                                bix++;
                            }
                            if (bix < num)
                            {
                                // step already searched
                                continue;
                            }

                            if (bix < steps.numsteps)
                            {
                                steps.steps[bix] = steps.steps[num];
                                steps.steps[num] = *possible;
                                num++;
                                step = possible;

                                if (sub_ix > 1)
                                {
                                    sub_ix = 0;
                                    stage++;
                                }
                                foundkiller = true;
                                break;
                            }
                        } else {
                            break;
                        }
                    }
                    if (foundkiller)
                        break;
                }
                sub_ix = 0;
                stage++;
            case 3:
                if (use_history)
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

                    history_num++;
                    step = &steps.steps[num++];
                    break;
                }
                stage++;
             default:
                step = &steps.steps[num++];
        }

        return step;
    }
}

class ABSearch
{
    Logger logger;
    TransTable ttable;
    HistoryHeuristic cuthistory;
    KillerHeuristic killers;
    TrapGenerator trap_search;

    Position nullmove;
    int max_depth;

    ulong nodes_searched;
    ulong tthits;

    ulong check_nodes;
    uint check_interval = 100000;
    bool delegate() should_abort;

    bool use_lmr = true;
    bool use_nmh = true;

    this(Logger l)
    {
        logger = l;
        StepSorter.logger = l;
        ttable = new TransTable(l, 10);
        cuthistory = new HistoryHeuristic();
        StepSorter.cuthistory = cuthistory;
        trap_search = new TrapGenerator();
        StepSorter.trap_search = trap_search;
        killers = new KillerHeuristic();
        StepSorter.killers = killers;
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
            case "capture_sort":
                StepSorter.capture_first = cast(bool)(toInt(value));
                break;
            case "use_lmr":
                use_lmr = cast(bool)toInt(value);
                break;
            case "use_nmh":
                use_nmh = cast(bool)toInt(value);
                break;
            case "use_killers":
                StepSorter.use_killers = cast(bool)(toInt(value));
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

    int logged_eval(Position pos)
    {
        throw new Exception("eval must be implemented");
    }

    int alphabeta(Position pos, int depth, int alpha, int beta, int height)
    {
        int score = MIN_SCORE;
        if (pos.is_endstate())
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

            if (score == ABORT_SCORE
                    || score == -ABORT_SCORE)
                return ABORT_SCORE;

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
            if (use_nmh && depth > 4 && !pos.inpush)
            {
                Position mynull = nullmove;
                nullmove = pos;
                Position n = pos.dup;
                n.do_step(NULL_STEP);

                use_nmh = false;
                int null_score = -alphabeta(n, depth-4, -beta, -alpha, height+1);
                use_nmh = true;

                Position.free(n);
                nullmove = mynull;

                if (score == -ABORT_SCORE
                        || score == ABORT_SCORE)
                    return ABORT_SCORE;

                if (null_score >= beta)
                    return null_score;
            }

            StepSorter sorted_steps = StepSorter.allocate(height, pos, prev_best);
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
                } else {
                    int first_val;
                    if (use_lmr && depth > 2
                            && sorted_steps.num > 3
                            && sorted_steps.history_num > 1)
                    {
                        use_lmr = false;
                        if (npos.stepsLeft == 4)
                        {
                            Position mynull = nullmove;
                            nullmove = npos.dup;
                            nullmove.do_step(NULL_STEP);

                            first_val = -alphabeta(npos, depth-2, -(alpha+1), -alpha, height+1);

                            Position.free(nullmove);
                            nullmove = mynull;
                        } else {
                            first_val = alphabeta(npos, depth-2, alpha, alpha+1, height+1);
                        }
                        use_lmr = true;
                    } else {
                        first_val = alpha + 1;
                    }

                    if (first_val > alpha)
                    {
                        if (npos.stepsLeft == 4)
                        {
                            Position mynull = nullmove;
                            nullmove = npos.dup;
                            nullmove.do_step(NULL_STEP);

                            cal = -alphabeta(npos, depth-1, -beta, -alpha, height+1);

                            Position.free(nullmove);
                            nullmove = mynull;
                        } else {
                            cal = alphabeta(npos, depth-1, alpha, beta, height+1);
                        }
                    } else {
                        cal = first_val;
                    }
                }

                Position.free(npos);

                if (cal == ABORT_SCORE
                        || cal == -ABORT_SCORE)
                {
                    score = ABORT_SCORE;
                    break;
                }

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

            if (sflag != SType.ALPHA && !pos.inpush)
            {
                cuthistory.update(pos, new_best, depth);
                killers.set_killer(height, pos.side, new_best);
            }

            StepSorter.free(sorted_steps);

            if (score == ABORT_SCORE)
                return ABORT_SCORE;
        }

        node.set(pos, depth, score, sflag, new_best);

        if (nodes_searched > check_nodes)
        {
            if (should_abort())
            {
                return ABORT_SCORE;
            }
            check_nodes += check_interval;
        }

        return score;
    }

    int mtdf(Position pos, int depth, int guess, int upperbound)
    {
        int lowerbound = MIN_SCORE;
        while (lowerbound < upperbound)
        {
            int beta = guess;
            if (guess == lowerbound)
                beta = guess + 1;

            guess = alphabeta(pos, depth, beta-1, beta, 0);
            if (guess < beta)
                upperbound = guess;
            else
                lowerbound = guess;
        }
        return guess;
    }

    void set_depth(int depth)
    {
        max_depth = depth;
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
        killers.age();
    }

    void report()
    {
        logger.info("nodes %d", nodes_searched);
    }
}

