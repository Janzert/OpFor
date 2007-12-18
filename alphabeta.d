
import position;

static const int WIN_SCORE = 32000;
static const int MAX_SCORE = 32767;
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
}

class TransTable
{
    TTNode[] store;

    this (int size)
    {
        store.length = (size*1024*1024) / TTNode.sizeof;
    }

    TTNode* get(Position pos)
    {
        int key = pos.zobrist % store.length;
        return &store[key];
    }

    void set(Position pos, int depth, int score, SType type, Step bstep)
    {
        int key = pos.zobrist % store.length;
        if (store[key].aged 
                || store[key].depth < depth
                || store[key].zobrist == pos.zobrist)
        {
            store[key].zobrist = pos.zobrist;
            store[key].depth = depth;
            store[key].score = score;
            store[key].type = type;
            store[key].beststep = bstep;
            store[key].aged = false;
        }
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
    int[64][64][2] score;

    int get_score(Position pos, Step step)
    {
        return score[pos.side][step.fromix][step.toix];
    }

    void update(Position pos, Step step, int depth)
    {
        score[pos.side][step.fromix][step.toix] += 1 << depth;
    }

    void soften()
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


class ABSearch
{
    TransTable ttable;
    // HistoryHeuristic cuthistory;
    Position nullmove;

    ulong nodes_searched;
    ulong tthits;

    bool tournament_rules;

    this(TransTable tt)
    {
        ttable = tt;
        // cuthistory = new HistoryHeuristic();
        nodes_searched = 0;
        tthits = 0;
        tournament_rules = true;
    }

    void sortstep(Position pos, StepList steps, Step* best, int num)
    {
        if (num == 0 && best !is null && (best.frombit != 0 || best.tobit != 0))
        {
            int bix = 0;
            while (bix < steps.numsteps && steps.steps[bix] != *best)
            {
                bix++;
            }
            
            assert (bix < steps.numsteps, "Did not find best step in step list");

            if (bix < steps.numsteps)
            {
                steps.steps[bix].copy(steps.steps[0]);
                steps.steps[0].copy(*best);
            }
        } /* else if (0) {
            int score = cuthistory.get_score(pos, steps.steps[num]);
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
        } */
    }

    int eval(Position pos)
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
            score = eval(pos);
            new_best.clear();
        } else {
            int best_ix;
            StepList steps = StepList.allocate();
            pos.get_steps(steps);
            if (steps.numsteps == 0)
            {
                return -WIN_SCORE;
            }
            for (int six=0; six < steps.numsteps; six++)
            {
                int cal;

                sortstep(pos, steps, prev_best, six);
                Position npos = pos.dup;
                npos.do_step(steps.steps[six]);

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
                    best_ix = six;

                    if (cal > alpha)
                    {
                        alpha = cal;
                        sflag = SType.EXACT;

                        if (cal >= beta)
                        {
                            sflag = SType.BETA;
                            nodes_searched += six;
                            break;
                        }
                    }
                }
            }
            if (sflag != SType.BETA)
            {
                nodes_searched += steps.numsteps;
            }
            /*if (0 && sflag != SType.ALPHA)
            {
                cuthistory.update(pos, steps.steps[best_ix], depth);
            }*/
            
            new_best = steps.steps[best_ix];
            StepList.free(steps);
        }

        ttable.set(pos, depth, score, sflag, new_best);

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
    }
}

