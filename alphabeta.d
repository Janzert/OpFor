
import std.conv;
import std.stdio;

import tango.core.Memory;

import goalsearch;
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

    long hits, miss, collisions;

    this (Logger l, int size)
    {
        log = l;
        set_size(size);
        hits = miss = collisions = 0;
    }

    void set_size(int size)
    {
        store.length = 0;
        store.length = (size*1024*1024) / TTNode.sizeof;
        store.length = store.length < 1 ? 1 : store.length;
        GC.setAttr(cast(void*)store, GC.BlkAttr.NO_SCAN);
        age();
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
                    if (store[key].zobrist == pos.zobrist
                            || (!node.aged && node.depth > store[key].depth))
                    {
                        node = &store[key];
                    }
                }
            }
        }
        if (node.zobrist == pos.zobrist)
        {
            hits += 1;
        }
        else if (node.aged)
        {
            miss += 1;
        } else {
            collisions += 1;
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
    uint[2] pass_score;

    uint get_score(Position pos, Step step)
    {
        if (step.frombit == INV_STEP)
            return pass_score[pos.side];
        return score[pos.side][step.fromix][step.toix];
    }

    void update(Position pos, Step step, int depth)
    {
        if (step.frombit == INV_STEP)
            pass_score[pos.side] += depth + 1;
        else
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
            pass_score[s] /= 10;
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
        if (height >= MAX_HEIGHT)
            return;

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

    static StepSorter allocate(int d, Position p, Step* b, Step* l)
    {
        if (reservesize)
        {
            reservesize--;
            StepSorter ss = reserve[reservesize];
            reserve[reservesize] = null;
            ss.init(d, p, b, l);
            return ss;
        }

        return new StepSorter(d, p, b, l);
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
    static bool prune_unrelated = true;

    int height;
    Position pos;
    StepList steps;
    Step best;

    bool remove_unrelated;
    Step* last;
    private ulong last_tneighbors;

    StepList capture_steps;
    bool captures_generated;
    int capture_num;

    private ulong considered[64];

    int num;
    int stage;
    int history_num;

    int sub_ix;

    this(int d, Position p, Step* b, Step* l)
    {
        init(d, p, b, l);
    }

    void init(int h, Position p, Step* b, Step* l)
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
        last = l;
        if (last !is null)
            last_tneighbors = neighbors_of(last.tobit);
        if (prune_unrelated
                && pos.stepsLeft == 3
                && !pos.inpush
                && last !is null)
            remove_unrelated = true;
        else
            remove_unrelated = false;
        num = 0;
        stage = 0;
        captures_generated = 0;
        history_num = 0;
        sub_ix = 0;
        for (int i=0; i < 64; i++)
            considered[i] = 0UL;
    }

    private bool is_related(Step* s)
    {
        // using this to check only the second step in a move still misses
        // some 3 step combos where the 3rd step depends on the first 2 steps
        // but neither of the first two depend on each other
        ulong to = s.tobit;
        ulong from = s.frombit;
        if (from == INV_STEP)
            return false;
        // Allow a step if:
        // Piece steps into last from
        // Same piece as last step
        // Last step supported this step onto a trap
        // Last step was to a neighbor of this from
        // Last step allowed this piece to step away from a trap
        if ((((to | from) & (last.tobit | last_tneighbors))
                    && ((to == last.frombit) || (last.tobit == from)
                        || ((to & TRAPS & last_tneighbors)
                            && !(pos.placement[pos.side]
                                & neighbors_of(to)
                                & ~from & ~last.tobit))
                        || (from & last_tneighbors)))
                || (last_tneighbors & neighbors_of(from) & TRAPS
                    & pos.placement[pos.side])
                || ((last.frombit & TRAPS)
                    && (from & neighbors_of(last.frombit)
                        & pos.placement[pos.side])
                    && !(neighbors_of(last.frombit)
                        & pos.placement[pos.side]
                        & ~from & ~last.tobit)))
            return true;
        return false;
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
                                Step* nstep = capture_steps.newstep();
                                *nstep = trap_search.captures[i].first_step;
                            }
                        }
                        trap_search.clear();
                        capture_num = 0;
                        captures_generated = true;
                    }

                    while (capture_num < capture_steps.numsteps)
                    {
                        Step* cstep = &capture_steps.steps[capture_num];
                        if (considered[cstep.fromix] & cstep.tobit)
                        {
                            capture_num++;
                            continue;
                        }

                        int bix = num;
                        while ((bix < steps.numsteps)
                                && (steps.steps[bix] != *cstep))
                        {
                            bix++;
                        }

                        if (bix < steps.numsteps)
                        {
                            Step tmp = steps.steps[num];
                            steps.steps[num] = steps.steps[bix];
                            steps.steps[bix] = tmp;
                            step = &steps.steps[num++];
                            break;
                        } else {
                            bool had_pull = false; // had the move as a pull or already used in previous step
                            for (int i=num; i < steps.numsteps; i++)
                            {
                                if (cstep.frombit == steps.steps[i].frombit
                                        && (cstep.tobit == steps.steps[i].tobit))
                                {
                                    had_pull = true;
                                    break;
                                }
                            }

                            if (!had_pull)
                            {
                                debug (missing_captures)
                                {
                                    writefln("%s\n%s", "wb"[pos.side], pos.to_long_str());
                                    writefln("step %s, cnum %d, num %d, stepsleft %d lf %s%s",
                                            cstep.toString(true),
                                            capture_num-1, num, pos.stepsLeft,
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
                    if (capture_num < capture_steps.numsteps)
                    {
                        capture_num++;
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
                            if (possible.frombit != INV_STEP
                                    && considered[possible.fromix] & possible.tobit)
                                continue;
                            if (remove_unrelated && !is_related(possible))
                                continue;
                            int bix = num;
                            while (bix < steps.numsteps && steps.steps[bix] != *possible)
                            {
                                bix++;
                            }
                            if (bix < steps.numsteps)
                            {
                                steps.steps[bix] = steps.steps[num];
                                steps.steps[num] = *possible;
                                num++;
                                step = possible;

                                if (sub_ix > 1)
                                {
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
                stage++;
            case 3:
                if (remove_unrelated)
                {
                    int s=num;
                    while (s < steps.numsteps)
                    {
                        Step* tstep = &steps.steps[s];
                        if ((tstep.frombit != INV_STEP
                                    && (considered[tstep.fromix] & tstep.tobit))
                                || !is_related(tstep))
                        {
                            steps.numsteps--;
                            *tstep = steps.steps[steps.numsteps];
                        } else {
                            s++;
                        }
                    }
                    remove_unrelated = false;
                    if (num == steps.numsteps)
                    {
                        return null;
                    }
                }
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

                    step = &steps.steps[num++];
                    history_num++;
                    break;
                }
                stage++;
             default:
                step = &steps.steps[num++];
        }

        if (step.frombit != INV_STEP)
            considered[step.fromix] |= step.tobit;
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
    GoalSearchDT goal_search;

    Position nullmove;
    int max_depth;

    ulong nodes_searched;
    ulong tthits;

    ulong check_nodes;
    uint check_interval = 100000;
    bool delegate() should_abort;

    bool use_lmr = true;
    bool use_nmh = true;
    bool use_early_beta = true;

    this(Logger l)
    {
        logger = l;
        StepSorter.logger = l;
        ttable = new TransTable(l, 10);
        cuthistory = new HistoryHeuristic();
        StepSorter.cuthistory = cuthistory;
        trap_search = new TrapGenerator();
        StepSorter.trap_search = trap_search;
        goal_search = new GoalSearchDT();
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
            case "use_early_beta":
                use_early_beta = cast(bool)toInt(value);
                break;
            case "use_killers":
                StepSorter.use_killers = cast(bool)(toInt(value));
                break;
            case "prune_unrelated":
                StepSorter.prune_unrelated = cast(bool)(toInt(value));
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

    int static_eval(Position pos)
    {
        throw new Exception("eval must be implemented");
    }

    int logged_eval(Position pos)
    {
        throw new Exception("eval must be implemented");
    }

    int alphabeta(Position pos, int depth, int alpha, int beta, int height, Step* last_step = null)
    {
        nodes_searched++;
        int score = MIN_SCORE;
        if (pos.is_endstate() && (pos.stepsLeft == 4
                    || !pos.is_goal(cast(Side)(pos.side^1))))
        {
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

        bool in_pv = (alpha+1) != beta;
        Step new_best;
        bool stop_search = false;
        if (!pos.inpush && depth < 1)
        {
            if (in_pv && height <= max_depth + 8)
            {
                goal_search.set_start(pos);
                goal_search.find_goals();

                if (goal_search.shortest[pos.side^1] == goal_search.NOT_FOUND
                        || goal_search.shortest[pos.side] <= pos.stepsLeft)
                    stop_search = true;
            } else {
                stop_search = true;
            }
        }
        if (stop_search)
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
            if (use_nmh && depth > 4 && !pos.inpush && pos.stepsLeft < 4)
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

            if (use_early_beta && depth < pos.stepsLeft)
            {
                int short_score = eval(pos, alpha, beta);
                if (short_score >= beta)
                    return short_score;
            }

            StepSorter sorted_steps = StepSorter.allocate(height, pos, prev_best, last_step);
            if (depth > max_depth - 4 && depth > max_depth / 2)
                sorted_steps.remove_unrelated = false;
            Step* curstep = sorted_steps.next_step();
            if (curstep is null)
            {
                // immobilized
                StepSorter.free(sorted_steps);
                return -WIN_SCORE;
            }
            while (curstep !is null)
            {
                int cal;

                Position npos = pos.dup;
                npos.do_step(*curstep);

                if (npos == nullmove)
                {
                    cal = -(WIN_SCORE+1);   // Make this worse than a normal
                                            // loss since it's actually an illegal move
                } else {
                    bool had_nw = false;
                    int first_val;
                    if (use_lmr && !in_pv && depth > 2
                            && sorted_steps.num > 3
                            && sorted_steps.history_num > 1)
                    {
                        use_lmr = false;
                        if (npos.stepsLeft == 4)
                        {
                            Position mynull = nullmove;
                            nullmove = npos.dup;
                            nullmove.do_step(NULL_STEP);

                            first_val = -alphabeta(npos, depth-2, -(alpha+1), -alpha, height+1, curstep);

                            Position.free(nullmove);
                            nullmove = mynull;
                        } else {
                            first_val = alphabeta(npos, depth-2, alpha, alpha+1, height+1, curstep);
                        }
                        had_nw = true;
                        use_lmr = true;
                    }
                    else if (in_pv && sorted_steps.num > 1) // NegaScout
                    {
                        if (npos.stepsLeft == 4)
                        {
                            Position mynull = nullmove;
                            nullmove = npos.dup;
                            nullmove.do_step(NULL_STEP);

                            first_val = -alphabeta(npos, depth-1, -(alpha+1), -alpha, height+1, curstep);

                            Position.free(nullmove);
                            nullmove = mynull;
                        } else {
                            first_val = alphabeta(npos, depth-1, alpha, alpha+1, height+1, curstep);
                        }
                        had_nw = true;
                    }

                    if (!had_nw)
                    {
                        if (npos.stepsLeft == 4)
                        {
                            Position mynull = nullmove;
                            nullmove = npos.dup;
                            nullmove.do_step(NULL_STEP);

                            cal = -alphabeta(npos, depth-1, -beta, -alpha, height+1, curstep);

                            Position.free(nullmove);
                            nullmove = mynull;
                        } else {
                            cal = alphabeta(npos, depth-1, alpha, beta, height+1, curstep);
                        }
                    }
                    else if (first_val > alpha)
                    {
                        if (npos.stepsLeft == 4)
                        {
                            Position mynull = nullmove;
                            nullmove = npos.dup;
                            nullmove.do_step(NULL_STEP);

                            cal = -alphabeta(npos, depth-1, -beta, -(first_val-1), height+1, curstep);

                            Position.free(nullmove);
                            nullmove = mynull;
                        } else {
                            cal = alphabeta(npos, depth-1, first_val-1, beta, height+1, curstep);
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
                curstep = sorted_steps.next_step();
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
        logger.info("TT hits %d misses %d collisions %d", ttable.hits, ttable.miss, ttable.collisions);
    }
}

