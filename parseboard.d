
import tango.core.Exception;
import tango.core.Memory;
import tango.io.device.File;
import tango.io.FilePath;
import tango.io.Stdout;
import tango.time.StopWatch;
import tango.util.Convert;

import logging;
import goalsearch;
import staticeval;
import trap_check;
import trapmoves;
import position;


int main(char[][] args)
{
    if (args.length < 2)
    {
        Stdout.format("usage: %s boardfile [run_playouts]",
                FilePath(args[0]).name);
        return 1;
    }
    int file_arg = 2;
    int steps_left = 4;
    try {
        steps_left = to!(int)(args[1]);
    } catch (ConversionException) {
        file_arg = 1;
    }
    char[] boardstr;
    try
    {
        boardstr = cast(char[])File.get(args[file_arg]);
    } catch (IOException fx)
    {
        Stdout.format("A file exception occured: " ~ fx.toString());
        return 2;
    }
    int run_playouts = 0;
    if (args.length > file_arg + 1)
        run_playouts = to!(int)(args[file_arg + 1]);

    Logger log = new Logger();
    log.to_console = true;

    Position pos = position.parse_long_str(boardstr);
    pos.set_steps_left(steps_left);
    Stdout("wb"[pos.side]).newline;
    Stdout(pos.to_long_str(true)).newline;
    if (pos.stepsLeft != 4) {
        Stdout.format("{} steps left", pos.stepsLeft).newline;
    }
    Stdout(pos.to_placing_move()).newline;
    Stdout.newline;
    Stdout.format("Zobrist hash: {:X}", pos.zobrist).newline;
    StepList steps = new StepList();
    pos.get_steps(steps);
    Stdout.format("There are {} initial steps.",
                steps.numsteps).newline;
    auto timer = new StopWatch();
    timer.start();
    PosStore moves = pos.get_moves();
    timer.stop();
    Stdout.format("{} unique moves.", moves.length).newline;
    Stdout.format("Time to generate moves {:f3} seconds",
            cast(double)timer.microsec / 1000000).newline;
    GoalSearchDT gsdt = new GoalSearchDT();
    int shortest_goal = gsdt.NOT_FOUND;
    StepList shortest_move;
    foreach (Position res; moves)
    {
        if (res.is_goal(pos.side))
        {
            StepList move = moves.getpos(res);
            int goal_len = 0;
            for (int i=0; i < move.numsteps; i++)
            {
                if (move.steps[i].frombit != INV_STEP
                        && move.steps[i].tobit != INV_STEP)
                    goal_len += 1;
            }
            if (goal_len < shortest_goal)
            {
                shortest_goal = goal_len;
                shortest_move = move;
            }
        }
    }
    if (shortest_goal != gsdt.NOT_FOUND)
        shortest_move = shortest_move.dup;
    moves.free_items();
    delete moves;
    GC.collect();

    real slow_score = FAME(pos);
    Stdout.format("FAME score: {}", slow_score).newline;
    FastFAME ffame = new FastFAME();
    int fast_score = ffame.score(pos);
    if (fast_score != cast(int)(slow_score))
        Stdout.format("Fast FAME score {} != slow fame score {}",
                fast_score, cast(int)(slow_score)).newline;
    TrapGenerator tgen = new TrapGenerator();
    StaticEval eval = new StaticEval(log, gsdt, tgen);
    int eval_score = eval.logged_eval(pos);
    Stdout.format("Eval score: {}", eval_score).newline;

    GoalSearch gsearch = new GoalSearch();
    if (shortest_goal != gsdt.NOT_FOUND)
        Stdout.format("Side to move goals in {} steps", shortest_goal).newline;
    gsearch.set_start(pos);
    gsearch.find_goals(30);
    if (gsearch.goals_found[Side.WHITE] > 0)
    {
        Stdout.format("White has a goal in {} steps from {}.",
                gsearch.goal_depth[Side.WHITE][0],
                ix_to_alg(gsearch.rabbit_location[Side.WHITE][0])).newline;
    }
    if (gsearch.goals_found[Side.BLACK] > 0)
    {
        Stdout.format("Black has a goal in {} steps from {}.",
                gsearch.goal_depth[Side.BLACK][0],
                ix_to_alg(gsearch.rabbit_location[Side.BLACK][0])).newline;
    }
    gsdt.set_start(pos);
    gsdt.find_goals();
    if (gsdt.shortest[Side.WHITE] != gsdt.NOT_FOUND)
        Stdout.format("DT: White has a goal in {} steps.",
                gsdt.shortest[Side.WHITE]).newline;
    if (gsdt.shortest[Side.BLACK] != gsdt.NOT_FOUND)
        Stdout.format("DT: Black has a goal in {} steps.",
                gsdt.shortest[Side.BLACK]).newline;

    if (shortest_goal != gsdt.shortest[pos.side])
    {
        Stdout.format("Goal detection error.").newline;
        if (shortest_goal != gsdt.NOT_FOUND)
            Stdout.format("shortest move {}",
                    shortest_move.to_move_str(pos)).newline;
        return 1;
    }

    if ((shortest_goal != gsdt.NOT_FOUND)
            && (gsdt.shortest[pos.side] != gsdt.NOT_FOUND))
    {
        Stdout.format("checking shortest goal with {}",
                shortest_move.to_move_str(pos)).newline;
        Position mpos = pos.dup;
        for (int i=0; i < (shortest_goal-1); i++)
        {
            mpos.do_step(shortest_move.steps[i]);
            if (mpos.inpush)
                continue;
            gsdt.set_start(mpos);
            gsdt.find_goals();
            if (gsdt.shortest[pos.side] != (shortest_goal - (i+1)))
            {
                Stdout.format("step {}", i+1).newline;
                Stdout.format(mpos.to_long_str()).newline;
                Stdout.format("Is goal in {}", (shortest_goal - (i+1))).newline;
                Stdout.format("Search found goal in {}",
                        gsdt.shortest[mpos.side]).newline;
                return 1;
            }
        }
        Position.free(mpos);
        StepList.free(shortest_move);
    }

    for (Side s = Side.WHITE; s <= Side.BLACK; s++)
    {
        if (tgen.find_captures(pos, s))
        {
            const char[] piece_names = ".RCDHMErcdhme";
            if (s == pos.side)
                Stdout.format("{} can capture:", ["Gold", "Silver"][s]).newline;
            else
                Stdout.format("{} could capture:",
                        ["Gold", "Silver"][s]).newline;
            int[64] victims;
            for (int i=0; i < tgen.num_captures; i++)
            {
                bitix vix = bitindex(tgen.captures[i].victim_bit);
                if (victims[vix] == 0 ||
                        victims[vix] > tgen.captures[i].length)
                    victims[vix] = tgen.captures[i].length;
            }
            for (int i=0; i < 64; i++)
            {
                if (victims[i])
                {
                    Stdout.format("  {} at {} in {} steps",
                            piece_names[pos.pieces[i]],
                            ix_to_alg(cast(bitix)i), victims[i]).newline;
                }
            }

            /*
            for (int i=0; i < tgen.num_captures; i++)
            {
                Stdout.format("  {} in {} steps {} first",
                        piece_names[tgen.captures[i].victim],
                        tgen.captures[i].length,
                        tgen.captures[i].first_step).newline;
            }*/
        }
        tgen.clear();
    }
    TrapCheck tcheck = new TrapCheck();
    StepList sl = StepList.allocate();
    tcheck.check_captures(pos, pos, sl);
    StepList.free(sl);

    if (run_playouts)
    {
        timer.start();
        Position gamepos = Position.allocate();
        PlayoutResult result;
        int tests = run_playouts;
        int wins = 0;
        int totalsteps = 0;
        for (int plays = 0; plays < tests; plays++)
        {
            gamepos.copy(pos);
            result = playout_steps(gamepos);
            if (pos.side == Side.WHITE)
            {
                if (result.endscore == 1)
                    wins += 1;
            } else
            {
                if (result.endscore == -1)
                    wins += 1;
            }
            totalsteps += result.length;
        }
        Position.free(gamepos);
        timer.stop();
        Stdout.format("Win percentage for side to move {}% with random play.", (cast(double)wins / tests) *100.0).newline;
        Stdout.format("{} playouts took {} seconds and averaged {} moves with {} total wins.",  tests, cast(double)timer.microsec / 1000000, totalsteps/tests, wins).newline;
    }

    return 0;
}

