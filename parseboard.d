
import std.file;
import std.path;
import std.stdio;
import std.string;
import std.perf;
import std.gc;

import goalsearch;
import trap_check;
import trapmoves;
import position;


int main(char[][] args)
{
    if (args.length < 2)
    {
        writefln("usage: %s boardfile", getBaseName(args[0]));
        return 1;
    }
    char[] boardstr;
    try
    {
        boardstr = cast(char[])read(args[1]);
    } catch (FileException fx)
    {
        writefln("A file exception occured: " ~ fx.toString());
        return 2;
    }

    Position pos = position.parse_long_str(boardstr);
    writefln("wb"[pos.side]);
    writefln(pos.to_long_str(true));
    writefln(pos.to_placing_move());
    writefln();
    StepList steps = new StepList();
    pos.get_steps(steps);
    writefln("There are %d initial steps.",
                steps.numsteps);
    ProcessTimesCounter Timer = new ProcessTimesCounter();
    Timer.start();
    PosStore moves = pos.get_moves();
    Timer.stop();
    writefln("%d unique moves.", moves.length);
    writefln("Time to generate moves %.3f seconds", cast(double)Timer.milliseconds / 1000);
    GoalSearchDT gsdt = new GoalSearchDT();
    int shortest_goal = gsdt.NOT_FOUND;
    StepList shortest_move;
    foreach (Position res; moves)
    {
        if (res.endscore() == 1)
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
    std.gc.fullCollect();

    real slow_score = FAME(pos);
    writefln("FAME score: %.2f", slow_score);
    FastFAME ffame = new FastFAME();
    int fast_score = ffame.score(pos);
    if (fast_score != cast(int)(slow_score))
        writefln("Fast FAME score %d != slow fame score %d", fast_score, cast(int)(slow_score));

    if (shortest_goal != gsdt.NOT_FOUND)
        writefln("Side to move goals in %d steps", shortest_goal);
    GoalSearch gsearch = new GoalSearch();
    gsearch.set_start(pos);
    gsearch.find_goals(30);
    if (gsearch.goals_found[Side.WHITE] > 0)
    {
        writefln("White has a goal in %d steps from %s.", gsearch.goal_depth[Side.WHITE][0],
                ix_to_alg(gsearch.rabbit_location[Side.WHITE][0]));
    }
    if (gsearch.goals_found[Side.BLACK] > 0)
    {
        writefln("Black has a goal in %d steps from %s.", gsearch.goal_depth[Side.BLACK][0],
                ix_to_alg(gsearch.rabbit_location[Side.BLACK][0]));
    }
    gsdt.set_start(pos);
    gsdt.find_goals();
    if (gsdt.shortest[Side.WHITE] != gsdt.NOT_FOUND)
        writefln("DT: White has a goal in %d steps.",
                gsdt.shortest[Side.WHITE]);
    if (gsdt.shortest[Side.BLACK] != gsdt.NOT_FOUND)
        writefln("DT: Black has a goal in %d steps.",
                gsdt.shortest[Side.BLACK]);

    if ((shortest_goal != gsdt.NOT_FOUND)
            && (gsdt.shortest[pos.side] != gsdt.NOT_FOUND))
    {
        writefln("checking shortest goal with %s",
                shortest_move.to_move_str(pos));
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
                writefln("step %d", i+1);
                writefln(mpos.to_long_str());
                writefln("Is goal in %d", (shortest_goal - (i+1)));
                writefln("Search found goal in %d", gsdt.shortest[mpos.side]);
                break;
            }
        }
        Position.free(mpos);
        StepList.free(shortest_move);
    }

    TrapGenerator tgen = new TrapGenerator();
    for (Side s = Side.WHITE; s <= Side.BLACK; s++)
    {
        if (tgen.find_captures(pos, s))
        {
            const char[] piece_names = ".RCDHMErcdhme";
            if (s == pos.side)
                writefln("%s can capture:", ["Gold", "Silver"][s]);
            else
                writefln("%s could capture:", ["Gold", "Silver"][s]);
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
                    writefln("  %s at %s in %d steps", piece_names[pos.pieces[i]],
                            ix_to_alg(cast(bitix)i), victims[i]);
                }
            }

            /*
            for (int i=0; i < tgen.num_captures; i++)
            {
                writefln("  %s in %d steps %s first", piece_names[tgen.captures[i].victim],
                        tgen.captures[i].length, tgen.captures[i].first_step);
            }*/
        }
    }
    TrapCheck tcheck = new TrapCheck();
    StepList sl = StepList.allocate();
    tcheck.check_captures(pos, pos, sl);
    StepList.free(sl);

    Timer = new ProcessTimesCounter();
    Timer.start();
    Position gamepos = Position.allocate();
    PlayoutResult result;
    const int tests = 10000;
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
    Timer.stop();
    writefln("Win percentage for side to move %.2f%% with random play.", (cast(double)wins / tests) *100.0);
    writefln("%d playouts took %.2f seconds and averaged %d moves with %d total wins.",  tests, cast(double)Timer.milliseconds / 1000, totalsteps/tests, wins);


    return 0;
}

