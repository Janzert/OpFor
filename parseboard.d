
import std.file;
import std.path;
import std.stdio;
import std.string;
import std.perf;
import std.gc;

import goalsearch;
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
    StepList steps = new StepList();
    pos.get_steps(steps);
    writefln("There are %d steps.", 
                steps.numsteps);
    ProcessTimesCounter Timer = new ProcessTimesCounter();
    //std.gc.disable();
    Timer.start();
    PosStore moves = pos.get_moves();
    Timer.stop();
    writefln("%d unique moves.", moves.length);
    writefln("Gen time %.4f, Steplists %d, Positions %d", cast(double)Timer.milliseconds / 1000,
                StepList.allocated, Position.allocated);
    writefln("reservesize = %d listsize = %d", Position.reserved, Position.rlistsize);
    /*foreach (Position move; moves)
    {
        writefln(move.to_short_str());
    }*/
    delete moves;
    //std.gc.enable();
    std.gc.fullCollect();

    writefln("FAME: %.2f", FAME(pos));
    GoalSearch gsearch = new GoalSearch(30);
    gsearch.set_start(pos);
    gsearch.find_goals();
    if (gsearch.goals_found[Side.WHITE] > 0)
    {
        writefln("White has a goal in %d unopposed steps.", gsearch.goal_depth[Side.WHITE][0]);
    }
    if (gsearch.goals_found[Side.BLACK] > 0)
    {
        writefln("Black has a goal in %d unopposed steps.", gsearch.goal_depth[Side.BLACK][0]);
    }
    
    Timer = new ProcessTimesCounter();
    Timer.start();
    Position gamepos = Position.allocate();
    PlayoutResult result;
    const int tests = 10000;
    int wins = 0;
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
    }
    Position.free(gamepos);
    Timer.stop();
    writefln("Win percentage = %.2f playtime = %.2f", (cast(double)wins / tests) *100.0,
                cast(double)Timer.milliseconds / 1000);
    

    return 0;
}

