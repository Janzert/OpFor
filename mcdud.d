
import std.file;
import std.path;
import std.perf;
import std.stdio;

import position;

struct Move
{
    Position position;
    StepList steps;
    int wins;
    int tests;
}

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

    Position pos = parse_long_str(boardstr);
    writefln("wb"[pos.side]);
    writefln(pos.to_long_str(true));
    PosStore movestore = pos.get_moves();
    writefln("%d possible moves.", movestore.length);

    Move[] moves;
    int mix = 0;
    moves.length = movestore.length;
    foreach (Position mpos; movestore)
    {
        moves[mix].position = mpos;
        moves[mix].steps = movestore.getpos(mpos);
        mix++;
    }

    int stopplays = 0;
    int totalplays = 0;
    int lastdisplay = 0;
    int displaystep = 1000;
    ulong totalsteps = 0;
    PerformanceCounter timer = new PerformanceCounter();
    timer.start();
    Position gamepos = Position.allocate();
    while (true)
    {
        for (mix=0; mix < moves.length; mix++)
        {
            gamepos.copy(moves[mix].position);
            PlayoutResult results = playout_steps(gamepos);
            totalsteps += results.length;
            int score = results.endscore;
            if (gamepos.side == pos.side)
            {
                if (score == 1)
                    moves[mix].wins += 1;
            } else
            {
                if (score == -1)
                    moves[mix].wins += 1;
            }
            moves[mix].tests++;
            totalplays++;

            if (totalplays-lastdisplay >= displaystep)
            {
                timer.stop();
                reportstats(moves, totalplays, totalsteps);
                writefln("%.2f games per second.", displaystep/(cast(double)timer.microseconds/1000000));
                if (stopplays > 0 && totalplays >= stopplays)
                    break;
                lastdisplay = totalplays;
                if (totalplays < 10000)
                    displaystep = 1000;
                else if (totalplays < 100000)
                    displaystep = 10000;
                else if (totalplays < 1000000)
                    displaystep = 100000;
                else
                    displaystep = 250000;
                timer.start();
            }
        }

        if (stopplays > 0 && totalplays >= stopplays)
            break;
    }

    return 0;
}

void reportstats(Move[] moves, int totalplays, ulong totalsteps)
{
    float maxscore = -1;
    int bestmove = 0;
    for (int mix=0; mix < moves.length; mix++)
    {
        float cscore = cast(float)moves[mix].wins / moves[mix].tests;
        if (cscore > maxscore)
        {
            maxscore = cscore;
            bestmove = mix;
        }
    }
    writefln("best move after %d plays with %d tests is %d and %.2f steps per playout.",
                totalplays, moves[bestmove].tests, bestmove, cast(double)totalsteps/totalplays);
    writefln(moves[bestmove].position.to_long_str());
    float winper = cast(float)moves[bestmove].wins /
                    moves[bestmove].tests;
    writefln("Win percentage = %.2f", winper);
}
