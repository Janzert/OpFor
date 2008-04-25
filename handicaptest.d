
import std.stdio;
import std.string;

import position;
import setupboard;

int main(char[][] args)
{
    SetupGenerator setgen = new SetupGenerator();
    setgen.random_all = true;
    Position pos = Position.allocate();
    int tests = 1000000;
    int wins = 0;
    if (args.length < 2)
    {
        writefln("usage: handicaptest <side> <handicap pieces>");
        return 1;
    }
    int side = ifind("wb", args[1][0]);
    if (side == -1)
    {
        writefln("Illegal side given, must be w or b");
        return 1;
    }
    int offset = (side == Side.WHITE) ? 0 : 6;
    Piece[] handicap;
    for (int i = 0; i < args[2].length; i++)
    {
        int p = ifind(".rcdhme", args[2][i]);
        if (p < 1)
        {
            writefln("Illegal piece given, %s", args[1][i]);
            return 1;
        }
        handicap.length = handicap.length + 1;
        handicap[length-1] = cast(Piece)(p + offset);
    }

    for (int i=0; i < tests; i++)
    {
        pos.clear();
        if (side == Side.WHITE)
        {
            setgen.setup_handicap(handicap, pos);
            setgen.setup_board(Side.BLACK, pos);
        } else {
            setgen.setup_board(Side.WHITE, pos);
            setgen.setup_handicap(handicap, pos);
        }
        PlayoutResult result = playout_steps(pos);
        if (result.endscore == 1)
            wins += 1;
    }

    writefln("Win percentage for gold %.2f%%", (cast(double)wins / tests)*100);
    writefln("%d tests with %d wins", tests, wins);

    return 0;
}
