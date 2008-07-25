
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
        writefln("usage: handicaptest <handicap pieces>");
        return 1;
    }

    int[13] handicap = [0, 8,2,2,2,1,1, 8,2,2,2,1,1];
    for (int i = 0; i < args[1].length; i++)
    {
        int p = find(".RCDHMErcdhme", args[1][i]);
        if (p < 1)
        {
            writefln("Illegal piece given, %s", args[1][i]);
            return 1;
        }
        if (handicap[p] == 0)
        {
            writefln("All %s pieces already handicapped");
            return 1;
        }
        handicap[p] -= 1;
    }

    Piece[][2] pieces;
    for (int i=Piece.BELEPHANT; i > Piece.EMPTY; i--)
    {
        int pside = (i < Piece.BRABBIT) ? Side.WHITE : Side.BLACK;
        for (int j=0; j < handicap[i]; j++)
        {
            pieces[pside].length = pieces[pside].length + 1;
            pieces[pside][length-1] = cast(Piece)i;
        }
    }

    writef("Playing ");
    int rnum = 0;
    for (int i = 0; i < pieces[0].length; i++)
    {
        if (pieces[0][i] == Piece.WRABBIT)
            rnum++;
        else
            writef("%s", ".RCDHME"[pieces[0][i]]);
    }
    writef("%dR vs ", rnum);
    rnum = 0;
    for (int i = 0; i < pieces[1].length; i++)
    {
        if (pieces[1][i] == Piece.BRABBIT)
            rnum++;
        else
            writef("%s", ".......rcdhme"[pieces[1][i]]);
    }
    writefln("%dr", rnum);

    for (int i=0; i < tests; i++)
    {
        pos.clear();
        setgen.setup_handicap(pieces[0], pos);
        setgen.setup_handicap(pieces[1], pos);
        PlayoutResult result = playout_steps(pos);
        if (result.endscore == 1)
            wins += 1;
    }

    writefln("Win percentage for gold %.2f%%", (cast(double)wins / tests)*100);
    writefln("%d playouts with %d wins", tests, wins);

    return 0;
}
