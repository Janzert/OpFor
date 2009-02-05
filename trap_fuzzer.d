
import std.random;
import std.stdio;

import position;
import trapmoves;
import trap_check;


private ulong random_bit(ulong bits)
{
    int num = popcount(bits);
    int bix = rand() % num;
    ulong b;
    for (int i=0; i <= bix; i++)
    {
        b = bits & -bits;
        bits ^= b;
    }
    return b;
}

void gen_position(inout Position pos)
{
    Piece[] white_pieces;
    white_pieces = [Piece.WELEPHANT, Piece.WCAMEL, Piece.WHORSE,
        Piece.WHORSE, Piece.WDOG, Piece.WDOG, Piece.WCAT, Piece.WCAT].dup;
    Piece[] black_pieces;
    black_pieces = [Piece.BELEPHANT, Piece.BCAMEL, Piece.BHORSE,
        Piece.BHORSE, Piece.BDOG, Piece.BDOG, Piece.BCAT, Piece.BCAT].dup;

    ulong[] restricted_sqr = [0UL, RANK_8, 0, 0, 0, 0, 0, RANK_1, 0, 0, 0, 0, 0];
    int[] num_piece = [0, 8, 2, 2, 2, 1, 1, 8, 2, 2, 2, 1, 1];

    ulong empty = ALL_BITS_SET;
    ulong sqb;
    for (Piece pt=Piece.WRABBIT; pt <= Piece.BELEPHANT; pt++)
    {
        int pt_side = pt < Piece.BRABBIT ? Side.WHITE : Side.BLACK;
        for (int n=0; n < num_piece[pt]; n++)
        {
            sqb = random_bit(empty & ~(TRAPS
                        & ~neighbors_of(pos.placement[pt_side]))
                        & ~restricted_sqr[pt]);
            empty ^= sqb;
            pos.place_piece(pt, sqb);
        }
    }
    pos.set_steps_left(4);
}

int main(char[][] args)
{
    Position pos = new Position();
    StepList steps = StepList.allocate();
    TrapCheck cap_checker = new TrapCheck();
    int pos_count;
    while (true)
    {
        gen_position(pos);
        pos_count += 1;
        writefln("%dw", pos_count);
        writefln(pos.to_long_str());
        cap_checker.check_captures(pos, pos, steps);
        assert (steps.numsteps == 0);
        pos.clear();
    }
    return 0;
}


