/// Random positions for the fuzzers and the unit tests. They draw from
/// std.random's default generator, so seeding rndGen repeats them.
module randompos;

import std.random : uniform;

import position;

private immutable ulong[] RESTRICTED_SQR = [0UL, RANK_8, 0, 0, 0, 0, 0,
    RANK_1, 0, 0, 0, 0, 0];
private immutable int[] NUM_PIECE = [0, 8, 2, 2, 2, 1, 1, 8, 2, 2, 2, 1, 1];

/// One of the set bits in bits, chosen at random.
ulong random_bit(ulong bits)
{
    int num = popcount(bits);
    int bix = uniform(0, num);
    ulong b;
    for (int i=0; i <= bix; i++)
    {
        b = bits & -bits;
        bits ^= b;
    }
    return b;
}

/// Fills an empty pos with every horse, camel and elephant and a random
/// number of rabbits, cats and dogs. No piece is left on a trap without a
/// friendly neighbor, and no rabbit starts on its goal row.
void random_position(Position pos)
{
    fill(pos, true);
}

/// Fills an empty pos with both full armies, placed as random_position
/// places them.
void full_position(Position pos)
{
    fill(pos, false);
}

private void fill(Position pos, bool random_minors)
{
    ulong empty = ALL_BITS_SET;
    for (Piece pt=Piece.WRABBIT; pt <= Piece.BELEPHANT; pt++)
    {
        int pt_side = pt < Piece.BRABBIT ? Side.WHITE : Side.BLACK;
        int place_num = NUM_PIECE[pt];
        if (random_minors && ((pt_side == Side.WHITE && pt < Piece.WHORSE)
                    || (pt_side == Side.BLACK && pt < Piece.BHORSE)))
            place_num = uniform(0, NUM_PIECE[pt]);
        for (int n=0; n < place_num; n++)
        {
            ulong sqb = random_bit(empty & ~(TRAPS
                        & ~neighbors_of(pos.placement[pt_side]))
                        & ~RESTRICTED_SQR[pt]);
            empty ^= sqb;
            pos.place_piece(pt, sqb);
        }
    }
    pos.set_steps_left(4);
}

/// Fills an empty pos with a position where gold may have a goal: five
/// silver rabbits on silver's home row, the other pieces anywhere not on
/// it, and gold's rabbits anywhere below row 8.
void goal_position(Position pos)
{
    immutable Piece[] white_pieces = [Piece.WELEPHANT, Piece.WCAMEL,
        Piece.WHORSE, Piece.WHORSE, Piece.WDOG, Piece.WDOG, Piece.WCAT,
        Piece.WCAT];
    immutable Piece[] black_pieces = [Piece.BELEPHANT, Piece.BCAMEL,
        Piece.BHORSE, Piece.BHORSE, Piece.BDOG, Piece.BDOG, Piece.BCAT,
        Piece.BCAT];
    ulong goal_squares = RANK_8;
    ulong sqb;
    for (int i=0; i < 5; i++)
    {
        sqb = random_bit(goal_squares);
        goal_squares ^= sqb;
        pos.place_piece(Piece.BRABBIT, sqb);
    }

    ulong squares = ~RANK_8 | goal_squares;
    foreach (piece; white_pieces)
    {
        sqb = random_bit(squares & ~(TRAPS
                    & ~neighbors_of(pos.placement[Side.WHITE])));
        squares ^= sqb;
        pos.place_piece(piece, sqb);
    }
    foreach (piece; black_pieces)
    {
        sqb = random_bit(squares & ~(TRAPS
                    & ~neighbors_of(pos.placement[Side.BLACK])));
        squares ^= sqb;
        pos.place_piece(piece, sqb);
    }
    for (int i=0; i < 8; i++)
    {
        sqb = random_bit(~RANK_8 & squares & ~(TRAPS
                    & ~neighbors_of(pos.placement[Side.WHITE])));
        squares ^= sqb;
        pos.place_piece(Piece.WRABBIT, sqb);
    }
    pos.set_steps_left(4);
}
