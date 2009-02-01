
import std.random;
import std.stdio;

import position;
import trapmoves;

ulong random_bit(ulong bits)
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

int get_captures(Position pos)
{
    int start_pop = population(pos);
    int[Piece.max+1] piece_count;
    for (Piece p=Piece.WRABBIT; p <= Piece.BELEPHANT; p++)
    {
        piece_count[p] = pop2count(start_pop, p);
    }
    PosStore moves = pos.get_moves();
    int pieceoffset = (pos.side^1) * 6;
    int victims = 0;
    foreach (Position res; moves)
    {
        int rpop = population(res);
        if (rpop != start_pop)
        {
            for (int p=Piece.WRABBIT + pieceoffset; p <= Piece.WELEPHANT + pieceoffset; p++)
            {
                if (piece_count[p] != pop2count(rpop, cast(Piece)(p)))
                {
                    victims |= 1 << p;
                }
            }
        }
    }
    moves.free_items();
    delete moves;

    return victims;
}

int main(char[][] args)
{
    Position pos = new Position();
    TrapGenerator trap_gen = new TrapGenerator();
    int pos_count;
    while (true)
    {
        gen_position(pos);
        pos_count += 1;
        writefln("%dw", pos_count);
        writefln(pos.to_long_str());
        int victims = get_captures(pos);
        int svictims = 0;
        trap_gen.find_captures(pos, pos.side);
        for (int i=0; i < trap_gen.num_captures; i++)
        {
            if (trap_gen.captures[i].length <= pos.stepsLeft)
            {
                svictims |= 1 << trap_gen.captures[i].victim;
            }
        }
        if (victims != svictims)
        {
            for (Piece pt=Piece.WRABBIT; pt <= Piece.BELEPHANT; pt++)
            {
                if ((victims & (1 << pt)) && !(svictims & (1 << pt)))
                {
                    writefln("Capture of %s missed by static capture", "xRCDHMErcdhme"[pt]);
                }
                else if (!(victims & (1 << pt)) && (svictims & (1 << pt)))
                {
                    writefln("Incorrect capture of %s reported by static capture", "xRCDHMErcdhme"[pt]);
                }
            }
            return 0;
        }
        pos.clear();
    }
}


