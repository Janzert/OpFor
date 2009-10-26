
import tango.math.random.Random;

import position;

class SetupGenerator
{
    const static ulong[] rabbit_setups = [0x00FF, // Standard
                0x81E7, // 99of9
                0xA5A5]; // Fritz
    const static ulong[] cat_setups = [0x2400,
                0x2400,
                0x42];
    const static ulong[] dog_setups = [0x8100,
                0x18,
                0x18];
    enum RabbitSetup { ANY = -1,
        STANDARD,
        NINETY_NINE,
        FRITZ };

    RabbitSetup rabbit_style = RabbitSetup.ANY;
    bool random_minor = true;
    bool random_all = false;

    int[] setup_weights = [19, 80, 1];

    private ulong gold_to_silver(ulong bitboard)
    {
        const static ulong ROW_1_MASK = 0xFF;
        const static ulong ROW_2_MASK = 0xFF00;
        const static int ROW_1_TO_8 = 56;
        const static int ROW_2_TO_7 = 40;

        return ((bitboard & ROW_2_MASK) << ROW_2_TO_7)
               | ((bitboard & ROW_1_MASK) << ROW_1_TO_8);
    }

    private ulong adjust_side(Side s, ulong bitboard)
    {
        if (s == Side.BLACK)
            return gold_to_silver(bitboard);
        return bitboard;
    }

    private void randomize_minor(Side s, inout Position pos)
    {
        int offset = (s == Side.WHITE) ? 0 : 6;
        ulong squares = pos.bitBoards[Piece.WCAT + offset] | pos.bitBoards[Piece.WDOG + offset];
        pos.place_piece(cast(Piece)(Piece.WCAT + offset), 0, true);
        pos.place_piece(cast(Piece)(Piece.WDOG + offset), 0, true);
        int[] pieces = [Piece.WDOG + offset, Piece.WDOG + offset,
                        Piece.WCAT + offset, Piece.WCAT + offset];
        while (squares)
        {
            ulong sbit = squares & -squares;
            squares ^= sbit;

            int pix = rand.uniformR!(int)(pieces.length);
            int piece = pieces[pix];
            pieces[pix] = pieces[length-1];
            pieces.length = pieces.length - 1;

            pos.place_piece(cast(Piece)piece, sbit);
        }
    }

    private void randomize_all(Side s, inout Position pos)
    {
        int offset = (s == Side.WHITE) ? 0 : 6;
        ulong squares = 0xFFFF;
        if (s == Side.BLACK)
            squares <<= 48;
        for (Piece p = cast(Piece)(Piece.WRABBIT+offset); p <= Piece.WELEPHANT+offset; p++)
        {
            pos.place_piece(p, 0, true);
        }
        Piece[] pieces;
        pieces.length = 16;
        for (int i = 0; i < 8; i++)
        {
            pieces[i] = cast(Piece)(Piece.WRABBIT+offset);
        }
        Piece p = cast(Piece)(Piece.WCAT + offset);
        for (int i = 8; i < 14; i++)
        {
            pieces[i] = p;
            if (i % 2 == 1)
                p++;
        }
        pieces[14] = cast(Piece)(Piece.WCAMEL + offset);
        pieces[15] = cast(Piece)(Piece.WELEPHANT + offset);

        while (squares)
        {
            ulong sbit = squares & -squares;
            squares ^= sbit;

            int pix = rand.uniformR!(int)(pieces.length);
            Piece piece = pieces[pix];
            pieces[pix] = pieces[length-1];
            pieces.length = pieces.length - 1;

            pos.place_piece(piece, sbit);
        }
    }

    void setup_board(Side s, inout Position pos)
    {
        int offset = (s == Side.WHITE) ? 0 : 6;
        RabbitSetup rsetup = rabbit_style;
        if (rsetup == RabbitSetup.ANY)
        {
            int total_weight = 0;
            for (int i=0; i <= RabbitSetup.max; i++)
                total_weight += setup_weights[i];
            int choice_weight = rand.uniformR!(int)(total_weight);
            int cur_weight = 0;
            for (int i=0; i <= RabbitSetup.max; i++)
            {
                cur_weight += setup_weights[i];
                rsetup = cast(RabbitSetup)i;
                if (cur_weight > choice_weight)
                    break;
            }
        }
        pos.place_piece(cast(Piece)(Piece.WRABBIT+offset), adjust_side(s, rabbit_setups[rsetup]), true);
        pos.place_piece(cast(Piece)(Piece.WCAT+offset), adjust_side(s, cat_setups[rsetup]), true);
        pos.place_piece(cast(Piece)(Piece.WDOG+offset), adjust_side(s, dog_setups[rsetup]), true);
        pos.place_piece(cast(Piece)(Piece.WHORSE+offset), adjust_side(s, 0x4200), true);
        pos.place_piece(cast(Piece)(Piece.WCAMEL+offset), adjust_side(s, 0x1000), true);
        pos.place_piece(cast(Piece)(Piece.WELEPHANT+offset), adjust_side(s, 0x0800), true);
        if (s == Side.BLACK)
        {
            if (pos.bitBoards[Piece.WELEPHANT] & 0xE8F0)
            {
                pos.place_piece(Piece.BELEPHANT, 0, true);
                pos.place_piece(Piece.BCAMEL, 0, true);
                pos.place_piece(Piece.BELEPHANT, 0x10000000000000, true);
                pos.place_piece(Piece.BCAMEL, 0x8000000000000, true);
            }
        }

        if (random_minor)
            randomize_minor(s, pos);
        if (random_all)
            randomize_all(s, pos);
    }

    private ulong random_bit(ulong bits)
    {
        int num = popcount(bits);
        int bix = rand.uniformR!(int)(num);
        ulong b;
        for (int i=0; i <= bix; i++)
        {
            b = bits & -bits;
            bits ^= b;
        }
        return b;
    }

    void setup_handicap(Piece[] pieces, inout Position pos)
    {
        ulong squares = 0xFFFF;
        if (pieces[0] > Piece.WELEPHANT)
        {
            squares <<= 48;
        }

        for (int i=0; i < pieces.length; i++)
        {
            ulong sq = random_bit(squares);
            squares ^= sq;
            pos.place_piece(pieces[i], sq);
        }
    }
}

