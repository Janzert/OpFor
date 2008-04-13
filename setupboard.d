
import std.random;

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

    private ulong gold_to_silver(ulong bitboard)
    {
        const static ulong ROW_1_MASK = 0xFF;
        const static ulong ROW_2_MASK = 0xFF00;
        const static int ROW_1_TO_8 = 56;
        const static int ROW_2_TO_7 = 40;

        return ((bitboard & ROW_2_MASK) << ROW_2_TO_7)
               | ((bitboard & ROW_1_MASK) << ROW_1_TO_8);
    }

    private void randomize_minor(Side s, inout Position pos)
    {
        int offset = (s == Side.WHITE) ? 0 : 6;
        ulong squares = pos.bitBoards[Piece.WCAT + offset] | pos.bitBoards[Piece.WDOG + offset];
        pos.bitBoards[Piece.WCAT + offset] = 0;
        pos.bitBoards[Piece.WDOG + offset] = 0;
        int[] pieces = [Piece.WDOG + offset, Piece.WDOG + offset,
                        Piece.WCAT + offset, Piece.WCAT + offset];
        while (squares)
        {
            ulong sbit = squares & -squares;
            squares ^= sbit;

            int pix = rand() % pieces.length;
            int piece = pieces[pix];
            pieces[pix] = pieces[length-1];
            pieces.length = pieces.length - 1;

            pos.bitBoards[piece] |= sbit;
        }
    }
    
    void setup_white(inout Position pos)
    {
        RabbitSetup rsetup = rabbit_style;
        if (rsetup == RabbitSetup.ANY)
        {
            rsetup = cast(RabbitSetup)(rand() % (RabbitSetup.max + 1));
        }
        pos.bitBoards[Piece.WRABBIT] = rabbit_setups[rsetup];
        pos.bitBoards[Piece.WCAT] = cat_setups[rsetup];
        pos.bitBoards[Piece.WDOG] = dog_setups[rsetup];
        pos.bitBoards[Piece.WHORSE] = 0x4200;
        pos.bitBoards[Piece.WCAMEL] = 0x1000;
        pos.bitBoards[Piece.WELEPHANT] = 0x0800;

        if (random_minor)
        {
            randomize_minor(Side.WHITE, pos);
        }

        pos.update_derived();
    }

    void setup_black(inout Position pos)
    {
        RabbitSetup rsetup = rabbit_style;
        if (rsetup == RabbitSetup.ANY)
        {
            rsetup = cast(RabbitSetup)(rand() % (RabbitSetup.max + 1));
        }
        pos.bitBoards[Piece.BRABBIT] = gold_to_silver(rabbit_setups[rsetup]);
        pos.bitBoards[Piece.BCAT] = gold_to_silver(cat_setups[rsetup]);
        pos.bitBoards[Piece.BDOG] = gold_to_silver(dog_setups[rsetup]);
        pos.bitBoards[Piece.BHORSE] = gold_to_silver(0x4200);
        if (pos.bitBoards[Piece.WELEPHANT] & 0x170F)
        {
            pos.bitBoards[Piece.BELEPHANT] = 0x08000000000000;
            pos.bitBoards[Piece.BCAMEL] = 0x10000000000000;
        } else {
            pos.bitBoards[Piece.BELEPHANT] = 0x10000000000000;
            pos.bitBoards[Piece.BCAMEL] = 0x8000000000000;
        }

        if (random_minor)
        {
            randomize_minor(Side.BLACK, pos);
        }

        pos.update_derived();
    }
}

