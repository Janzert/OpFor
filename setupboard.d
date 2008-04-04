
import std.random;

import position;

class SetupGenerator
{
    const static ulong ROW_1_MASK = 0xFF;
    const static ulong ROW_2_MASK = 0xFF00;
    const static int ROW_1_TO_8 = 56;
    const static int ROW_2_TO_7 = 40;
    const static ulong[] rabbit_setups = [0x00FF, // Standard
                0x81E7, // 99of9
                0xA5A5]; // Fritz
    enum RabbitSetup { ANY = -1,
        STANDARD,
        NINETY_NINE,
        FRITZ };

    RabbitSetup rabbit_style = RabbitSetup.ANY;
    
    void setup_white(inout Position pos)
    {
        RabbitSetup rsetup = rabbit_style;
        if (rsetup == RabbitSetup.ANY)
        {
            rsetup = cast(RabbitSetup)(rand() % (RabbitSetup.max + 1));
        }
        pos.bitBoards[Piece.WRABBIT] = rabbit_setups[rsetup];

        pos.bitBoards[Piece.WELEPHANT] = 0x0800;
        pos.bitBoards[Piece.WCAMEL] = 0x1000;
        pos.bitBoards[Piece.WHORSE] = 0x4200;

        switch (rsetup)
        {
            case RabbitSetup.STANDARD:
                pos.bitBoards[Piece.WCAT] = 0x2400;
                pos.bitBoards[Piece.WDOG] = 0x8100;
                break;
            case RabbitSetup.NINETY_NINE:
                pos.bitBoards[Piece.WCAT] = 0x2400;
                pos.bitBoards[Piece.WDOG] = 0x18;
                break;
            case RabbitSetup.FRITZ:
                pos.bitBoards[Piece.WCAT] = 0x42;
                pos.bitBoards[Piece.WDOG] = 0x18;
                break;
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
        pos.bitBoards[Piece.BRABBIT] = 
            ((rabbit_setups[rsetup] & ROW_2_MASK) << ROW_2_TO_7)
            | ((rabbit_setups[rsetup] & ROW_1_MASK) << ROW_1_TO_8);

        if (pos.pieces[11] == Piece.WELEPHANT)
        {
            pos.bitBoards[Piece.BELEPHANT] = 0x08000000000000;
            pos.bitBoards[Piece.BCAMEL] = 0x10000000000000;
        } else {
            pos.bitBoards[Piece.BELEPHANT] = 0x10000000000000;
            pos.bitBoards[Piece.BCAMEL] = 0x8000000000000;
        }
        pos.bitBoards[Piece.BHORSE] = 0x42000000000000;

        switch (rsetup)
        {
            case RabbitSetup.STANDARD:
                pos.bitBoards[Piece.BCAT] = 0x24000000000000;
                pos.bitBoards[Piece.BDOG] = 0x81000000000000;
                break;
            case RabbitSetup.NINETY_NINE:
                pos.bitBoards[Piece.BCAT] = 0x24000000000000;
                pos.bitBoards[Piece.BDOG] = 0x1800000000000000;
                break;
            case RabbitSetup.FRITZ:
                pos.bitBoards[Piece.BCAT] = 0x4200000000000000;
                pos.bitBoards[Piece.BDOG] = 0x1800000000000000;
                break;
        }

        pos.update_derived();
    }
}

