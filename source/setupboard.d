
import std.array : split;
import std.conv : to;
import std.file : readText;
import std.format : format;
import std.random : uniform, uniform01;
import std.string : indexOf, lineSplitter, strip;

import position;
import setupbook;

/**
 * Setups to pick from at random, by weight. A line of a book file is
 *
 *     <colours> <weight> <front>/<back>
 *
 * with colours g, s or gs, and the two rows written a to h as they stand
 * on the board, so `gs 2.5 RHCMECHR/RRRDDRRR`. Anything after a # is a
 * comment. A setup is played as written or mirrored, each half the time.
 */
class SetupBook
{
    private struct Entry
    {
        bool[2] sides;
        double weight;
        string front;
        string back;
    }

    private Entry[] entries;
    private double[2] total_weight = [0.0, 0.0];

    this(string text)
    {
        foreach (raw; text.lineSplitter)
        {
            auto hash = raw.indexOf('#');
            string line = strip(hash == -1 ? raw : raw[0 .. hash]);
            if (line.length)
                add_line(line);
        }
        foreach (side; [Side.WHITE, Side.BLACK])
        {
            if (total_weight[side] <= 0.0)
                throw new ValueException(format("Setup book has no setups for side %s", side));
        }
    }

    private void add_line(string line)
    {
        auto fields = line.split;
        if (fields.length != 3)
            throw new ValueException("Bad setup book line: " ~ line);
        Entry entry;
        foreach (c; fields[0])
        {
            if (c == 'g')
                entry.sides[Side.WHITE] = true;
            else if (c == 's')
                entry.sides[Side.BLACK] = true;
            else
                throw new ValueException("Bad setup book line: " ~ line);
        }
        entry.weight = to!double(fields[1]);
        auto rows = fields[2].split("/");
        if (entry.weight <= 0.0 || rows.length != 2 || rows[0].length != 8
                || rows[1].length != 8)
            throw new ValueException("Bad setup book line: " ~ line);
        entry.front = rows[0];
        entry.back = rows[1];
        int[char] counts;
        foreach (c; entry.front ~ entry.back)
            counts[c]++;
        foreach (c, count; ['R': 8, 'C': 2, 'D': 2, 'H': 2, 'M': 1, 'E': 1])
        {
            if ((c in counts) is null || counts[c] != count)
                throw new ValueException("Bad setup book line: " ~ line);
        }
        entries ~= entry;
        foreach (side; [Side.WHITE, Side.BLACK])
        {
            if (entry.sides[side])
                total_weight[side] += entry.weight;
        }
    }

    private Entry pick(Side s)
    {
        double choice = uniform01() * total_weight[s];
        Entry last;
        foreach (entry; entries)
        {
            if (!entry.sides[s])
                continue;
            last = entry;
            choice -= entry.weight;
            if (choice < 0.0)
                break;
        }
        return last;
    }

    void place(Side s, ref Position pos)
    {
        static immutable string piece_chars = "RCDHME";
        static immutable int[] front_rank = [1, 6];
        static immutable int[] back_rank = [0, 7];

        Entry entry = pick(s);
        bool mirror = uniform(0, 2) == 1;
        int offset = (s == Side.WHITE) ? 0 : 6;
        ulong[6] boards;
        foreach (r; 0 .. 2)
        {
            int rank = (r == 0) ? front_rank[s] : back_rank[s];
            string row = (r == 0) ? entry.front : entry.back;
            foreach (file, c; row)
            {
                // The h file is the low bit of a rank.
                int shift = mirror ? cast(int) file : 7 - cast(int) file;
                boards[piece_chars.indexOf(c)] |= 1UL << (rank * 8 + shift);
            }
        }
        for (int i = 0; i < 6; i++)
            pos.place_piece(cast(Piece)(Piece.WRABBIT + offset + i), 0, true);
        for (int i = 0; i < 6; i++)
            pos.place_piece(cast(Piece)(Piece.WRABBIT + offset + i), boards[i]);
    }
}

class SetupGenerator
{
    static immutable ulong[] rabbit_setups = [0x00FF, // Standard
                0x81E7, // 99of9
                0xA5A5]; // Fritz
    static immutable ulong[] cat_setups = [0x2400,
                0x2400,
                0x42];
    static immutable ulong[] dog_setups = [0x8100,
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

    /// When set, setups come from this instead of the formations above.
    SetupBook book;

    this()
    {
        book = new SetupBook(DEFAULT_SETUP_BOOK);
    }

    /// Use the formations above, for options that choose among them.
    void use_formations()
    {
        book = null;
    }

    /// Load a book file, or use the formations with an empty path.
    void load_book(string path)
    {
        book = path.length ? new SetupBook(readText(path)) : null;
    }

    private ulong gold_to_silver(ulong bitboard)
    {
        static immutable ulong ROW_1_MASK = 0xFF;
        static immutable ulong ROW_2_MASK = 0xFF00;
        static immutable int ROW_1_TO_8 = 56;
        static immutable int ROW_2_TO_7 = 40;

        return ((bitboard & ROW_2_MASK) << ROW_2_TO_7)
               | ((bitboard & ROW_1_MASK) << ROW_1_TO_8);
    }

    private ulong adjust_side(Side s, ulong bitboard)
    {
        if (s == Side.BLACK)
            return gold_to_silver(bitboard);
        return bitboard;
    }

    private void randomize_minor(Side s, ref Position pos)
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

            int pix = uniform(0, cast(int)(pieces.length));
            int piece = pieces[pix];
            pieces[pix] = pieces[$-1];
            pieces.length = pieces.length - 1;

            pos.place_piece(cast(Piece)piece, sbit);
        }
    }

    private void randomize_all(Side s, ref Position pos)
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

            int pix = uniform(0, cast(int)(pieces.length));
            Piece piece = pieces[pix];
            pieces[pix] = pieces[$-1];
            pieces.length = pieces.length - 1;

            pos.place_piece(piece, sbit);
        }
    }

    void setup_board(Side s, ref Position pos)
    {
        if (book !is null && !random_all)
        {
            book.place(s, pos);
            return;
        }

        int offset = (s == Side.WHITE) ? 0 : 6;
        RabbitSetup rsetup = rabbit_style;
        if (rsetup == RabbitSetup.ANY)
        {
            int total_weight = 0;
            for (int i=0; i <= RabbitSetup.max; i++)
                total_weight += setup_weights[i];
            int choice_weight = uniform(0, cast(int)(total_weight));
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
        int bix = uniform(0, cast(int)(num));
        ulong b;
        for (int i=0; i <= bix; i++)
        {
            b = bits & -bits;
            bits ^= b;
        }
        return b;
    }

    void setup_handicap(Piece[] pieces, ref Position pos)
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

