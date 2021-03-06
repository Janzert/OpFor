
import std.intrinsic;
import tango.core.Memory;
import tango.core.sync.Mutex;
import tango.io.Stdout;
import tango.math.random.Random;
import tango.text.convert.Format;
import tango.text.Text;
import tango.text.Unicode;
import tango.text.Util;
import tango.util.Convert;

import zobristkeys;

private int find(char[] src, char pattern)
{
    int index = locate!(char)(src, pattern);
    if (index == src.length)
        index = -1;
    return index;
}

typedef byte bitix;

enum Side : byte { WHITE, BLACK }
enum Piece : byte { EMPTY, WRABBIT, WCAT, WDOG, WHORSE, WCAMEL, WELEPHANT,
                    BRABBIT, BCAT, BDOG, BHORSE, BCAMEL, BELEPHANT }

const ulong A_FILE = 0x8080808080808080UL;
const ulong B_FILE = 0x4040404040404040UL;
const ulong G_FILE = 0x0202020202020202UL;
const ulong H_FILE = 0x0101010101010101UL;
const ulong NOT_A_FILE = ~A_FILE;
const ulong NOT_H_FILE = ~H_FILE;
const ulong RANK_1 = 0xFFUL;
const ulong RANK_2 = 0xFF00UL;
const ulong RANK_7 = 0xFF000000000000UL;
const ulong RANK_8 = 0xFF00000000000000UL;
const ulong NOT_RANK_1 = ~RANK_1;
const ulong NOT_RANK_8 = ~RANK_8;
const ulong NOT_EDGE = NOT_A_FILE & NOT_H_FILE & NOT_RANK_1 & NOT_RANK_8;

const ulong TRAPS = 0x0000240000240000UL;
const ulong TRAP_C3 = 0x200000UL;
const ulong TRAP_F3 = 0x40000UL;
const ulong TRAP_C6 = 0x200000000000UL;
const ulong TRAP_F6 = 0x40000000000UL;
const bitix TRAP_F3_IX = 18;
const bitix TRAP_C3_IX = 21;
const bitix TRAP_F6_IX = 42;
const bitix TRAP_C6_IX = 45;

const ulong ALL_BITS_SET = 0xFFFFFFFFFFFFFFFFUL;

bitix bitindex(ulong value)
{
    if (cast(uint)(value))
        return cast(bitix)bsf(cast(uint)(value));
    else
        return cast(bitix)(bsf(cast(uint)(value >> 32)) + 32);
}
/*
in
{
    // one and only one bit must be set in value
    assert (value && (value == (value & ((value ^ ALL_BITS_SET) +1))));
}
body
{
    bitix index = cast(bitix)((value & 0xAAAAAAAAAAAAAAAAUL) != 0);
    index |= ((value & 0xCCCCCCCCCCCCCCCCUL) != 0) << 1;
    index |= ((value & 0xF0F0F0F0F0F0F0F0UL) != 0) << 2;
    index |= ((value & 0xFF00FF00FF00FF00UL) != 0) << 3;
    index |= ((value & 0xFFFF0000FFFF0000UL) != 0) << 4;
    index |= ((value & 0xFFFFFFFF00000000UL) != 0) << 5;
    return index;
}*/

bitix msbindex(ulong value)
{
    if (value >> 32)
        return cast(bitix)(bsr(cast(uint)(value >> 32)) + 32);
    else
        return cast(bitix)(bsr(cast(uint)(value)));
}

int popcount(ulong value)
{
    value -= (value >> 1) & 0x5555555555555555UL;
    value = (value & 0x3333333333333333UL) +
            ((value >> 2) & 0x3333333333333333UL);
    value = (value + (value >> 4)) & 0x0F0F0F0F0F0F0F0FUL;
    value = (value * 0x0101010101010101UL) >> 56;
    return value;
}

ulong neighbors_of(ulong value)
{
    value = ((value & NOT_H_FILE) >> 1) | ((value & NOT_A_FILE) << 1) |
            (value >> 8) | (value << 8);
    return value;
}

ulong rabbit_steps(Side side, ulong bits)
{
    ulong expanded;
    expanded = (bits & NOT_A_FILE) << 1;
    expanded |= (bits & NOT_H_FILE) >> 1;
    expanded |= ((bits << 8) >> (side << 4))
        | (((bits & RANK_8) >> 8) << ((side^1) << 5));
    //expanded |= (cur_side == Side.WHITE) ?
    //            (bits & NOT_RANK_8) << 8 : (bits & NOT_RANK_1) >> 8;

    return expanded;
}

char[] ix_to_alg(bitix index)
{
    char[] alg;
    alg ~= "hgfedcba"[index % 8];
    alg ~= to!(char[])((index / 8) + 1);

    return alg;
}

char[] bits_to_str(ulong bits)
{
    char[] boardstr = " +-----------------+\n".dup;
    for (int rownum = 8; rownum > 0; rownum--)
    {
        char[] rowstr = to!(char[])(rownum) ~ "| ";
        int rowix = 8 * (rownum - 1);
        for (int colnum = 0; colnum < 8; colnum++)
        {
            int index = rowix + (7 - colnum);
            ulong squarebit = 1UL << index;
            char[] piecestr;
            if (squarebit & bits)
            {
                piecestr = "* ";
            } else
            {
                if (squarebit & TRAPS)
                {
                    piecestr = "x ";
                } else
                {
                    piecestr = ". ";
                }
            }
            rowstr ~= piecestr;
        }
        rowstr ~= "|\n";
        boardstr ~= rowstr;
    }
    boardstr ~= " +-----------------+\n";
    boardstr ~= "   a b c d e f g h\n";
    return boardstr;
}

static const ulong INV_STEP = 3UL;

static int[64][64] taxicab_dist;

static this()
{
    for (int i = 0; i < 64; i++)
    {
        for (int j = 0; j < 64; j++)
        {
            int rd = (i/8) - (j/8);
            rd = (rd < 0) ? -rd : rd;
            int fd = (i%8) - (j%8);
            fd = (fd < 0) ? -fd : fd;
            int dist = rd + fd;
            taxicab_dist[i][j] = dist;
        }
    }
}

struct Step
{
    ulong frombit, tobit;
    bool push;

    void clear()
    {
        frombit = 0;
        tobit = 0;
        push = false;
    }

    bitix fromix()
    {
        return bitindex(frombit);
    }

    bitix toix()
    {
        return bitindex(tobit);
    }

    void set(bitix f, bitix t, bool p=false)
    {
        assert((f == 64 && t == 64) || f != t,
                Format("from {} == to {}", f, t));
        assert((f == 64 && t == 64) || (f >= 0 && f < 64),
                Format("from {} out of bounds", f));

        frombit = 1UL << f;
        tobit = 1UL << t;
        push = p;
    }

    void set(ulong f, ulong t, bool p=false)
    {
        assert((f == INV_STEP && t == INV_STEP) || f != t,
                Format("from {:X} == to {:X}", f, t));
        assert((f == INV_STEP && t == INV_STEP) || popcount(f) == 1,
                Format("invalid f {:X}", f));
        assert(t == INV_STEP || popcount(t) == 1,
                Format("invalid t {:X}", t));

        frombit = f;
        tobit = t;
        push = p;
    }

    char[] toString()
    {
        return toString(false);
    }

    char[] toString(bool showpush=false)
    {
        char[] str;
        if (frombit == INV_STEP)
            return "pass";
        str ~= ix_to_alg(fromix);
        if (tobit == INV_STEP)
        {
            str ~= "x";
        } else {
            switch (toix - fromix)
            {
                case 8:
                    str ~= "n";
                    break;
                case -8:
                    str ~= "s";
                    break;
                case -1:
                    str ~= "e";
                    break;
                case 1:
                    str ~= "w";
                    break;
                default:
                    str ~= ix_to_alg(toix);
            }
        }
        if (showpush && push)
        {
            str ~= "p";
        }
        return str;
    }
}

const static Step NULL_STEP = { frombit: INV_STEP, tobit: INV_STEP };

class StepList
{
    const int ALLOCA_MULT = 2;
    Step[] steps;
    int numsteps = 0;

    private static Mutex reserve_lock;
    private static StepList[] reservelists;
    private static int reservesize;
    static int allocated = 0;

    static this()
    {
        reserve_lock = new Mutex();
    }

    static int reserved()
    {
        return reservesize;
    }

    static StepList allocate()
    {
        synchronized (reserve_lock)
        {
            if (reservesize)
            {
                reservesize--;
                StepList returnlist = reservelists[reservesize];
                reservelists[reservesize] = null;
                returnlist.clear();
                return returnlist;
            }
        }

        return new StepList();
    }

    static void free(StepList list)
    {
        synchronized (reserve_lock)
        {
            if (reservelists.length == reservesize)
                reservelists.length = (reservelists.length+1) * 2;

            reservelists[reservesize++] = list;
        }
    }

    this(int startlength=32)
    {
        steps.length = startlength;
        GC.setAttr(cast(void*)steps, GC.BlkAttr.NO_SCAN);
        allocated += 1;
    }

    invariant
    {
        assert (numsteps >= 0);
        assert (numsteps <= steps.length);
        assert (steps.length > 0);
    }

    StepList dup()
    {
        StepList newlist = allocate();
        newlist.steps[0..numsteps] = steps[0..numsteps];
        newlist.numsteps = numsteps;
        GC.setAttr(cast(void*)newlist.steps, GC.BlkAttr.NO_SCAN);
        return newlist;
    }

    Step[] getsteps()
    {
        return steps[0..numsteps];
    }

    Step pop()
    {
        numsteps--;
        return steps[numsteps];
    }

    Step* newstep()
    {
        if (numsteps == steps.length)
        {
            steps.length = steps.length * ALLOCA_MULT;
            GC.setAttr(cast(void*)steps, GC.BlkAttr.NO_SCAN);
        }
        return &steps[numsteps++];
    }

    void clear()
    {
        numsteps = 0;
    }

    char[] to_move_str(Position start)
    {
        char [] move;
        Position current = start.dup;

        foreach (Step step; steps[0..numsteps])
        {
            if (step.frombit == INV_STEP) // pass step
                break;
            if (step.tobit != INV_STEP) // trap step
            {
                if (step.frombit)
                {
                    move ~= ".RCDHMErcdhme"[current.pieces[step.fromix]];
                } else {
                    move ~= '.';
                }
                move ~= ix_to_alg(step.fromix);
                switch (step.toix - step.fromix)
                {
                    case 8:
                        move ~= "n";
                        break;
                    case -8:
                        move ~= "s";
                        break;
                    case -1:
                        move ~= "e";
                        break;
                    case 1:
                        move ~= "w";
                        break;
                    default:
                        move ~= ix_to_alg(step.toix);
                }
                move ~= " ";

                Position previous = current.dup;
                Side pside = (current.pieces[step.fromix] < Piece.BRABBIT ) ? Side.WHITE : Side.BLACK;
                current.do_step(step);
                int prevpop = popcount(previous.placement[0]
                        | previous.placement[1]);
                int curpop = popcount(current.placement[0]
                        | current.placement[1]);
                if (prevpop != curpop)
                {
                    ulong ntrap = neighbors_of(step.frombit) & TRAPS;
                    bitix ntrapix = bitindex(ntrap);
                    if (ntrap && (previous.placement[pside] & ntrap)
                            && !(current.placement[pside] & ntrap))
                    {
                        move ~= ".RCDHMErcdhme"[previous.pieces[ntrapix]];
                        move ~= ix_to_alg(ntrapix);
                    } else if ((step.tobit & TRAPS)
                            && !(current.placement[pside] & step.tobit))
                    {
                        move ~= ".RCDHMErcdhme"[previous.pieces[step.fromix]];
                        move ~= ix_to_alg(step.toix);
                    } else {
                        throw new ValueException(Format(
                                "Piece disappeared without being trapped. {}",
                                move));
                    }
                    move ~= "x ";
                }
                if (previous.side != current.side)
                {
                    move ~= (current.side == Side.WHITE) ? "w " : "b ";
                }
                Position.free(previous);
            }
        }
        Position.free(current);

        if (move.length == 0)
            throw new ValueException("Tried to make move with no or pass only steps");

        move = move[0..length-1];
        if (move[length-2] == ' ')
            move = move[0..length-2];

        return move;
    }
}

class Position
{
    Side side;
    int stepsLeft;
    ulong frozen;
    ulong[Side.max+1] placement;
    ulong[Piece.max+1] bitBoards;
    Piece[64] pieces;
    Piece[64][2] strongest;
    ulong zobrist;

    Piece lastpiece;
    bitix lastfrom;
    bool inpush;

    debug (verify_position)
    {
        invariant
        {
            ulong usedsquares = 0;
            foreach(int piece, ulong board; bitBoards)
            {
                if ((usedsquares & board) != 0)
                {
                    if (board & bitBoards[Piece.EMPTY])
                    {
                        assert(0, "Piece on empty square");
                    } else {
                        assert (0, "two pieces on same square");
                    }
                }
                usedsquares |= board;

                if (piece == 0)
                {
                    if (placement[0] & board)
                    {
                        assert (0, "white placement contained empty square");
                    }
                    if (placement[1] & board)
                    {
                        assert (0, "black placement contained empty square");
                    }
                } else
                {
                    ulong places = placement[0];
                    if (piece > Piece.WELEPHANT)
                        places = placement[1];
                    if (board != (board & places))
                    {
                        assert (0, "placement doesn't have some of the pieces, " ~ std.string.toString(piece));
                    }
                }

                while (board)
                {
                    ulong piecebit = board & -board;
                    board ^= piecebit;
                    int pieceix = bitindex(piecebit);
                    if (pieces[pieceix] != piece)
                    {
                        assert (0, "pieces array has wrong piece");
                    }
                }
            }
            if (usedsquares != ALL_BITS_SET)
            {
                assert(0, Format("not all squares were accounted for, {:X}", usedsquares));
            }

            ulong zcheck = ZOBRIST_STEP[stepsLeft];
            if (side == Side.BLACK)
            {
                zcheck ^= ZOBRIST_SIDE;
            }
            if (inpush)
            {
                zcheck ^= ZOBRIST_INPUSH;
            }
            for (int pix=1; pix <= Piece.max; pix++)
            {
                ulong board = bitBoards[pix];
                while (board)
                {
                    ulong piecebit = board & -board;
                    bitix pieceix = bitindex(piecebit);
                    zcheck ^= ZOBRIST_PIECE[pix][pieceix];
                    board ^= piecebit;
                }
            }
            zcheck ^= ZOBRIST_LAST_PIECE[lastpiece][lastfrom];
            assert (zcheck == zobrist, "Incorrect zobrist encountered.");

            ulong wneighbors = neighbors_of(placement[Side.WHITE]);
            ulong bneighbors = neighbors_of(placement[Side.BLACK]);
            ulong wstronger = placement[Side.WHITE];
            ulong bstronger = placement[Side.BLACK];
            ulong checkfrozen = 0;
            for (int pix = 1; pix <= 6; pix++)
            {
                wstronger ^= bitBoards[pix];
                bstronger ^= bitBoards[pix+6];
                checkfrozen |= bitBoards[pix] & neighbors_of(bstronger) & (~wneighbors);
                checkfrozen |= bitBoards[pix+6] & neighbors_of(wstronger) & (~bneighbors);
            }
            assert (checkfrozen == frozen, Format("Incorrect frozen board encountered. {:X}, {:X}", frozen, checkfrozen));

            for (int sqix = 0; sqix < 64; sqix++)
            {
                for (Side sideix = Side.WHITE; sideix < 2; sideix++)
                {
                    ulong neighbors = neighbors_of(1UL << sqix) & placement[sideix];
                    Piece strong = Piece.EMPTY;
                    while (neighbors)
                    {
                        ulong nbit = neighbors & -neighbors;
                        neighbors ^= nbit;
                        bitix nix = bitindex(nbit);
                        if (pieces[nix] > strong)
                            strong = pieces[nix];
                    }
                    assert (strongest[sideix][sqix] == strong,
                            Format("Incorrect strongest neighbor encountered. {} {} {} {}",
                                   sideix, sqix, strong, strongest[sideix][sqix]));
                }
            }
        }
    }

    private static Mutex reserve_lock;
    private static Position[] reserve;
    private static int reservesize;
    static int allocated;

    static this()
    {
        reserve_lock = new Mutex();
    }

    static int reserved()
    {
        return reservesize;
    }

    static real reserve_size()
    {
        return ((reservesize * Position.classinfo.init.length)
            / cast(real)(1024*1024));
    }

    static int rlistsize()
    {
        return reserve.length;
    }

    static Position allocate()
    {
        synchronized (reserve_lock)
        {
            if (reservesize)
            {
                reservesize--;
                Position pos = reserve[reservesize];
                reserve[reservesize] = null;
                return pos;
            }
        }

        return new Position();
    }

    static Position allocate(Position other)
    {
        synchronized (reserve_lock)
        {
            if (reservesize)
            {
                reservesize--;
                Position pos = reserve[reservesize];
                reserve[reservesize] = null;
                pos.copy(other);
                return pos;
            }
        }

        return new Position(other);
    }

    static void free(Position pos)
    {
        synchronized (reserve_lock)
        {
            if (reserve.length == reservesize)
            {
                reserve.length = (reserve.length+1) * 2;
            }

            reserve[reservesize++] = pos;
        }
    }

    static void reduce_reserve(real size)
    {
        synchronized (reserve_lock)
        {
            int max_num = cast(int)((size * 1024*1024) / Position.classinfo.init.length);
            while (reservesize > max_num)
            {
                delete reserve[--reservesize];
                reserve[reservesize] = null;
                allocated--;
            }
        }
    }

    this()
    {
        this.bitBoards[0] = ALL_BITS_SET;
        this.lastfrom = 64;
        GC.setAttr(cast(void*)this, GC.BlkAttr.NO_SCAN);
        allocated++;
    }

    this(Position other)
    {
        this.side = other.side;
        this.stepsLeft = other.stepsLeft;
        this.zobrist = other.zobrist;
        this.frozen = other.frozen;
        this.placement[] = other.placement[];
        this.bitBoards[] = other.bitBoards[];
        this.pieces[] = other.pieces[];
        this.strongest[][] = other.strongest[][];
        this.lastpiece = other.lastpiece;
        this.lastfrom = other.lastfrom;
        this.inpush = other.inpush;
        GC.setAttr(cast(void*)this, GC.BlkAttr.NO_SCAN);
        allocated++;
    }

    this(Side color, int steps, ulong[Piece.max+1] bitboards)
    {
        this.side = color;
        if (steps < 1 || steps > 4)
            throw new ValueException("Invalid number of steps given for Position.");
        this.stepsLeft = steps;
        this.bitBoards[] = bitboards[];
        for (int pix = 1; pix <= Piece.max; pix++)
        {
            if (pix < Piece.BRABBIT)
                placement[0] |= bitBoards[pix];
            else
                placement[1] |= bitBoards[pix];

            ulong board = bitBoards[pix];
            while (board)
            {
                ulong piecebit = board & ((board ^ ALL_BITS_SET) + 1);
                board ^= piecebit;
                bitix pieceix = bitindex(piecebit);
                assert(pieces[pieceix] == Piece.EMPTY);
                pieces[pieceix] = cast(Piece)pix;
            }
        }

        lastpiece = Piece.EMPTY;
        lastfrom = 64;
        inpush = false;

        update_derived();

        GC.setAttr(cast(void*)this, GC.BlkAttr.NO_SCAN);
        allocated++;
    }

    void clear()
    {
        side = Side.WHITE;
        stepsLeft = 0;

        frozen = 0;
        placement[0] = 0;
        placement[1] = 0;

        bitBoards[0] = ALL_BITS_SET;
        for (int i=1; i < bitBoards.length; i++)
        {
            bitBoards[i] = 0;
        }

        for (int i=0; i < pieces.length; i++)
        {
            pieces[i] = Piece.EMPTY;
        }

        for (int i=0; i < 2; i++)
        {
            for (int j=0; j < 64; j++)
            {
                strongest[i][j] = Piece.EMPTY;
            }
        }

        zobrist = 0;

        lastpiece = Piece.EMPTY;
        lastfrom = 64;
        inpush = false;
    }

    private void update_derived()
    {
        if (side)
            zobrist = ZOBRIST_SIDE;
        else
            zobrist = 0;
        zobrist ^= ZOBRIST_STEP[stepsLeft];
        placement[Side.WHITE] = 0UL;
        placement[Side.BLACK] = 0UL;
        for (int i=0; i < 64; i++)
            pieces[i] = Piece.EMPTY;

        for (Piece pix = Piece.WRABBIT; pix <= Piece.BELEPHANT; pix++)
        {
            ulong board = bitBoards[pix];
            Side s = (pix < Piece.BRABBIT) ? Side.WHITE : Side.BLACK;
            placement[s] |= board;
            while (board)
            {
                ulong piecebit = board & ((board ^ ALL_BITS_SET) + 1);
                board ^= piecebit;
                bitix pieceix = bitindex(piecebit);
                pieces[pieceix] = pix;
                zobrist ^= ZOBRIST_PIECE[pix][pieceix];
            }
        }
        bitBoards[Piece.EMPTY] = ~(placement[Side.WHITE] | placement[Side.BLACK]);
        if (inpush)
        {
            zobrist ^= ZOBRIST_INPUSH;
        }
        zobrist ^= ZOBRIST_LAST_PIECE[lastpiece][lastfrom];

        ulong wneighbors = neighbors_of(placement[Side.WHITE]);
        ulong bneighbors = neighbors_of(placement[Side.BLACK]);
        ulong wstronger = placement[Side.WHITE];
        ulong bstronger = placement[Side.BLACK];
        frozen = 0;
        for (int pix = 1; pix <= 6; pix++)
        {
            wstronger ^= bitBoards[pix];
            bstronger ^= bitBoards[pix+6];
            frozen |= bitBoards[pix] & neighbors_of(bstronger) & (~wneighbors);
            frozen |= bitBoards[pix+6] & neighbors_of(wstronger) & (~bneighbors);
        }

        for (int sqix = 0; sqix < 64; sqix++)
        {
            for (Side sideix = Side.WHITE; sideix < 2; sideix++)
            {
                ulong neighbors = neighbors_of(1UL << sqix) & placement[sideix];
                Piece strong = Piece.EMPTY;
                while (neighbors)
                {
                    ulong nbit = neighbors & -neighbors;
                    neighbors ^= nbit;
                    bitix nix = bitindex(nbit);
                    if (pieces[nix] > strong)
                        strong = pieces[nix];
                }
                strongest[sideix][sqix] = strong;
            }
        }
    }

    bool opEquals(Position other)
    {
        if (zobrist != other.zobrist ||
            stepsLeft != other.stepsLeft ||
            side != other.side ||
            lastpiece != other.lastpiece ||
            lastfrom != other.lastfrom ||
            inpush != other.inpush ||
            frozen != other.frozen ||
            placement[Side.WHITE] != other.placement[Side.WHITE] ||
            placement[Side.BLACK] != other.placement[Side.BLACK])
            return false;
        for (int pieceix=0; pieceix <= Piece.max; pieceix++)
        {
            if (bitBoards[pieceix] != other.bitBoards[pieceix])
                return false;
        }
        return true;
    }

    Position dup()
    {
        return allocate(this);
    }

    void copy(Position other)
    {
        this.side = other.side;
        this.stepsLeft = other.stepsLeft;
        this.zobrist = other.zobrist;
        this.frozen = other.frozen;
        this.placement[] = other.placement[];
        this.bitBoards[] = other.bitBoards[];
        this.pieces[] = other.pieces[];
        this.strongest[][] = other.strongest[][];
        this.lastpiece = other.lastpiece;
        this.lastfrom = other.lastfrom;
        this.inpush = other.inpush;
    }

    bool is_endstate()
    {
        if (bitBoards[Piece.WRABBIT] & RANK_8 ||
            bitBoards[Piece.BRABBIT] & RANK_1 ||
            !bitBoards[Piece.WRABBIT] ||
            !bitBoards[Piece.BRABBIT])
            return true;
        return false;
    }

    bool is_goal()
    {
        if (bitBoards[Piece.WRABBIT] & RANK_8 ||
                bitBoards[Piece.BRABBIT] & RANK_1)
            return true;
        return false;
    }

    bool is_goal(Side s)
    {
        ulong bb = bitBoards[Piece.WRABBIT + (s * 6)];
        ulong rank = s == Side.WHITE ? RANK_8 : RANK_1;
        if (bb & rank)
            return true;
        return false;
    }

    int endscore()
    {
        ulong ggoal = bitBoards[Piece.WRABBIT] & RANK_8;
        ulong sgoal = bitBoards[Piece.BRABBIT] & RANK_1;
        if (ggoal || sgoal)
        {
            if (side == Side.WHITE)
            {
                if (sgoal)
                    return -1;
                else
                    return 1;
            } else
            {
                if (ggoal)
                    return 1;
                else
                    return -1;
            }
        }

        ulong grabbits = bitBoards[Piece.WRABBIT];
        ulong srabbits = bitBoards[Piece.BRABBIT];
        if (!grabbits || !srabbits)
        {
            if (side == Side.WHITE)
            {
                if (!grabbits)
                    return -1;
                else
                    return 1;
            } else
            {
                if (!srabbits)
                    return 1;
                else
                    return -1;
            }
        }
        return 0;
    }

    int numpieces(int side=-1, int piece=-1)
    in
    {
        assert (side >= -1 && side <= Side.max);
        assert (piece >= -1 && piece < Piece.max);
    }
    body
    {
        if (side == -1)
        {
            if (piece == -1)
                return popcount(placement[0] | placement[1]);
            return popcount(bitBoards[piece] | bitBoards[piece+6]);
        }
        if (piece == -1)
            return popcount(placement[side]);
        if (side == Side.BLACK)
            piece += 6;
        return popcount(bitBoards[piece]);
    }

    char[] to_long_str(bool dots=false)
    {
        ulong notempty = ~bitBoards[Piece.EMPTY];
        char[] boardstr = " +-----------------+\n".dup;
        for (int rownum = 8; rownum > 0; rownum--)
        {
            char[] rowstr = to!(char[])(rownum) ~ "| ";
            int rowix = 8 * (rownum - 1);
            for (int colnum = 0; colnum < 8; colnum++)
            {
                int index = rowix + (7 - colnum);
                ulong squarebit = 1UL << index;
                char[] piecestr = "* ";
                if (squarebit & notempty)
                {
                    foreach (int pix, ulong piece; bitBoards[1..length])
                    {
                        if (squarebit & piece)
                        {
                            piecestr = "RCDHMErcdhme"[pix] ~ " ";
                            break;
                        }
                    }
                } else
                {
                    if (squarebit & TRAPS)
                    {
                        piecestr = "x ";
                    } else
                    {
                        if (dots)
                            piecestr = ". ";
                        else
                            piecestr = "  ";
                    }
                }
                rowstr ~= piecestr;
            }
            rowstr ~= "|\n";
            boardstr ~= rowstr;
        }
        boardstr ~= " +-----------------+\n";
        boardstr ~= "   a b c d e f g h\n";
        return boardstr;
    }

    char[] to_short_str()
    {
        ulong notempty = ~bitBoards[Piece.EMPTY];
        char[] boardstr = "[".dup;
        for (int index = 63; index >= 0; index--)
        {
            ulong squarebit = 1UL << index;
            char piecech = '*';
            if (squarebit & notempty)
            {
                foreach (int pix, ulong board; bitBoards[1..length])
                {
                    if (squarebit & board)
                    {
                        piecech = "RCDHMErcdhme"[pix];
                        break;
                    }
                }
            } else
            {
                piecech = ' ';
            }
            boardstr ~= piecech;
        }
        boardstr ~= "]";
        return boardstr;
    }

    char[] to_placing_move(int side=-1)
    {
        const static char[] piece_char = " RCDHMErcdhme";

        char[] mstr;
        if (side == Side.WHITE || side == -1)
        {
            if (side == -1)
            {
                mstr ~= "w ";
            }

            for (Piece p = Piece.WRABBIT; p <= Piece.WELEPHANT; p++)
            {
                ulong pieces = bitBoards[p];
                while (pieces)
                {
                    ulong pbit = pieces & -pieces;
                    pieces ^= pbit;
                    bitix pix = bitindex(pbit);

                    mstr ~= piece_char[p];
                    mstr ~= ix_to_alg(pix);
                    mstr ~= " ";
                }
            }
        }

        if (side == Side.BLACK || side == -1)
        {
            if (side == -1)
            {
                mstr ~= "\nb ";
            }

            for (Piece p = Piece.BRABBIT; p <= Piece.BELEPHANT; p++)
            {
                ulong pieces = bitBoards[p];
                while (pieces)
                {
                    ulong pbit = pieces & -pieces;
                    pieces ^= pbit;
                    bitix pix = bitindex(pbit);

                    mstr ~= piece_char[p];
                    mstr ~= ix_to_alg(pix);
                    mstr ~= " ";
                }
            }
        }

        return mstr;
    }

    private void update_add(Side side, Piece piece, ulong tobit)
    {
        Side oside = cast(Side)(side ^ 1);

        Piece rank = cast(Piece)((piece < Piece.BRABBIT) ? piece + 6 : piece - 6);
        ulong tneighbors = neighbors_of(tobit);
        // unfreeze any friendly neighbors
        frozen &= ~(tneighbors & placement[side]);
        // update strongest neighbor
        ulong checkbits = 0;
        while (tneighbors)
        {
            ulong nbit = tneighbors & -tneighbors;
            tneighbors ^= nbit;
            bitix nix = bitindex(nbit);

            if (strongest[side][nix] < piece)
            {
                strongest[side][nix] = piece;
                if (pieces[nix] < rank)
                    checkbits |= nbit;
            }
        }
        // update neighboring enemies
        frozen |= placement[oside] & checkbits & (~neighbors_of(placement[oside]));
    }

    private void update_remove(Side side, Piece piece, ulong frombit)
    {
        Side oside = cast(Side)(side ^ 1);
        frozen &= ~frombit;     // make sure from is unfrozen.

        ulong fromneighbors = neighbors_of(frombit);
        while (fromneighbors)
        {
            ulong nbit = fromneighbors & -fromneighbors;
            fromneighbors ^= nbit;
            bitix nix = bitindex(nbit);
            if (strongest[side][nix] == piece)
            {
                ulong nnbits = neighbors_of(nbit);
                if (placement[side] & nnbits)
                {
                    for (Piece neighbor = piece; neighbor > 0; neighbor--)
                    {
                        if (bitBoards[neighbor] & nnbits)
                        {
                            strongest[side][nix] = neighbor;
                            if ((placement[oside] & nbit) && strongest[oside][nix] == Piece.EMPTY)
                            {
                                Piece rank = cast(Piece)((pieces[nix] < Piece.BRABBIT) ? pieces[nix] + 6 : pieces[nix] - 6);
                                if (rank >= neighbor)
                                    frozen &= ~nbit;
                            }
                            break;
                        }
                    }
                } else
                {
                    strongest[side][nix] = Piece.EMPTY;
                    frozen &= ~nbit;
                    if (placement[side] & nbit)
                    {
                        Piece rank = cast(Piece)((pieces[nix] + side + 6) % (Piece.max+1));
                        if (rank < strongest[oside][nix])
                            frozen |= nbit;
                    }
                }
            }
        }
    }

    void do_step(Step step)
    {
        zobrist ^= ZOBRIST_STEP[stepsLeft];

        if (step.tobit != INV_STEP) // not a pass or trap step
        {
            bitix fromix = step.fromix;
            bitix toix = step.toix;
            Piece piece = pieces[fromix];
            assert (piece != Piece.EMPTY, Format("move empty piece f{} t{}", fromix, toix));
            assert (pieces[toix] == Piece.EMPTY, Format("occupied to f{} t{}", fromix, toix));

            Side piece_side;
            if (placement[Side.WHITE] & step.frombit)
            {
                piece_side = Side.WHITE;
            } else {
                piece_side = Side.BLACK;
                assert (placement[Side.BLACK] & step.frombit);
            }
            ulong tofrom = step.frombit ^ step.tobit;
            bitBoards[Piece.EMPTY] ^= tofrom;
            bitBoards[piece] ^= tofrom;
            placement[piece_side] ^= tofrom;
            pieces[fromix] = Piece.EMPTY;
            pieces[toix] = piece;

            zobrist ^= ZOBRIST_PIECE[piece][fromix] ^
                       ZOBRIST_PIECE[piece][toix];

            ulong trapped = (neighbors_of(step.frombit) & TRAPS)
                    & placement[piece_side];
            if (trapped && (trapped & ~neighbors_of(placement[piece_side])))
            {
                placement[piece_side] ^= trapped;
                bitix trapix = bitindex(trapped);
                Piece piecetr = pieces[trapix];
                pieces[trapix] = Piece.EMPTY;
                bitBoards[piecetr] ^= trapped;
                bitBoards[Piece.EMPTY] ^= trapped;
                zobrist ^= ZOBRIST_PIECE[piecetr][trapix];
                if (trapix != toix)
                {
                    update_remove(piece_side, piecetr, trapped);
                    update_add(piece_side, piece, step.tobit);
                }
            } else {
                update_add(piece_side, piece, step.tobit);
            }
            update_remove(piece_side, piece, step.frombit);
            stepsLeft--;

            zobrist ^= ZOBRIST_LAST_PIECE[lastpiece][lastfrom];
            if (inpush != step.push)
            {
                zobrist ^= ZOBRIST_INPUSH;
            }
            if (!inpush && (step.push || (piece_side == side)))
            {
                lastpiece = piece;
                lastfrom = fromix;
            } else {
                lastpiece = Piece.EMPTY;
                lastfrom = 64;
            }
            inpush = step.push;
            zobrist ^= ZOBRIST_LAST_PIECE[lastpiece][lastfrom];
        }

        if (stepsLeft < 1 ||
            (step.frombit == INV_STEP && step.tobit == INV_STEP)) // pass step
        {
            assert (!inpush, Format("stepsleft {}, step.from {}, step.to {}", stepsLeft, step.fromix, step.toix));
            side ^= 1;
            zobrist ^= ZOBRIST_SIDE ^ ZOBRIST_LAST_PIECE[lastpiece][lastfrom];
            stepsLeft = 4;
            lastpiece = Piece.EMPTY;
            lastfrom = 64;
        }

        zobrist ^= ZOBRIST_STEP[stepsLeft];
    }

    void do_str_move(char[] move)
    {
        Side start_side = side;

        foreach (char[] step; split!(char)(move, " "))
        {
            Piece piece = cast(Piece)(find("RCDHMErcdhme", step[0]) +1);
            if (piece <= 0)
            {
                throw new ValueException(Format("Step starts with invalid piece. {}", step));
            }
            int column = find("abcdefgh", step[1])+1;
            if (column < 1)
            {
                throw new ValueException(Format("Step has invalid column. {}", step));
            }
            if (!isDigit(step[2]))
            {
                throw new ValueException(Format("Step column is not a number. {}", step));
            }
            int rank = to!(int)(step[2..3])-1;
            if (rank < 0 || rank > 7)
            {
                throw new ValueException(Format("Step column is invalid. {}", step));
            }

            bitix fromix = cast(bitix)((rank*8) + (8-column));
            ulong from = 1UL << fromix;
            if (step.length > 3)
            {
                switch (step[3..4])
                {
                    case "n":
                        if (pieces[fromix] != piece)
                        {
                            throw new ValueException(Format("Step moves non-existant piece. {}", step));
                        }
                        if (pieces[fromix+8] != Piece.EMPTY)
                        {
                            throw new ValueException(Format("Step tries to move to an occupied square. {}", step));
                        }
                        Step bstep;
                        bstep.set(from, from << 8);
                        do_step(bstep);
                        break;
                    case "s":
                        if (pieces[fromix] != piece)
                        {
                            throw new ValueException(Format("Step moves non-existant piece. {}", step));
                        }
                        if (pieces[fromix-8] != Piece.EMPTY)
                        {
                            throw new ValueException(Format("Step tries to move to an occupied square. {}", step));
                        }
                        Step bstep;
                        bstep.set(from, from >> 8);
                        do_step(bstep);
                        break;
                    case "e":
                        if (pieces[fromix] != piece)
                        {
                            throw new ValueException(Format("Step moves non-existant piece. {}", step));
                        }
                        if (pieces[fromix-1] != Piece.EMPTY)
                        {
                            throw new ValueException(Format("Step tries to move to an occupied square. {}", step));
                        }
                        Step bstep;
                        bstep.set(from, from >> 1);
                        do_step(bstep);
                        break;
                    case "w":
                        if (pieces[fromix] != piece)
                        {
                            throw new ValueException(Format("Step moves non-existant piece. {}", step));
                        }
                        if (pieces[fromix+1] != Piece.EMPTY)
                        {
                            throw new ValueException(Format("Step tries to move to an occupied square. {}", step));
                        }
                        Step bstep;
                        bstep.set(from, from << 1);
                        do_step(bstep);
                        break;
                    case "x":
                        break;
                    default:
                        throw new ValueException(Format("Step direction is invalid. {}", step));
                }
            } else {
                if (pieces[fromix] != Piece.EMPTY)
                {
                    throw new ValueException(Format("Tried to place a piece in a non-empty square. {}", step));
                }
                pieces[fromix] = piece;
                bitBoards[piece] |= from;
                bitBoards[0] &= ~from;
                placement[(piece < Piece.BRABBIT) ? Side.WHITE : Side.BLACK] |= from;
            }
        }

        side = cast(Side)(start_side ^ 1);
        stepsLeft = 4;
        lastpiece = Piece.EMPTY;
        lastfrom = 64;
        inpush = false;
        update_derived();
    }

    void place_piece(Piece p, ulong squares, bool clear_other = false)
    {
        if (clear_other)
        {
            bitBoards[Piece.EMPTY] |= bitBoards[p];
            bitBoards[p] = 0UL;
        }

        if ((~bitBoards[Piece.EMPTY]) & squares)
            throw new ValueException(Format("Tried to place a piece in a non-empty square. squares {:X} empty {:X}", squares, bitBoards[Piece.EMPTY]));

        bitBoards[p] |= squares;
        update_derived();
    }

    void remove_piece(bitix square_ix)
    {
        Piece pt = pieces[square_ix];
        if (pt == Piece.EMPTY) {
            throw new ValueException("Tried to remove piece from empty square");
        }
        Side pside = pt < Piece.BRABBIT ? Side.WHITE : Side.BLACK;
        ulong pbit = 1UL << square_ix;
        placement[pside] ^= pbit;
        pieces[square_ix] = Piece.EMPTY;
        bitBoards[pt] ^= pbit;
        bitBoards[Piece.EMPTY] ^= pbit;
        zobrist ^= ZOBRIST_PIECE[pt][square_ix];
        update_remove(pside, pt, 1UL << square_ix);
    }

    void set_steps_left(int num)
    {
        if (num < 0 || num > 4)
            throw new ValueException(Format("Tried to set steps left to an illegal value, {}.", num));
        stepsLeft = num;
        update_derived();
    }

    void set_side(Side s)
    {
        side = s;
        update_derived();
    }

    void get_steps(StepList steps)
    {
        Step* step;
        int pieceoffset = 0;
        int enemyoffset = 6;
        if (side)
        {
            pieceoffset = 6;
            enemyoffset = -6;
        }
        ulong lfbit = 1UL << lastfrom;

        if (inpush)
        {
            ulong pospushers = neighbors_of(lfbit) & placement[side] & ~frozen;
            while (pospushers)
            {
                ulong pushbit = pospushers & -pospushers;
                pospushers ^= pushbit;
                bitix fromix = bitindex(pushbit);
                if (pieces[fromix]+enemyoffset > lastpiece)
                {
                    step = steps.newstep();
                    step.set(pushbit, lfbit);
                }
            }
        } else {
            ulong pullmap = 0UL;

            // Finish any pulls
            if (lastpiece > pieceoffset &&
                lastpiece <= pieceoffset+6 &&
                lastpiece-pieceoffset > Piece.WRABBIT)
            // last to move was friendly and stronger than a rabbit
            {
                pullmap = lfbit;
                ulong pospulls = neighbors_of(lfbit) & placement[side^1];
                while (pospulls)
                {
                    ulong pullbit = pospulls & -pospulls;
                    pospulls ^= pullbit;
                    bitix fromix = bitindex(pullbit);
                    if (pieces[fromix] < lastpiece+enemyoffset)
                    {
                        pullmap |= pullbit;

                        step = steps.newstep();
                        step.set(pullbit, lfbit);
                    }
                }
            }

            if (stepsLeft > 1)
            {
                // Start any pushes
                ulong pushables = 0UL;
                ulong weaker = placement[side^1];
                for (int piece = Piece.WELEPHANT+pieceoffset; piece > Piece.WRABBIT+pieceoffset; piece--)
                {
                    weaker ^= bitBoards[piece+enemyoffset];
                    pushables |= weaker & neighbors_of(~frozen & bitBoards[piece]);
                }
                while (pushables)
                {
                    ulong frombit = pushables & -pushables;
                    pushables ^= frombit;
                    ulong tobits = neighbors_of(frombit) & bitBoards[Piece.EMPTY];
                    while (tobits)
                    {
                        ulong tobit = tobits & -tobits;
                        tobits ^= tobit;
                        if (!((frombit & pullmap) && (tobit & pullmap)))
                        {
                            step = steps.newstep();
                            step.set(frombit, tobit, true);
                        }
                    }
                }
            }

            if (stepsLeft != 4)
            {
                step = steps.newstep();
                step.set(INV_STEP, INV_STEP);
            }

            ulong stepbits;
            ulong stepbit;
            ulong mpieces = placement[side] & ~frozen;

            if (side == Side.BLACK)
                stepbits = ((mpieces & ~bitBoards[Piece.BRABBIT]) << 8) &
                                bitBoards[Piece.EMPTY];
            else
                stepbits = (mpieces << 8) & bitBoards[Piece.EMPTY];
            while (stepbits)
            {
                stepbit = stepbits & -stepbits;
                stepbits ^= stepbit;
                step = steps.newstep();
                step.set(stepbit >> 8, stepbit);
            }

            stepbits = ((mpieces & NOT_A_FILE) << 1) & bitBoards[Piece.EMPTY];
            while (stepbits)
            {
                stepbit = stepbits & -stepbits;
                stepbits ^= stepbit;
                step = steps.newstep();
                step.set(stepbit >> 1, stepbit);
            }

            stepbits = ((mpieces & NOT_H_FILE) >> 1) & bitBoards[Piece.EMPTY];
            while (stepbits)
            {
                stepbit = stepbits & -stepbits;
                stepbits ^= stepbit;
                step = steps.newstep();
                step.set(stepbit << 1, stepbit);
            }

            if (side == Side.WHITE)
                stepbits = ((mpieces & ~bitBoards[Piece.WRABBIT]) >> 8) &
                                bitBoards[Piece.EMPTY];
            else
                stepbits = (mpieces >> 8) & bitBoards[Piece.EMPTY];
            while (stepbits)
            {
                stepbit = stepbits & -stepbits;
                stepbits ^= stepbit;
                step = steps.newstep();
                step.set(stepbit << 8, stepbit);
            }
        }
    }

    PosStore get_moves()
    {
        StepList nextsteps = StepList.allocate();
        PosStore partial = new PosStore();
        PosStore nextpart = new PosStore();
        PosStore finished = new PosStore();
        Position newpos = Position.allocate();
        partial.addpos(this.dup, StepList.allocate());
        while (partial.length != 0)
        {
            foreach (Position curpos; partial)
            {
                StepList cursteps = partial.getpos(curpos);
                nextsteps.clear();
                curpos.get_steps(nextsteps);
                foreach (Step step; nextsteps.getsteps())
                {
                    newpos.copy(curpos);
                    newpos.do_step(step);
                    if (newpos.side == this.side)
                    {
                        if (!nextpart.haspos(newpos))
                        {
                            StepList newsteps = cursteps.dup;
                            (*newsteps.newstep()) = step;
                            nextpart.addpos(newpos, newsteps);
                            newpos = Position.allocate();
                        }
                    } else if (!finished.haspos(newpos))
                    {
                        StepList newsteps = cursteps.dup;
                        (*newsteps.newstep()) = step;
                        finished.addpos(newpos, newsteps);
                        newpos = Position.allocate();
                    }
                }
            }
            PosStore tmp = partial;
            partial = nextpart;
            tmp.free_items();
            nextpart = tmp;
        }
        Position.free(newpos);
        StepList.free(nextsteps);

        Step passmove;
        passmove.set(INV_STEP, INV_STEP);
        Position nullmove = this.dup;
        nullmove.do_step(passmove);
        if (finished.haspos(nullmove))
        {
            StepList.free(finished.getpos(nullmove));
            Position.free(finished.delpos(nullmove));
        }
        Position.free(nullmove);
        return finished;
    }

    Position reverse()
    {
        Position rpos = Position.allocate();
        rpos.clear();

        rpos.side = cast(Side)(side^1);
        rpos.stepsLeft = stepsLeft;
        if (lastpiece != Piece.EMPTY)
        {
            rpos.lastpiece = (lastpiece < Piece.BRABBIT) ?
                cast(Piece)(lastpiece+6) : cast(Piece)(lastpiece-6);
            rpos.lastfrom = cast(bitix)(63-lastfrom);
        }
        rpos.inpush = inpush;

        for (int ix=0; ix < 64; ix++)
        {
            ulong pbit = 1UL << ix;
            Piece piece = pieces[63-ix];
            if (piece != Piece.EMPTY)
            {
                piece = (piece < Piece.BRABBIT) ?
                    cast(Piece)(piece+6) : cast(Piece)(piece-6);
                rpos.pieces[ix] = piece;
                rpos.bitBoards[piece] |= pbit;
                rpos.bitBoards[Piece.EMPTY] &= ~pbit;
                rpos.placement[(piece < Piece.BRABBIT) ? Side.WHITE : Side.BLACK] |= pbit;
            }
        }
        rpos.update_derived();
        return rpos;
    }
}

class PosStore
{
    private:
        const int START_SIZE = 14;
        const double MAX_LOAD = 0.7;
        static Position DELETED_ENTRY;
        Position[] positions;
        StepList[] steplists;
        int numstored = 0;
        int keysize = START_SIZE;
        int keymask = (1 << START_SIZE) - 1;
        int keystep = 1261;

        bool isrprime(int l, int s)
        {
            int t;
            while (s > 0)
            {
                t = l % s;
                l = s;
                s = t;
            }
            if (l == 1)
                return true;
            return false;
        }

        void expand()
        {
            Position[] newpos;
            StepList[] newlists;
            int newsize = keysize + 1;
            int newmask = (1 << newsize)-1;
            newpos.length = 1 << newsize;
            newlists.length = newpos.length;
            // find a new step that is relatively prime to the length
            int newstep = (newpos.length/13)+1;
            while (!isrprime(newpos.length, newstep))
            {
                newstep++;
                if (newstep > newpos.length/2)
                {
                    newstep = 11;
                    break;
                }
            }

            for (int ix=0; ix < positions.length; ix++)
            {
                if (positions[ix] !is null && positions[ix] !is DELETED_ENTRY)
                {
                    int key = positions[ix].zobrist & newmask;
                    while (newpos[key] !is null)
                    {
                        key = (key + newstep) & newmask;
                    }
                    newpos[key] = positions[ix];
                    newlists[key] = steplists[ix];
                }
            }

            positions = newpos;
            steplists = newlists;
            keymask = newmask;
            keysize = newsize;
            keystep = newstep;
        }

    public:
    static this()
    {
        DELETED_ENTRY = new Position();
    }

    this()
    {
        positions.length = 1 << keysize;
        steplists.length = 1 << keysize;
    }

    int opApply(int delegate(inout Position) lpbody)
    {
        int result = 0;
        for (int ix = 0; ix < positions.length; ix++)
        {
            if (positions[ix] !is null && positions[ix] !is DELETED_ENTRY)
            {
                result = lpbody(positions[ix]);
                if (result)
                    break;
            }
        }
        return result;
    }

    bool checktable()
    {
        int found = 0;
        for (int ix=0; ix < positions.length; ix++)
        {
            if (positions[ix] !is null && positions[ix] !is DELETED_ENTRY)
            {
                if (!haspos(positions[ix]))
                {
                    throw new ValueException("Couldn't find position in table");
                }
                StepList list = getpos(positions[ix]);
                if (list is null || list !is steplists[ix])
                {
                    throw new ValueException("Got wrong step list for position.");
                }
                found++;
            }
        }

        if (numstored != found)
        {
            throw new ValueException(Format(
                "found different number of positions {} != {}", numstored, found));
        }
        return true;
    }

    bool haspos(Position pos)
    {
        int key = pos.zobrist & keymask;
        while (positions[key] !is null)
        {
            assert(positions[key].zobrist != pos.zobrist || positions[key] == pos, "Zobrist key collision");

            if (positions[key] !is DELETED_ENTRY &&
                    positions[key].zobrist == pos.zobrist && positions[key] == pos)
                return true;
            key = (key + keystep) & keymask;
        }

        return false;
    }

    void addpos(Position pos, StepList steps)
    {
        double load = cast(double)numstored / positions.length;
        if (load >= MAX_LOAD)
            expand();

        int key = pos.zobrist & keymask;
        while (positions[key] !is null && positions[key] !is DELETED_ENTRY)
        {
            key = (key + keystep) & keymask;
        }

        positions[key] = pos;
        steplists[key] = steps;
        numstored++;
    }

    Position delpos(Position pos)
    {
        int key = pos.zobrist & keymask;
        int nextkey = (key + keystep) & keymask;
        Position fpos = null;

        // find the location
        while (positions[key] !is null)
        {
            if (positions[key] == pos)
                break;
            key = nextkey;
            nextkey = (nextkey + keystep) & keymask;
        }
        // if the position was in the table.
        if (positions[key] !is null)
        {
            fpos = positions[key];
            positions[key] = DELETED_ENTRY;
            steplists[key] = null;
            numstored--;
        }

        return fpos;
    }

    StepList getpos(Position pos)
    {
        int key = pos.zobrist & keymask;
        while (positions[key] !is null
                && (positions[key] is DELETED_ENTRY
                || positions[key] != pos))
        {
            key = (key + keystep) & keymask;
        }
        assert (positions[key] !is null);
        return steplists[key];
    }

    int length()
    {
        return numstored;
    }

    void free_items()
    {
        for (int key=0; key < positions.length; key++)
        {
            if (positions[key] !is null && positions[key] !is DELETED_ENTRY)
            {
                Position.free(positions[key]);
                StepList.free(steplists[key]);
            }
            positions[key] = null;
            steplists[key] = null;
        }
        numstored = 0;
    }
}


Position parse_long_str(char[] boardstr)
{
    char[][] rowstrs = splitLines!(char)(boardstr);
    if (rowstrs.length < 10)
        throw new InvalidBoardException("Not enough lines for a full board.");
    rowstrs[0] = trim!(char)(rowstrs[0]);
    foreach (int rownum, char[] row; rowstrs[1..10])
    {
        row = trim!(char)(row);
        if (row.length < 17)
            throw new InvalidBoardException("Short row encountered in board, rownum " ~
                   to!(char[])(rownum+2));
    }

    Side color;
    char sidechar = rowstrs[0][length-1];
    if (sidechar == 'w' || sidechar == 'g')
    {
        color = Side.WHITE;
    } else if (sidechar == 'b' || sidechar == 's')
    {
        color = Side.BLACK;
    } else
    {
        throw new InvalidBoardException("Invalid side to move.");
    }

    auto first_row = new Text!(char)(rowstrs[1]);
    if (!first_row.trim().equals("+-----------------+"))
        throw new InvalidBoardException("Invalid board header.");

    ulong[Piece.max+1] bitboards;
    foreach (int lineix, char[] line; rowstrs[2..10])
    {
        if (to!(int)(line[0..1]) != 8-lineix)
            throw new InvalidBoardException(Format("Invalid row marker, expected {} got {}",
                       7-lineix, line[0]));
        for (int squareix = 3; squareix < 18; squareix += 2)
        {
            char piecech = line[squareix];
            int colnum = (squareix-3) / 2;
            ulong squarebit = 1UL << (((7-lineix)*8) + (7-colnum));
            if (find("xX .", piecech) != -1)
            {
                bitboards[0] |= squarebit;
                continue;
            }
            int piece = find("RCDHMErcdhme", piecech);
            if (piece == -1)
                throw new InvalidBoardException("Invalid piece encountered.");

            bitboards[piece+1] |= squarebit;
        }
    }
    return new Position(color, 4, bitboards);
}

Position parse_short_str(Side side, int steps, char[] boardstr)
{
    if (steps > 4 || steps < 1)
        throw new InvalidBoardException("Incorrect number of steps left.");

    boardstr = trim!(char)(boardstr);
    if (boardstr.length < 66)
        throw new InvalidBoardException("Not long enough for full board.");

    ulong[Piece.max+1] bitboards;
    foreach (int squareix, char piecech; boardstr[1..65])
    {
        int piece = find(" RCDHMErcdhme", piecech);
        if (piece == -1)
            throw new InvalidBoardException(Format("Invalid piece encountered. {} {}", boardstr, piecech));
        bitboards[piece] |= 1UL << (63-squareix);
    }
    return new Position(side, steps, bitboards);
}

char[] random_setup_move(Side side)
{
    char[] setup;

    char[] piece_chars;
    piece_chars = "RRRRRRRRCCDDHHME".dup;
    char[] rank_chars = "12";
    if (side == Side.BLACK)
    {
        piece_chars = "rrrrrrrrccddhhme".dup;
        rank_chars = "87";
    }

    for (int i=0; i < 16; i++)
    {
        int pix = rand.uniformR!(int)(piece_chars.length);
        char piece = piece_chars[pix];
        piece_chars[pix] = piece_chars[length-1];
        piece_chars.length = piece_chars.length - 1;

        int start = setup.length;
        setup.length = setup.length + 4;
        setup[start] = piece;
        setup[start+1] = "abcdefgh"[i % 8];
        setup[start+2] = rank_chars[i / 8];
        setup[start+3] = ' ';
    }

    return setup;
}

struct PlayoutResult
{
    int endscore;
    int length;
}

PlayoutResult playout_steps(Position pos, int max_length = 0)
{

    PlayoutResult result;
    result.endscore = 0;
    result.length = 0;

    StepList steps = StepList.allocate();

    Side curside = pos.side;
    while (!pos.is_endstate() && (max_length == 0 || result.length < max_length))
    {
        pos.get_steps(steps);
        if (steps.numsteps == 0)
        {
            if (pos.side == Side.WHITE)
            {
                result.endscore = -1;
            } else {
                result.endscore = 1;
            }
            break;
        }
        int stepix = rand.uniformR!(int)(steps.numsteps);
        pos.do_step(steps.steps[stepix]);
        steps.clear();
        if (pos.side != curside)
            result.length += 1;
    }
    if (result.endscore == 0)
        result.endscore = pos.endscore();

    assert (result.endscore != 0);

    StepList.free(steps);

    return result;
}

real FAME(Position pos, real scale = 33.695652173913032)
{
    static const int[] matchscore = [256, 85, 57, 38, 25, 17, 11, 7];

    real famescore = 0;

    int wrabbits = popcount(pos.bitBoards[Piece.WRABBIT]);
    int brabbits = popcount(pos.bitBoards[Piece.BRABBIT]);
    int wr_left = wrabbits;
    int br_left = brabbits;

    Piece wp_ix = Piece.WELEPHANT;
    int wused = 0;
    Piece bp_ix = Piece.BELEPHANT;
    int bused = 0;

    for (int i=0; i < 8; i++)
    {
        Piece wpiece = Piece.EMPTY;
        while (wpiece == Piece.EMPTY)
        {
            if (wp_ix != Piece.EMPTY
                    && popcount(pos.bitBoards[wp_ix]) - wused > 0)
            {
                wpiece = wp_ix;
                wused++;
            } else {
                wp_ix--;
                wused = 0;
                if (wp_ix < Piece.WRABBIT)
                {
                    wp_ix = Piece.EMPTY;
                    break;
                }
            }
        }

        Piece bpiece = Piece.EMPTY;
        while (bpiece == Piece.EMPTY)
        {
            if (bp_ix != Piece.EMPTY
                    && popcount(pos.bitBoards[bp_ix]) - bused > 0)
            {
                bpiece = bp_ix;
                bused++;
            } else {
                bp_ix--;
                bused = 0;
                if (bp_ix < Piece.BRABBIT)
                {
                    bp_ix = Piece.EMPTY;
                    break;
                }
            }
        }

        if (wp_ix < Piece.WCAT && bp_ix < Piece.BCAT)
            break;

        if (wpiece <= Piece.WRABBIT)
            wr_left--;

        if (bpiece <= Piece.BRABBIT)
            br_left--;

        if (wpiece > bpiece - Piece.WELEPHANT)
        {
            famescore += matchscore[i];
        } else if (wpiece < bpiece - Piece.WELEPHANT)
        {
            famescore -= matchscore[i];
        }
    }

    if (pos.placement[Side.BLACK])
    {
        int bpieces = popcount(pos.placement[Side.BLACK]
            & ~pos.bitBoards[Piece.BRABBIT]);
        famescore += wr_left * (600.0/(brabbits+(2*bpieces)));
    } else {
        famescore = 3369.562173913032;
    }

    if (pos.placement[Side.WHITE])
    {
        int wpieces = popcount(pos.placement[Side.WHITE]
            & ~pos.bitBoards[Piece.WRABBIT]);
        famescore -= br_left * (600.0/(wrabbits+(2*wpieces)));
    } else {
        famescore = -3369.562173913032;
    }

    return famescore / scale;
}

const static int[] pop_offset = [24, 0, 4, 6, 8, 10, 11, 12, 16, 18, 20, 22, 23];
const static int[] pop_mask = [0, 0xF, 0x3, 0x3, 0x3, 0x1, 0x1, 0xF, 0x3, 0x3, 0x3, 0x1, 0x1];

int population(Position pos)
{
    int count = 0;
    if (pos.bitBoards[Piece.WELEPHANT])
        count = 1 << pop_offset[Piece.WELEPHANT];
    if (pos.bitBoards[Piece.WCAMEL])
        count |= 1 << pop_offset[Piece.WCAMEL];
    count |= popcount(pos.bitBoards[Piece.WHORSE]) << pop_offset[Piece.WHORSE];
    count |= popcount(pos.bitBoards[Piece.WDOG]) << pop_offset[Piece.WDOG];
    count |= popcount(pos.bitBoards[Piece.WCAT]) << pop_offset[Piece.WCAT];
    count |= popcount(pos.bitBoards[Piece.WRABBIT]) << 0; //pop_offset[Piece.WRABBIT]; workaround compiler bug

    if (pos.bitBoards[Piece.BELEPHANT])
        count |= 1 << pop_offset[Piece.BELEPHANT];
    if (pos.bitBoards[Piece.BCAMEL])
        count |= 1 << pop_offset[Piece.BCAMEL];
    count |= popcount(pos.bitBoards[Piece.BHORSE]) << pop_offset[Piece.BHORSE];
    count |= popcount(pos.bitBoards[Piece.BDOG]) << pop_offset[Piece.BDOG];
    count |= popcount(pos.bitBoards[Piece.BCAT]) << pop_offset[Piece.BCAT];
    count |= popcount(pos.bitBoards[Piece.BRABBIT]) << pop_offset[Piece.BRABBIT];

    debug (check_population)
    {
        Stdout("Check population count").newline;
        for (Piece p = Piece.WRABBIT; p <= Piece.BELEPHANT; p++)
        {
            int p2c = pop2count(count, p);
            int pc = popcount(pos.bitBoards[p]);
            if (p2c != pc)
            {
                Stdout.format("p2c {} != pc {} for {} from {:X}", p2c, pc, p,
                        count).newline;
                Stdout.format("piece board: {:X}", pos.bitBoards[p]).newline;
                Stdout.format("offset: {} mask: {:X}", pop_offset[p],
                        pop_mask[p]).newline;
                debug
                {
                    assert(false, "Bad population count");
                }
            }
        }
    }

    return count;
}

int count2pop(int population, Piece piece, int count)
{
    population = population & ~(pop_mask[piece] << pop_offset[piece]);
    population |= (count & pop_mask[piece]) << pop_offset[piece];
    return population;
}

int pop2count(int population, Piece piece)
{
    return (population >> pop_offset[piece]) & pop_mask[piece];
}

class FastFAME
{
    int[int] cache;
    real scale;

    this(real s = 33.695652173913032)
    {
        scale = s;
    }

    int score(Position pos)
    {
        return score(population(pos));
    }

    int score(int population)
    {
        if (population in cache)
        {
            return cache[population];
        }

        int score = cast(int)(popfame(population));
        cache[population] = score;
        return score;
    }

    real popfame(int population)
    {
        static const int[] matchscore = [256, 85, 57, 38, 25, 17, 11, 7];

        real famescore = 0;

        int wrabbits = pop2count(population, Piece.WRABBIT);
        int brabbits = pop2count(population, Piece.BRABBIT);
        int wr_left = wrabbits;
        int br_left = brabbits;

        Piece wp_ix = Piece.WELEPHANT;
        int wused = 0;
        Piece bp_ix = Piece.BELEPHANT;
        int bused = 0;

        for (int i=0; i < 8; i++)
        {
            Piece wpiece = Piece.EMPTY;
            while (wpiece == Piece.EMPTY)
            {
                if (wp_ix != Piece.EMPTY
                        && (pop2count(population, wp_ix) - wused) > 0)
                {
                    wpiece = wp_ix;
                    wused++;
                } else {
                    wp_ix--;
                    wused = 0;
                    if (wp_ix < Piece.WRABBIT)
                    {
                        wp_ix = Piece.EMPTY;
                        break;
                    }
                }
            }

            Piece bpiece = Piece.EMPTY;
            while (bpiece == Piece.EMPTY)
            {
                if (bp_ix != Piece.EMPTY
                        && (pop2count(population, bp_ix) - bused) > 0)
                {
                    bpiece = bp_ix;
                    bused++;
                } else {
                    bp_ix--;
                    bused = 0;
                    if (bp_ix < Piece.BRABBIT)
                    {
                        bp_ix = Piece.EMPTY;
                        break;
                    }
                }
            }

            if (wp_ix < Piece.WCAT && bp_ix < Piece.BCAT)
                break;

            if (wpiece <= Piece.WRABBIT)
                wr_left--;

            if (bpiece <= Piece.BRABBIT)
                br_left--;

            if (wpiece > bpiece - Piece.WELEPHANT)
            {
                famescore += matchscore[i];
            } else if (wpiece < bpiece - Piece.WELEPHANT)
            {
                famescore -= matchscore[i];
            }
        }

        int bpieces = 0;
        for (Piece i=Piece.BCAT; i <= Piece.BELEPHANT; i++)
        {
            bpieces += pop2count(population, i);
        }
        if (bpieces || brabbits)
        {
            famescore += wr_left * (600.0/(brabbits+(2*bpieces)));
        } else {
            return 3369.562173913032 / scale;
        }

        int wpieces = 0;
        for (Piece i=Piece.WCAT; i <= Piece.WELEPHANT; i++)
        {
            wpieces += pop2count(population, i);
        }
        if (wpieces || wrabbits)
        {
            famescore -= br_left * (600.0/(wrabbits+(2*wpieces)));
        } else {
            return -3369.562173913032 / scale;
        }

        return famescore / scale;
    }
}

class InvalidBoardException : Exception
{
    this(char[] msg)
    {
        super(msg);
    }
}

class ValueException : Exception
{
    this(char[] msg)
    {
        super(msg);
    }
}

