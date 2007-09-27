
import std.intrinsic;
import std.stdio;
import std.string;
import std.random;

import zobristkeys;

typedef byte bitix;

enum Side : byte { WHITE, BLACK }
enum Piece : byte { EMPTY, WRABBIT, WCAT, WDOG, WHORSE, WCAMEL, WELEPHANT, 
                    BRABBIT, BCAT, BDOG, BHORSE, BCAMEL, BELEPHANT }

const ulong TRAPS = 0x0000240000240000UL;

const ulong NOT_A_FILE = 0x7F7F7F7F7F7F7F7FUL;
const ulong NOT_H_FILE = 0xFEFEFEFEFEFEFEFEUL;
const ulong RANK_1 = 0xFFUL;
const ulong RANK_8 = 0xFF00000000000000UL;
const ulong NOT_RANK_1 = ~RANK_1;
const ulong NOT_RANK_8 = ~RANK_8;
const ulong NOT_EDGE = NOT_A_FILE & NOT_H_FILE & NOT_RANK_1 & NOT_RANK_8;

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

char[] ix_to_alg(bitix index)
{
    char[] alg;
    alg ~= "hgfedcba"[index % 8];
    alg ~= toString((index / 8) + 1);
    
    return alg;
}

static const ulong INV_STEP = 3UL;

struct Step
{
    ulong frombit, tobit;
    bool push;

    void copy(Step other)
    {
        frombit = other.frombit;
        tobit = other.tobit;
        push = other.push;
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
        assert((f == 64 && t == 64) || f != t, format("from %d == to %d", f, t));
        assert((f == 64 && t == 64) || (f >= 0 && f < 64), format("from %d out of bounds", f));

        frombit = 1UL << f;
        tobit = 1UL << t;
        push = p;
    }

    void set(ulong f, ulong t, bool p=false)
    {
        assert((f == INV_STEP && t == INV_STEP) || f != t, format("from %d == to %d", f, t));
        assert((f == INV_STEP && t == INV_STEP) || popcount(f) == 1, format("invalid f %d", f));
        assert(t == INV_STEP || popcount(t) == 1, format("invalid t %d", t));

        frombit = f;
        tobit = t;
        push = p;
    }

   void set(Step other)
   {
      frombit = other.frombit;
      tobit = other.tobit;
      push = other.push;
   } 
}

class StepList
{
    const int ALLOCA_MULT = 2;
    Step[] steps;
    int numsteps = 0;

    private static StepList[] reservelists;
    private static int reservesize;
    static int allocated = 0;

    static StepList allocate()
    {
        if (reservesize)
        {
            reservesize--;
            StepList returnlist = reservelists[reservesize];
            reservelists[reservesize] = null;
            returnlist.clear();
            return returnlist;
        }

        return new StepList();
    }

    static void free(StepList list)
    {
        if (reservelists.length == reservesize)
            reservelists.length = (reservelists.length+1) * 2;

        reservelists[reservesize++] = list;
    }

    this(int startlength=4)
    {
        steps.length = startlength;
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
        return newlist;
    }

    Step[] getsteps()
    {
        return steps[0..numsteps];
    }

    Step* newstep()
    {
        if (numsteps == steps.length)
        {
            steps.length = steps.length * ALLOCA_MULT;
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
                move ~= ".RCDHMErcdhme"[current.pieces[step.fromix]];
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
                        throw new ValueException(format(
                                "Piece disappeared without being trapped. %s",
                                move));
                    }
                    move ~= "x ";
                }
            }
        }

        if (move.length == 0)
            throw new ValueException("Tried to make move with no or pass only steps");

        return move[0..length-1];
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

    invariant
    {
        ulong usedsquares = 0;
        foreach(int piece, ulong board; bitBoards)
        {
            if ((usedsquares & board) != 0)
            {
                assert (0, "two pieces on same square");
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
                    return false;
                }
            }
        }
        if (usedsquares != ALL_BITS_SET)
        {
            assert(0, format("not all squares were accounted for, %X", usedsquares));
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
        assert (checkfrozen == frozen, format("Incorrect frozen board encountered. %X, %X", frozen, checkfrozen));

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
                        format("Incorrect strongest neighbor encountered. %d %d %d %d",
                               sideix, sqix, strong, strongest[sideix][sqix]));
            }
        }
    }

    private static Position[] reserve;
    private static int reservesize;
    static int allocated;

    static int reserved()
    {
        return reservesize;
    }

    static int rlistsize()
    {
        return reserve.length;
    }

    static Position allocate()
    {
        if (reservesize)
        {
            reservesize--;
            Position pos = reserve[reservesize];
            reserve[reservesize] = null;
            return pos;
        }

        return new Position();
    }

    static Position allocate(Position other)
    {
        if (reservesize)
        {
            reservesize--;
            Position pos = reserve[reservesize];
            reserve[reservesize] = null;
            pos.copy(other);
            return pos;
        }

        return new Position(other);
    }


    static void free(Position pos)
    {
        if (reserve.length == reservesize)
            reserve.length = (reserve.length+1) * 2;

        reserve[reservesize++] = pos;
    }


    this()
    {
        this.bitBoards[0] = ALL_BITS_SET;
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

        allocated++;
    }

    private void update_derived()
    {
        if (side)
            zobrist = ZOBRIST_SIDE;
        else
            zobrist = 0;
        zobrist ^= ZOBRIST_STEP[stepsLeft];
        for (int pix = 1; pix <= Piece.max; pix++)
        {
            ulong board = bitBoards[pix];
            while (board)
            {
                ulong piecebit = board & ((board ^ ALL_BITS_SET) + 1);
                board ^= piecebit;
                bitix pieceix = bitindex(piecebit);
                zobrist ^= ZOBRIST_PIECE[pix][pieceix];
            }
        }
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
            char[] rowstr = std.string.toString(rownum) ~ "| ";
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

    private void updatefrozen(Side side, Piece piece, Step step)
    {
        Side oside = cast(Side)(side ^ 1);
        bitix fromix = step.fromix;
        bitix toix = step.toix;

        if (pieces[toix] != Piece.EMPTY)    // piece may have been trapped
        {
            Piece rank = cast(Piece)((piece + side + 6) % (Piece.max+1));
            ulong tobit = step.tobit;
            // unfreeze any friendly neighbors
            frozen ^= frozen & neighbors_of(tobit) & placement[side];
            // update strongest neighbor
            ulong checkbits = 0;
            int sqix = void;
            if (tobit & NOT_A_FILE)
            {
                sqix = toix+1;
                if (strongest[side][sqix] < piece)
                {
                    strongest[side][sqix] = piece;
                    if (pieces[sqix] < rank)
                        checkbits |= tobit << 1;
                }
            }
            if (tobit & NOT_H_FILE)
            {
                sqix = toix-1;
                if (strongest[side][sqix] < piece)
                {
                    strongest[side][sqix] = piece;
                    if (pieces[sqix] < rank)
                        checkbits |= tobit >> 1;
                }
            }
            if (tobit & NOT_RANK_8)
            {
                sqix = toix+8;
                if (strongest[side][sqix] < piece)
                {
                    strongest[side][sqix] = piece;
                    if (pieces[sqix] < rank)
                        checkbits |= tobit << 8;
                }
            }
            if (tobit & NOT_RANK_1)
            {
                sqix = toix-8;
                if (strongest[side][sqix] < piece)
                {
                    strongest[side][sqix] = piece;
                    if (pieces[sqix] < rank)
                        checkbits |= tobit >> 8;
                }
            }
            // update neighboring enemies
            frozen |= placement[oside] & checkbits & (~neighbors_of(placement[oside]));
        }
        
        updatefrozen(side, piece, step.frombit);
    }

    private void updatefrozen(Side side, Piece piece, ulong frombit)
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
                                Piece rank = cast(Piece)((pieces[nix] + oside + 6) % (Piece.max+1));
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
        //writefln(to_long_str());
        //writefln("%d, %d", step.from, step.to);

        zobrist ^= ZOBRIST_STEP[stepsLeft];

        if (step.tobit != INV_STEP) // not a pass or trap step
        {
            bitix fromix = step.fromix;
            bitix toix = step.toix;
            Piece piece = pieces[fromix];
            assert (piece != Piece.EMPTY);
            assert (pieces[toix] == Piece.EMPTY);

            Side side;
            if (placement[Side.WHITE] & step.frombit)
            {
                side = Side.WHITE;
            } else
            {
                side = Side.BLACK;
                assert (placement[Side.BLACK] & step.frombit);
            }
            ulong tofrom = step.frombit ^ step.tobit;
            bitBoards[Piece.EMPTY] ^= tofrom;
            bitBoards[piece] ^= tofrom;
            placement[side] ^= tofrom;
            pieces[fromix] = Piece.EMPTY;
            pieces[toix] = piece;

            zobrist ^= ZOBRIST_PIECE[piece][fromix] ^
                       ZOBRIST_PIECE[piece][toix];

            ulong trapped = (neighbors_of(step.frombit) & TRAPS)
                    & placement[side];
            if (trapped && (trapped & ~neighbors_of(placement[side])))
            {
                placement[side] ^= trapped;
                bitix trapix = bitindex(trapped);
                Piece piecetr = pieces[trapix];
                pieces[trapix] = Piece.EMPTY;
                bitBoards[piecetr] ^= trapped;
                bitBoards[Piece.EMPTY] ^= trapped;
                zobrist ^= ZOBRIST_PIECE[piecetr][trapix];
                if (trapix != toix)
                    updatefrozen(side, piecetr, trapped);
            }
            updatefrozen(side, piece, step);
            stepsLeft--;

            if (inpush != step.push)
            {
                zobrist ^= ZOBRIST_INPUSH;
            }
            zobrist ^= ZOBRIST_LAST_PIECE[lastpiece][lastfrom];
            lastpiece = piece;
            lastfrom = fromix;
            inpush = step.push;
            zobrist ^= ZOBRIST_LAST_PIECE[lastpiece][lastfrom];
        }
        
        if (stepsLeft < 1 || 
            (step.frombit == INV_STEP && step.tobit == INV_STEP)) // pass step
        {
            assert (!inpush, format("stepsleft %d, step.from %d, step.to %d", stepsLeft, step.fromix, step.toix));
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

        foreach (char[] step; split(move))
        {
            Piece piece = cast(Piece)(find("RCDHMErcdhme", step[0]) +1);
            if (piece <= 0)
            {
                throw new ValueException(format("Step starts with invalid piece. %s", step));
            }
            int column = find("abcdefgh", step[1])+1;
            if (column < 1)
            {
                throw new ValueException(format("Step has invalid column. %s", step));
            }
            if (!isNumeric(step[2]))
            {
                throw new ValueException(format("Step column is not a number. %s", step));
            }
            int rank = atoi(step[2..3])-1;
            if (rank < 0 || rank > 7)
            {
                throw new ValueException(format("Step column is invalid. %s", step));
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
                            throw new ValueException(format("Step moves non-existant piece. %s", step));
                        }
                        if (pieces[fromix+8] != Piece.EMPTY)
                        {
                            throw new ValueException(format("Step tries to move to an occupied square. %s", step));
                        }
                        Step bstep;
                        bstep.set(from, from << 8);
                        do_step(bstep);
                        break;
                    case "s":
                        if (pieces[fromix] != piece)
                        {
                            throw new ValueException(format("Step moves non-existant piece. %s", step));
                        }
                        if (pieces[fromix-8] != Piece.EMPTY)
                        {
                            throw new ValueException(format("Step tries to move to an occupied square. %s", step));
                        }
                        Step bstep;
                        bstep.set(from, from >> 8);
                        do_step(bstep);
                        break;
                    case "e":
                        if (pieces[fromix] != piece)
                        {
                            throw new ValueException(format("Step moves non-existant piece. %s", step));
                        }
                        if (pieces[fromix-1] != Piece.EMPTY)
                        {
                            throw new ValueException(format("Step tries to move to an occupied square. %s", step));
                        }
                        Step bstep;
                        bstep.set(from, from >> 1);
                        do_step(bstep);
                        break;
                    case "w":
                        if (pieces[fromix] != piece)
                        {
                            throw new ValueException(format("Step moves non-existant piece. %s", step));
                        }
                        if (pieces[fromix+1] != Piece.EMPTY)
                        {
                            throw new ValueException(format("Step tries to move to an occupied square. %s", step));
                        }
                        Step bstep;
                        bstep.set(from, from << 1);
                        do_step(bstep);
                        break;
                    case "x":
                        break;
                    default:
                        throw new ValueException(format("Step direction is invalid. %s", step));
                }
            } else {
                if (pieces[fromix] != Piece.EMPTY)
                {
                    throw new ValueException(format("Tried to place a piece in a non-empty square. %s", step));
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

    void get_single_steps(StepList steps)
    {
        Step* step;
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

    void get_double_steps(StepList steps)
    {
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
            ulong pospushers = neighbors_of(lfbit) & placement[side];
            while (pospushers)
            {
                ulong pushbit = pospushers & -pospushers;
                pospushers ^= pushbit;
                bitix fromix = bitindex(pushbit);
                if (pieces[fromix]+enemyoffset > lastpiece)
                {
                    Step* step = steps.newstep();
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

                        Step* step = steps.newstep();
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
                            Step* step = steps.newstep();
                            step.set(frombit, tobit, true);
                        }
                    }
                }
            }
        }
    }

    void get_steps(StepList steps)
    {
        get_double_steps(steps);
        if (stepsLeft != 4 && !inpush)
        {
            Step* step = steps.newstep();
            step.set(INV_STEP, INV_STEP);
        }
        if (!inpush)
        {
            get_single_steps(steps);
        }
    }

    PosStore get_moves()
    {
        StepList nextsteps = new StepList(32);
        PosStore partial = new PosStore();
        PosStore nextpart = new PosStore();
        PosStore finished = new PosStore();
        Position newpos = new Position();
        partial.addpos(this.dup, new StepList());
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
        Step passmove;
        passmove.set(INV_STEP, INV_STEP);
        Position nullmove = this.dup;
        nullmove.do_step(passmove);
        finished.delpos(nullmove);
        return finished;
    }
}

class PosStore
{
    private:
        const int START_SIZE = 14;
        const double MAX_LOAD = 0.7;
        Position DELETED_ENTRY;
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
    this()
    {
        DELETED_ENTRY = new Position();
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
            throw new ValueException(format(
                "found different number of positions %d != %d", numstored, found));
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

    void delpos(Position pos)
    {
        int key = pos.zobrist & keymask;
        int nextkey = (key + keystep) & keymask;
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
            positions[key] = DELETED_ENTRY;
            steplists[key] = null;
            numstored--;
        }
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
    char[][] rowstrs = std.string.splitlines(boardstr);
    if (rowstrs.length < 10)
        throw new InvalidBoardException("Not enough lines for a full board.");
    rowstrs[0] = std.string.strip(rowstrs[0]);
    foreach (int rownum, char[] row; rowstrs[1..10])
    {
        row = std.string.strip(row);
        if (row.length < 17)
            throw new InvalidBoardException("Short row encountered in board, rownum " ~
                   std.string.toString(rownum+2));
    }

    Side color;
    if (rowstrs[0][length-1] == 'w')
    {
        color = Side.WHITE;
    } else if (rowstrs[0][length-1] == 'b')
    {
        color = Side.BLACK;
    } else
    {
        throw new InvalidBoardException("Invalid side to move.");
    }
    
    if (!std.string.cmp(rowstrs[1], "+-----------------+"))
        throw new InvalidBoardException("Invalid board header.");

    ulong[Piece.max+1] bitboards;
    foreach (int lineix, char[] line; rowstrs[2..10])
    {
        if (std.string.atoi(line[0..1]) != 8-lineix)
            throw new InvalidBoardException(format("Invalid row marker, expected %d got %s",
                       7-lineix, line[0]));
        for (int squareix = 3; squareix < 18; squareix += 2)
        {
            char piecech = line[squareix];
            int colnum = (squareix-3) / 2;
            ulong squarebit = 1UL << (((7-lineix)*8) + (7-colnum));
            if (std.string.find("xX .", piecech) != -1)
            {
                bitboards[0] |= squarebit;
                continue;
            }
            int piece = std.string.find("RCDHMErcdhme", piecech);
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

    boardstr = std.string.strip(boardstr);
    if (boardstr.length < 66)
        throw new InvalidBoardException("Not long enough for full board.");
    
    ulong[Piece.max+1] bitboards;
    foreach (int squareix, char piecech; boardstr[1..66])
    {
        int piece = std.string.find(" RCDHMErcdhme", piecech);
        if (piece == -1)
            throw new InvalidBoardException("Invalid piece encountered.");
        bitboards[piece] |= 1UL << (63-squareix);
    }
    return new Position(side, steps, bitboards);
}

struct PlayoutResult 
{
    int endscore;
    int length;
}

PlayoutResult playout_steps(Position pos)
{

    PlayoutResult result;
    StepList steps = StepList.allocate();
    Position movestart = Position.allocate(pos);
    while (!pos.is_endstate())
    {
        result.length += 1;
        pos.get_steps(steps);
        if (steps.numsteps == 0)
        {
            if (pos == movestart)
            {
                if (pos.side == Side.WHITE)
                {
                    result.endscore = -1;
                } else {
                    result.endscore = 1;
                }
                break;
            } else
            {
                pos.copy(movestart);
            }
        }
        int stepix = rand() % steps.numsteps;
        pos.do_step(steps.steps[stepix]);
        if (pos.side != movestart.side)
        {
            movestart.copy(pos);
        }
        steps.clear();
    }
    if (result.endscore == 0)
        result.endscore = pos.endscore();

    assert (result.endscore != 0);

    Position.free(movestart);
    StepList.free(steps);

    return result;
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

