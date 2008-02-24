
import std.c.string;
import std.conv;
import std.date;
import std.math;
import std.random;
import std.stdio;
import std.string;

import alphabeta;
import aeibot;
import goalsearch;
import logging;
import position;

const char[] BOT_NAME = "OpFor";
const char[] BOT_AUTHOR = "Janzert";

const int START_SEARCH_NODES = 30000;

int trap_safety(Position pos)
{
    const int BOTH_SAFE = 1;
    const int HOME_CONTROL = 2;
    const int AWAY_CONTROL = 5;

    int score = 0;

    ulong c3_neighbors = neighbors_of(TRAP_C3);
    int trap_safe = 0;
    if (c3_neighbors & pos.bitBoards[Piece.WELEPHANT]
            || (popcount(c3_neighbors & pos.placement[Side.WHITE]) > 1))
        trap_safe |= 1;
    if (c3_neighbors & pos.bitBoards[Piece.BELEPHANT]
            || (popcount(c3_neighbors & pos.placement[Side.BLACK]) > 1))
        trap_safe |= 2;
    switch (trap_safe)
    {
        case 0:
            break;
        case 1:
            score += HOME_CONTROL;
            break;
        case 2:
            score -= AWAY_CONTROL;
            break;
        case 3:
            score -= BOTH_SAFE;
            break;
    }

    ulong f3_neighbors = neighbors_of(TRAP_F3);
    trap_safe = 0;
    if (f3_neighbors & pos.bitBoards[Piece.WELEPHANT]
            || (popcount(f3_neighbors & pos.placement[Side.WHITE]) > 1))
        trap_safe |= 1;
    if (f3_neighbors & pos.bitBoards[Piece.BELEPHANT]
            || (popcount(f3_neighbors & pos.placement[Side.BLACK]) > 1))
        trap_safe |= 2;
    switch (trap_safe)
    {
        case 0:
            break;
        case 1:
            score += HOME_CONTROL;
            break;
        case 2:
            score -= AWAY_CONTROL;
            break;
        case 3:
            score -= BOTH_SAFE;
            break;
    }

    ulong c6_neighbors = neighbors_of(TRAP_C6);
    trap_safe = 0;
    if (c6_neighbors & pos.bitBoards[Piece.WELEPHANT]
            || (popcount(c6_neighbors & pos.placement[Side.WHITE]) > 1))
        trap_safe |= 1;
    if (c6_neighbors & pos.bitBoards[Piece.BELEPHANT]
            || (popcount(c6_neighbors & pos.placement[Side.BLACK]) > 1))
        trap_safe |= 2;
    switch (trap_safe)
    {
        case 0:
            break;
        case 1:
            score += AWAY_CONTROL;
            break;
        case 2:
            score -= HOME_CONTROL;
            break;
        case 3:
            score += BOTH_SAFE;
            break;
    }

    ulong f6_neighbors = neighbors_of(TRAP_F6);
    trap_safe = 0;
    if (f6_neighbors & pos.bitBoards[Piece.WELEPHANT]
            || (popcount(f6_neighbors & pos.placement[Side.WHITE]) > 1))
        trap_safe |= 1;
    if (f6_neighbors & pos.bitBoards[Piece.BELEPHANT]
            || (popcount(f6_neighbors & pos.placement[Side.BLACK]) > 1))
        trap_safe |= 2;
    switch (trap_safe)
    {
        case 0:
            break;
        case 1:
            score += AWAY_CONTROL;
            break;
        case 2:
            score -= HOME_CONTROL;
            break;
        case 3:
            score += BOTH_SAFE;
            break;
    }

    return score;
}

// penalty for piece on trap, pinned or framed
int on_trap(Position pos)
{
    const int ON_TRAP[13] = [0, -6, -9, -12, -18, -33, -88, 6, 9, 12, 18, 33, 88];
    const int PINNED[13] = [0, 0, -2, -3, -5, -8, -22, 0, 2, 3, 5, 8, 22];
    const int FRAMER[13] = [0, 0, -1, -2, -3, -4, -11, 0, 1, 2, 3, 4, 11];

    int score = 0;
    ulong occupied_traps = ~pos.bitBoards[Piece.EMPTY] & TRAPS;
    while (occupied_traps)
    {
        ulong tbit = occupied_traps & -occupied_traps;
        occupied_traps ^= tbit;
        ulong tneighbors = neighbors_of(tbit);
        bitix tix = bitindex(tbit);
        Piece tpiece = pos.pieces[tix];
        Side tside = (tpiece > Piece.WELEPHANT) ? Side.BLACK : Side.WHITE;
        int pieceoffset = (tside == Side.WHITE) ? 6 : -6;
        
        if (pos.strongest[tside][tix] == Piece.WELEPHANT+pieceoffset
                || popcount(pos.placement[tside] & tneighbors) > 1)
        {
            score += ON_TRAP[tpiece] / 2;
        } else {
            score += ON_TRAP[tpiece];
        }

        ulong fneighbors = tneighbors & pos.placement[tside];
        if (popcount(fneighbors) == 1)
        {
            bitix fix = bitindex(fneighbors);
            score += PINNED[pos.pieces[fix]];

            tneighbors ^= fneighbors;
            if (tpiece == Piece.WRABBIT)
                tneighbors &= ~(tbit >> 8);
            else if (tpiece == Piece.BRABBIT)
                tneighbors &= ~(tbit << 8);

            if (!(tneighbors & pos.bitBoards[Piece.EMPTY]))
            {
                bool framed = true;
                real framing_score = 0;
                while (tneighbors)
                {
                    ulong ebit = tneighbors & -tneighbors;
                    tneighbors ^= ebit;
                    bitix eix = bitindex(ebit);
                    if (tpiece + pieceoffset > pos.pieces[eix]
                            && (neighbors_of(ebit) & pos.bitBoards[Piece.EMPTY]))
                    {
                        framed = false;
                        break;
                    }
                    Piece epiece;
                    epiece = pos.pieces[eix];
                    framing_score += FRAMER[epiece];
                }
                if (framed)
                {
                    score += ON_TRAP[tpiece];
                    score += framing_score;
                }
            }
        }
    }
    return score;
}

int map_elephant(Position pos)
{
    const int[] CENTRAL_MAP =
        [0, 1, 1, 2, 2, 1, 1, 0,
         1, 2, 2, 4, 4, 2, 2, 1,
         2, 3, 3, 6, 6, 3, 3, 2,
         3, 4, 6, 6, 6, 6, 4, 3,
         3, 4, 6, 6, 6, 6, 4, 3,
         2, 3, 3, 6, 6, 3, 3, 2,
         1, 2, 2, 4, 4, 2, 2, 1,
         0, 1, 1, 2, 2, 1, 1, 0];

    int score = 0;
    if (pos.bitBoards[Piece.WELEPHANT])
        score += CENTRAL_MAP[bitindex(pos.bitBoards[Piece.WELEPHANT])];
    if (pos.bitBoards[Piece.BELEPHANT])
        score -= CENTRAL_MAP[bitindex(pos.bitBoards[Piece.BELEPHANT])];

    return score;
}

int rabbit_wall(Position pos)
{
    const int[2] BLOCKING_BONUS = [5, -5];

    int score = 0;
    for (Side s; s < 2; s++)
    {
        int p_rabbit = Piece.WRABBIT;
        int p_cat = Piece.WCAT;
        int p_dog = Piece.WDOG;
        if (s == Side.BLACK)
        {
            p_rabbit = Piece.BRABBIT;
            p_cat = Piece.BCAT;
            p_dog = Piece.BDOG;
        }
        ulong rcandd = pos.bitBoards[p_rabbit] | pos.bitBoards[p_cat] | pos.bitBoards[p_dog];

        ulong rabbits = pos.bitBoards[p_rabbit];
        while (rabbits)
        {
            ulong rbit = rabbits & -rabbits;
            rabbits ^= rbit;

            ulong ladjacent = rbit & ~A_FILE;
            if (ladjacent)
            {
                ladjacent = (ladjacent << 1) | (ladjacent << 9) | (ladjacent >> 7);
                if (ladjacent & rcandd)
                {
                    score += BLOCKING_BONUS[s];
                }
            } else {
                score += BLOCKING_BONUS[s];
            }

            ulong radjacent = rbit & ~H_FILE;
            if (radjacent)
            {
                radjacent = (radjacent >> 1) | (radjacent >> 9) | (radjacent << 7);
                if (radjacent & rcandd)
                {
                    score += BLOCKING_BONUS[s];
                }
            } else {
                score += BLOCKING_BONUS[s];
            }
        }
    }

    return score;
}

int rabbit_open(Position pos)
{
    const int[8][2] NORABBIT_FILE = [[1, 1, 1, 2, 3, 5, 7, 0], [0, -7, -5, -3, -2, -1, -1, -1]];
    const int[8][2] NORABBIT_ADJ = [[1, 1, 1, 2, 2, 4, 4, 0], [0, -4, -4, -2, -2, -1, -1, -1]];
    const int[8][2] OPEN_FILE = [[2, 2, 2, 3, 10, 20, 40, 0], [0, -40, -20, -10, -3, -2, -2, -2]];
    const int[8][2] OPEN_ADJ = [[2, 2, 3, 20, 40, 80, 120, 0], [0, -120, -80, -40, -20, -3, -2, -2]];

    int score = 0;

    for (int file=0; file < 8; file++)
    {
        ulong fmask = H_FILE << file;
        ulong rabbits = fmask & pos.bitBoards[Piece.WRABBIT] & ~pos.frozen;
        if (rabbits)
        {
            bitix rix = msbindex(rabbits);
            ulong mask = H_FILE << rix;
            if (!(pos.bitBoards[Piece.BRABBIT] & mask))
            {
                bool open_file = false;
                int rank = rix/8;
                score += NORABBIT_FILE[Side.WHITE][rank];
                if (!(pos.placement[Side.BLACK] & mask))
                {
                    open_file = true;
                    score += OPEN_FILE[Side.WHITE][rank];
                }
                ulong adj_mask = 0;
                if (file != 0)
                    adj_mask = H_FILE << (rix+7);
                if (file != 7)
                    adj_mask |= H_FILE << (rix+9);
                if (!(pos.bitBoards[Piece.BRABBIT] & adj_mask))
                {
                    score += NORABBIT_ADJ[Side.WHITE][rank];
                    adj_mask &= NOT_RANK_8;
                    if (open_file && !(pos.placement[Side.BLACK] & adj_mask))
                    {
                        score += OPEN_ADJ[Side.WHITE][rank];
                    }
                }
            }
        }

        rabbits = fmask & pos.bitBoards[Piece.BRABBIT] & ~pos.frozen;
        if (rabbits)
        {
            bitix rix = bitindex(rabbits);
            ulong rmask = A_FILE >> (63-rix);
            if (!(pos.bitBoards[Piece.WRABBIT] & rmask))
            {
                bool open_file = false;
                int rank = rix / 8;
                score += NORABBIT_FILE[Side.BLACK][rank];
                if (!(pos.placement[Side.WHITE] & rmask))
                {
                    open_file = true;
                    score += OPEN_FILE[Side.BLACK][rank];
                }
                ulong adj_mask = 0;
                if (file != 0)
                    adj_mask = A_FILE >> (63 - (rix-9));
                if (file != 7)
                    adj_mask |= A_FILE >> (63 - (rix-7));
                if (!(pos.bitBoards[Piece.WRABBIT] & adj_mask))
                {
                    score += NORABBIT_ADJ[Side.BLACK][rank];
                    adj_mask &= NOT_RANK_1;
                    if (open_file && !(pos.placement[Side.WHITE] & adj_mask))
                    {
                        score += OPEN_ADJ[Side.BLACK][rank];
                    }
                }
            }
        }
    }

    return score;
}

int rabbit_home(Position pos)
{
    const static int[] side_mul = [1, -1];
    const static ulong[][] side_rank = [[RANK_1, RANK_2], [RANK_8, RANK_7]];
    const static int FIRST_ROW = 3;
    
    int score = 0;
    for (Side side = Side.WHITE; side <= Side.BLACK; side++)
    {
        Piece rpiece = (side == Side.WHITE) ? Piece.WRABBIT : Piece.BRABBIT;
        ulong rabbits = pos.bitBoards[rpiece];
        score += popcount(side_rank[side][0] & rabbits) * FIRST_ROW * side_mul[side];
        score += popcount(side_rank[side][1] & rabbits) * side_mul[side];
    }

    return score;
}

real rabbit_strength(Position pos, GoalSearch goals, real weak_w, real strong_w)
{
    const static int[] pieceval = [0, 0, 45, 60, 150, 200, 300,
          0, -45, -60, -150, -200, -300];
    const static int[] distval = [100, 100, 95, 75, 70,
          40, 30, 25, 20, 5, 1, 1, 1, 1, 0, 0];
    const static real[][] rankval = [[0, 0, 0, 0.2, 0.4, 1.0, 1.3, 0],
          [0, -1.2, -1.0, -0.5, -0.2, 0, 0, 0]];
    const static real[] goalval = [1.0,
          1.0, 1.0, 1.0, 1.0,
          1.0, 1.0, 0.9, 0.9,
          0.8, 0.8, 0.8, 0.8,
          0.7, 0.7, 0.7, 0.7];
    const static real[] weakgoal = [0,
          0.1, 0.2, 0.2, 0.4,
          0.5, 0.6, 0.7, 0.8,
          1, 1, 1, 1,
          1, 1, 1, 1];
    const static int[][] weakval = [[0, 0, -15, -30, -35, -40, -30, 0], 
         [0, 30, 40, 35, 30, 15, 0, 0]];
    const static int power_balance = 1000;
    const static real full_weak = 6000;
    const static int full_strong = 8000;
    const static int[] rforward = [8, -8];
    const static int[] side_mul = [1, -1];

    int wscore = 0;
    real sscore = 0;
    ulong allpieces = (pos.placement[Side.WHITE] | pos.placement[Side.BLACK])
        & ~pos.bitBoards[Piece.WRABBIT] & ~pos.bitBoards[Piece.BRABBIT]
        & ~pos.frozen;
    int[16] pval;
    bitix[16] pixs;
    int num_pieces;
    while (allpieces)
    {
        ulong pbit = allpieces & -allpieces;
        allpieces ^= pbit;
        bitix pix = bitindex(pbit);

        pval[num_pieces] = pieceval[pos.pieces[pix]];
        pixs[num_pieces++] = pix;
    }

    for (Side s = Side.WHITE; s <= Side.BLACK; s++)
    {
        ulong rabbits;
        if (s == Side.WHITE)
        {
            rabbits = pos.bitBoards[Piece.WRABBIT] & ~(RANK_1 & RANK_2);
        } else {
            rabbits = pos.bitBoards[Piece.BRABBIT] & ~(RANK_8 & RANK_7);
        }
        while (rabbits)
        {
            ulong rbit = rabbits & -rabbits;
            rabbits ^= rbit;
            bitix rix = bitindex(rbit);
            uint forward = rix+rforward[s];

            int power = 0;
            for (int i=0; i < num_pieces; i++)
            {
                power += pval[i] * distval[taxicab_dist[forward][pixs[i]]];
            }
            power *= side_mul[s];
            power -= power_balance;

            int goalsteps = goals.board_depth[rix];
            goalsteps = (goalsteps < 16) ? goalsteps : 16;

            if (power <= 0)
            {
                real sfactor = -power / full_weak;
                sfactor = (sfactor < 1) ? sfactor : 1;
                debug (rabbit_strength)
                {
                    writefln("weak r at %s, gs %d, pf %.2f", ix_to_alg(rix), goalsteps, sfactor);
                }
                wscore += weakval[s][rix/8] * weakgoal[goalsteps] * sfactor;
            } else {
                power = (power < full_strong) ? power : full_strong;
                real rv = rankval[s][rix/8];
                real rval = power * rv * goalval[goalsteps];
                if (rbit & TRAPS)
                    rval /= 2;
                debug (rabbit_strength)
                {
                    writefln("strong r at %s, val %.2f final %d", ix_to_alg(rix), rval, cast(int)(rval*strong_w));
                }
                sscore += rval;
            }
        }
    }

    return (wscore * weak_w) + (sscore * strong_w);
}

int old_piece_strength(Position pos, int[64] pstrengths)
{
    const static int[] pieceval = [0, 0, 4, 6, 15, 20, 30,
          0, -4, -6, -15, -20, -30];
    const static int[] distval = [100, 100, 100, 90, 60,
          30, 15, 7, 4, 2, 2, 1, 1, 1, 0, 0];
    const static int MAX_POWER = 3000; // == pieceval[Piece.WELEPHANT] * distval[0];
    const static int MIN_POWER = -3000; // == pieceval[Piece.BELEPHANT] * distval[0];
    
    Piece[32] stronger;
    int[32] sixs;

    int pieceoffset = 6;
    int score = 0;
    ulong stronger_bits = (pos.placement[Side.WHITE] | pos.placement[Side.BLACK])
        & ~pos.bitBoards[Piece.WRABBIT] & ~pos.bitBoards[Piece.BRABBIT]
        & ~pos.frozen;
    for (int p = Piece.WCAT; p < Piece.WELEPHANT; p++)
    {
        int power = 0;
        int num_stronger = 0;

        stronger_bits &= ~pos.bitBoards[p] & ~pos.bitBoards[p+pieceoffset];
        ulong sbits = stronger_bits;
        while (sbits)
        {
            ulong sbit = sbits & -sbits;
            sbits ^= sbit;
            bitix pix = bitindex(sbit);

            stronger[num_stronger] = pos.pieces[pix];
            sixs[num_stronger++] = pix;
        }

        ulong pieces = pos.bitBoards[p] | pos.bitBoards[p+pieceoffset];
        while (pieces)
        {
            ulong pbit = pieces & -pieces;
            pieces ^= pbit;
            bitix pix = bitindex(pbit);

            int ppower = 0;
            for (int i=0; i < num_stronger; i++)
            {
                ppower += pieceval[stronger[i]] * distval[taxicab_dist[pix][sixs[i]]];
            }
            ppower = (ppower < MAX_POWER) ? ppower : MAX_POWER;
            ppower = (ppower > MIN_POWER) ? ppower : MIN_POWER;
            pstrengths[pix] = ppower;
            power += ppower;
        }
        score += power * pieceval[p];
    }

    return score;
}

int piece_strength(Position pos, int[64] pstrengths)
{
    const static int[] pieceval = [0, 0, 8, 12, 24, 36, 44,
          0, -8, -12, -24, -36, -44];
    const static int[] distval = [100, 100, 95, 90, 85,
          80, 40, 35, 30, 20, 1, 1, 1, 1, 0, 0];
    const static int[][] pmul = [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
          [0, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2],
          [0, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 2],
          [0, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2],
          [0, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2],
          [0, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2],
          [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
          [0, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2],
          [0, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 2],
          [0, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2],
          [0, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2],
          [0, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2],
          [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]];
    const static int MAX_POWER = 4400; // == pieceval[Piece.WELEPHANT] * distval[0] * pmul;
    const static int MIN_POWER = -4400; // == pieceval[Piece.BELEPHANT] * distval[0] * pmul;
    
    bitix[16] ixs;
    int value[16];
    Piece piece[16];

    int num_pieces = 0;

    int score = 0;
    ulong piece_bits = (pos.placement[Side.WHITE] | pos.placement[Side.BLACK])
        & ~pos.bitBoards[Piece.WRABBIT] & ~pos.bitBoards[Piece.BRABBIT];
    ulong pbits = piece_bits;
    while (pbits)
    {
        ulong pbit = pbits & -pbits;
        pbits ^= pbit;
        bitix pix = bitindex(pbit);

        piece[num_pieces] = pos.pieces[pix];
        value[num_pieces] = pieceval[pos.pieces[pix]];
        if (pbit & pos.frozen)
            value[num_pieces] >>= 3;
        ixs[num_pieces++] = pix;
    }

    debug (piece_strength)
    {
        writefln("%s\n%s", "wb"[pos.side], pos.to_long_str());
    }
    for (int p = num_pieces; p--;)
    {
        int ppower = 0;
        bitix pix = ixs[p];
        for (int s = num_pieces; s--;)
        {
            if (s != p)
            {
                ppower += value[s] * distval[taxicab_dist[pix][ixs[s]]] * pmul[piece[p]][piece[s]];
            }
        }
        ppower = (ppower < MAX_POWER) ? ppower : MAX_POWER;
        ppower = (ppower > MIN_POWER) ? ppower : MIN_POWER;
        pstrengths[pix] = ppower;
        score += ppower;
        debug (piece_strength)
        {
            writefln("piece %d at %s has %d power", pos.pieces[pix], ix_to_alg(pix), ppower);
        }
    }
    debug (piece_strength)
    {
        writefln("overall board piece strength %d", score);
    }
    return score;
}

int frozen_pieces(Position pos)
{
    static const int[13] FROZEN_PENALTY = [0, -6, -9, -12, -18, -33, -88, 6, 9, 12, 18, 33, 88];
    static const real ALMOST_FROZEN = 0.1;
    static const real[33] POPULATION_MUL =
           [0.8, 0.8, 0.8, 0.8, 0.8, 0.8, 0.8, 0.8, 0.8,
                 0.9, 0.9, 0.9, 0.9, 0.9, 0.9, 0.9, 0.9,
                 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0,
                 1.1, 1.1, 1.1, 1.1, 1.2, 1.2, 1.2, 1.2];

    int score = 0;
    for (int p=1; p < 12; p++)
    {
        score += popcount(pos.bitBoards[p] & pos.frozen) * FROZEN_PENALTY[p];
    }

    for (Side s=Side.WHITE; s <= Side.BLACK; s++)
    {
        int enemyoffset = 6;
        int pieceoffset = 0;
        if (s == Side.BLACK)
        {
            enemyoffset = 0;
            pieceoffset = 6;
        }
        ulong stronger = pos.placement[s^1] & ~pos.frozen;
        for (int p=Piece.WRABBIT; p <= Piece.WELEPHANT; p++)
        {
            stronger &= ~pos.bitBoards[p+enemyoffset];
            ulong nstronger = neighbors_of(stronger);
            score += (popcount(pos.bitBoards[p+pieceoffset] & ~pos.frozen & nstronger) * FROZEN_PENALTY[p]) * ALMOST_FROZEN;
        }
    }

    uint total_pop = popcount(~pos.bitBoards[Piece.EMPTY]);
    total_pop = (total_pop < 32) ? total_pop : 32;
    real pop_mul = POPULATION_MUL[total_pop];

    return cast(int)(score * pop_mul);
}

int mobility(Position pos, int[64] pstrengths, real blockade_w, real hostage_w)
{
    static const int[] BLOCKADE_VAL = [0, -5, -12, -16, -30, -55, -132,
                                5, 12, 16, 30, 55, 132];
    static const int[] HOSTAGE_VAL = [0, -10, -25, -39, -61, -110, -264,
                                10, 25, 39, 61, 110, 264];
    static const int[13] FROZEN_PENALTY = [0, -6, -9, -12, -18, -33, -88, 6, 9, 12, 18, 33, 88];
    static const int[] TRAP_DIST_MUL =
        [1, 1, 2, 1, 1, 2, 1, 1,
         1, 2, 2, 2, 2, 2, 2, 1,
         2, 2, 2, 2, 2, 2, 2, 2,
         1, 2, 2, 2, 2, 2, 2, 1,
         1, 2, 2, 2, 2, 2, 2, 1,
         2, 2, 2, 2, 2, 2, 2, 2,
         1, 2, 2, 2, 2, 2, 2, 1,
         1, 1, 2, 1, 1, 2, 1, 1];

    real bscore = 0;
    real hscore = 0;
    for (Side side = Side.WHITE; side <= Side.BLACK; side++)
    {
        int pieceoffset = 0;
        int enemyoffset = -6;
        if (side == Side.BLACK)
        {
            pieceoffset = 6;
            enemyoffset = 6;
        }

        ulong unsafe = 0;
        ulong tbits = TRAPS;
        while (tbits)
        {
            ulong tbit = tbits & -tbits;
            tbits ^= tbit;

            if (popcount(neighbors_of(tbit) & pos.placement[side]) < 2)
            {
                unsafe |= tbit;
            }
        }

        ulong empty_neighbors = neighbors_of(pos.bitBoards[Piece.EMPTY]);

        ulong bcheck = (pos.bitBoards[Piece.WELEPHANT+pieceoffset] | pos.bitBoards[Piece.WCAMEL+pieceoffset]
            | pos.bitBoards[Piece.WHORSE+pieceoffset]) & ~pos.frozen;
        while (bcheck)
        {
            ulong pbit = bcheck & -bcheck;
            bcheck ^= pbit;
            bitix pix = bitindex(pbit);
            ulong pneighbors = neighbors_of(pbit);

            if (popcount(pneighbors & pos.bitBoards[Piece.EMPTY]) > 1)
                continue;

            if ((pos.pieces[pix] >= (pos.strongest[side^1][pix] + enemyoffset))
                    || (popcount(pneighbors & pos.placement[side]) >= 2))
            {
                if ((pneighbors & pos.placement[side] & ~pos.bitBoards[Piece.WRABBIT+pieceoffset])
                    & empty_neighbors & ~unsafe)
                {
                    continue;
                }

                if (rabbit_steps(side, pneighbors & pos.bitBoards[Piece.WRABBIT+pieceoffset])
                            & pos.bitBoards[Piece.EMPTY])
                {
                    continue;
                }
            }

            bool can_push = false;
            ulong oneighbors = pneighbors & pos.placement[side^1] & empty_neighbors;
            while (oneighbors)
            {
                ulong obit = oneighbors & -oneighbors;
                oneighbors ^= obit;
                bitix oix = bitindex(obit);
                if (pos.pieces[pix] > pos.pieces[oix] + enemyoffset)
                {
                    can_push = true;
                    break;
                }
            }
            if (can_push)
                continue;

            if (pos.pieces[pix] >= (pos.strongest[side^1][pix] + enemyoffset))
            {
                // the piece is blockaded
                debug (mobility)
                {
                    writefln("b piece %d", pos.pieces[pix]);
                }
                bscore += BLOCKADE_VAL[pos.pieces[pix]];
            } else {
                // the piece is blockaded but actually a hostage
                real power_mul = pstrengths[pix] / (8800.0 * 5); // Should restrict the range -.2 to .2
                if (side)
                    power_mul = (power_mul < 0) ? 1+power_mul : 0.8;
                else
                    power_mul = (power_mul > 0) ? 1-power_mul : 0.8;
                // power_mul should now be .8 to 1
                debug (mobility)
                {
                    writefln("fb piece %d at %s, pp %.2f", pos.pieces[pix], ix_to_alg(pix), power_mul);
                }
                hscore += HOSTAGE_VAL[pos.pieces[pix]] * TRAP_DIST_MUL[pix] * power_mul;
                hscore += FROZEN_PENALTY[pos.pieces[pix]] * 3; // magic number is frozen_w
            }
        }

        ulong hcheck = (pos.placement[side] & ~pos.bitBoards[Piece.WRABBIT+pieceoffset]) & pos.frozen;
        if (hcheck)
        {
            ulong coverage = neighbors_of(pos.placement[side] & ~pos.bitBoards[Piece.WRABBIT+pieceoffset] & ~pos.frozen)
                & pos.bitBoards[Piece.EMPTY] & ~unsafe;
            for (int steps = 0; steps < 3; steps++)
            {
                coverage |= neighbors_of(coverage) & pos.bitBoards[Piece.EMPTY] & ~unsafe;
            }
            while (hcheck)
            {
                ulong pbit = hcheck & -hcheck;
                hcheck ^= pbit;

                ulong pneighbors = neighbors_of(pbit);
                if (popcount(pneighbors & coverage) < 2)
                {
                    bitix pix = bitindex(pbit);
                    real power_mul = pstrengths[pix] / (8800.0 * 5); // Should restrict the range -.2 to .2
                    if (side)
                        power_mul = (power_mul < 0) ? 1+power_mul : 0.8;
                    else
                        power_mul = (power_mul > 0) ? 1-power_mul : 0.8;
                    // power_mul should now be .8 to 1
                    debug (mobility)
                    {
                        writefln("h piece %d at %s, pp %.2f", pos.pieces[pix], ix_to_alg(pix), power_mul);
                    }
                    hscore += HOSTAGE_VAL[pos.pieces[pix]] * TRAP_DIST_MUL[pix] * power_mul;
                }
            }
        }
    }

    return cast(int)((bscore * blockade_w) + (hscore * hostage_w));
}

class ScoreSearch : ABSearch
{
    this(Logger l)
    {
        super(l);
    }

    int eval(Position pos)
    {
        float wscore = 0;
        for (Piece i = Piece.WRABBIT; i <= Piece.WELEPHANT; i++)
        {
            wscore += popcount(pos.bitBoards[i]) * i;
        }
        wscore *= popcount(pos.bitBoards[Piece.WRABBIT]) + 1;
        float wrpoints = 0;
        for (int rank = 1; rank <= 8; rank++)
        {
            ulong rmask = position.RANK_1 << (8*(rank-1));
            wrpoints += popcount(pos.bitBoards[Piece.WRABBIT] & rmask) * pow(cast(real)rank, 3);
        }
        wscore += wrpoints;

        float bscore = 0;
        for (Piece i = Piece.BRABBIT; i <= Piece.BELEPHANT; i++)
        {
            bscore += popcount(pos.bitBoards[i]) * (i - Piece.WELEPHANT);
        }
        bscore *= popcount(pos.bitBoards[Piece.BRABBIT]) + 1;
        float brpoints = 0;
        for (int rank = 1; rank <= 8; rank++)
        {
            ulong rmask = position.RANK_8 >> (8*(rank-1));
            brpoints += popcount(pos.bitBoards[Piece.BRABBIT] & rmask) * pow(cast(real)rank, 3);
        }
        bscore += brpoints;

        // Give a small random component so the bot won't always play the same move
        int score = cast(int)(wscore - bscore) * 10;

        score += rand() % 10;

        if (pos.side == Side.BLACK)
            score = -score;

        return score;
    }
}

struct PositionRecord
{
    ulong position_key;
    int total_seen;
    int gold_wins;
}

class FullSearch : ABSearch
{
    GoalSearch goal_searcher;
    FastFAME fame;

    ulong nodes_quiesced = 0;
    
    real map_e_w = 2;
    real tsafety_w = 1;
    real ontrap_w = 2;
    real frozen_w = 3;
    real rwall_w = 1;
    real ropen_w = 4;
    real rhome_w = 5;
    real rweak_w = 1;
    real rstrong_w = 0.05;
    real pstrength_w = 0.0001;
    real goal_w = 0.3;
    real static_otrap_w = 0.8;
    real static_strap_w = 0.8;
    real blockade_w = 1;
    real hostage_w = 1;
    int max_qdepth = -16;
    int do_qsearch = 1;
    int expand_qdepth = true;

    int qdepth;
    
    this(Logger l)
    {
        super(l);
        goal_searcher = new GoalSearch();
        fame = new FastFAME(0.1716);
    }

    void prepare()
    {
        super.prepare();
        nodes_quiesced = 0;
    }
    
    bool set_option(char[] option, char[] value)
    {
        bool handled = true;
        switch (option)
        {
            case "eval_map_e":
                map_e_w = toReal(value);
                break;
            case "eval_tsafety":
                tsafety_w = toReal(value);
                break;
            case "eval_frozen":
                frozen_w = toReal(value);
                break;
            case "eval_ontrap":
                ontrap_w = toReal(value);
                break;
            case "eval_rwall":
                rwall_w = toReal(value);
                break;
            case "eval_ropen":
                ropen_w = toReal(value);
                break;
            case "eval_rhome":
                rhome_w = toReal(value);
                break;
            case "eval_rweak":
                rweak_w = toReal(value);
                break;
            case "eval_rstrong":
                rstrong_w = toReal(value);
                break;
            case "eval_pstrength":
                pstrength_w = toReal(value) * 0.00001;
                break;
            case "eval_goal":
                goal_w = toReal(value);
                break;
            case "eval_quiesce":
                do_qsearch = toInt(value);
                break;
            case "eval_qdepth":
                max_qdepth = 0 - toInt(value);
                qdepth = max_qdepth;
                break;
            case "expand_qdepth":
                expand_qdepth = cast(bool)toInt(value);
                break;
            case "eval_static_otrap":
                static_otrap_w = toReal(value);
                break;
            case "eval_static_strap":
                static_strap_w = toReal(value);
                break;
            case "eval_blockade":
                blockade_w = toReal(value);
                break;
            case "eval_hostage":
                hostage_w = toReal(value);
                break;
            default:
                handled = super.set_option(option, value);
        }
        return handled;
    }

    void set_depth(int depth)
    {
        super.set_depth(depth);
        if (expand_qdepth)
        {
            depth += 4;
            qdepth = (-(depth/2) * 4) + (depth % 4);
            qdepth = (qdepth > max_qdepth) ? qdepth : max_qdepth;
        }
    }

    int eval(Position pos, int alpha, int beta)
    {
        switch (do_qsearch)
        {
            case 0:
                return static_eval(pos);
            default:
                int score = quiesce(pos, 0, alpha, beta);
                return score;
        }
    }

    int quiesce(Position pos, int depth, int alpha, int beta)
    {
        int score = MIN_SCORE;
        if (pos.is_endstate())
        {
            if (tournament_rules || pos.is_goal())
            {
                // This is actually technically incorrect as it disallows 
                // pushing a rabbit onto then back off of the goal line
                score = pos.endscore() * WIN_SCORE;
                if (pos.side == Side.BLACK)
                {
                    score = -score;
                }
                return score;
            }
        }

        SType sflag = SType.ALPHA;
        TTNode* node = ttable.get(pos);
        Step* prev_best;
        if (node.zobrist == pos.zobrist)
        {
            node.aged = false;
            if (node.depth >= depth)
            {
                if (node.type == SType.EXACT
                    || (node.type == SType.ALPHA && node.score <= alpha)
                    || (node.type == SType.BETA && node.score >= beta))
                {
                    tthits++;
                    return node.score;
                }
            }
            prev_best = &node.beststep;
        }

        if (!pos.inpush)
        {
            score = static_eval(pos);

            debug (eval_bias)
            {
                Position reversed = pos.reverse();
                int rscore = static_eval(reversed);
                if ((score < rscore-2) || (score > rscore+2))
                {
                    writefln("%s\n%s", "wb"[pos.side], pos.to_long_str());
                    writefln("reversed:\n%s\n%s", "wb"[reversed.side], reversed.to_long_str());
                    throw new Exception(format("Biased eval, %d != %d", score, rscore));
                }
                Position.free(reversed);
            }

            if (depth < qdepth)
                return score;

            if (score >= beta)
                return score;
            if (score > alpha)
            {
                alpha = score;
                sflag = SType.EXACT;
            }
        }
        
        StepList steps = StepList.allocate();
        if (!pos.inpush)
        {
            trap_search.find_captures(pos, pos.side);
            for (int six=0; six < trap_search.num_captures; six++)
            {
                if (trap_search.captures[six].length <= pos.stepsLeft)
                {
                    bool duplicate = false;
                    for (int cix=0; cix < steps.numsteps; cix++)
                    {
                        if (trap_search.captures[six].first_step == steps.steps[cix])
                        {
                            duplicate = true;
                            break;
                        }
                    }
                    if (!duplicate)
                    {
                        Step* step = steps.newstep();
                        step.set(trap_search.captures[six].first_step);
                    }
                }
            }
        } else {
            pos.get_steps(steps);
        }
        int best_ix = -1;
        for (int six = 0; six < steps.numsteps; six++)
        {
            nodes_searched++;
            nodes_quiesced++;
            int cal;
            Position npos = pos.dup;
            npos.do_step(steps.steps[six]);

            if (npos == nullmove)
            {
                cal = -(WIN_SCORE+1);   // Make this worse than a normal
                                        // loss since it's actually an illegal move
            } else if (npos.stepsLeft == 4)
            {
                Position mynull = nullmove;
                nullmove = npos.dup;
                nullmove.do_step(NULL_STEP);

                cal = -quiesce(npos, depth-1, -beta, -alpha);

                Position.free(nullmove);
                nullmove = mynull;
            } else {
                cal = quiesce(npos, depth-1, alpha, beta);
            }

            Position.free(npos);

            if (cal > score)
            {
                score = cal;
                best_ix = six;

                if (cal > alpha)
                {
                    alpha = cal;
                    sflag = SType.EXACT;

                    if (cal >= beta)
                    {
                        sflag = SType.BETA;
                        break;
                    }
                }
            }
        }

        Step bstep;
        if (best_ix != -1)
        {
           bstep = steps.steps[best_ix];
        } else {
            bstep.clear();
        }
        node.set(pos, depth, score, sflag, bstep);
        StepList.free(steps);

        return score;
    }

    int static_trap_eval(Position pos, Side side, int pop, int fscore)
    {
        int score = 0;
        if (trap_search.find_captures(pos, side))
        {
            int[3] valuable_vid;
            Piece[3] valuable_victim;
            int[3] valuable_length;
            ulong[3] valuable_traps;
            for (int i=0; i < trap_search.num_captures; i++)
            {
                /*
                int tid;
                version (trap_switch)
                {
                    switch (trap_search.captures[i].trap_bit)
                    {
                        case TRAP_F3:
                            tid = 0;
                            break;
                        case TRAP_C3:
                            tid = 1;
                            break;
                        case TRAP_F6:
                            tid = 2;
                            break;
                        case TRAP_C6:
                            tid = 3;
                            break;
                        default:
                            throw new Exception(format("trap_bit not a trap %X", trap_search.captures[i].trap_bit));
                    }
                } else
                {
                    ulong trap_bit = trap_search.captures[i].trap_bit;
                    if (trap_bit == TRAP_F3)
                        tid = 0;
                    else if (trap_bit == TRAP_C3)
                        tid = 1;
                    else if (trap_bit == TRAP_F6)
                        tid = 2;
                    else if (trap_bit == TRAP_C6)
                        tid = 3;
                    else
                        throw new Exception(format("trap_bit not a trap %X", trap_search.captures[i].trap_bit));
                }
                */

                int vid = bitindex(trap_search.captures[i].victim_bit); // | (tid << 8);
                ulong tbit = trap_search.captures[i].trap_bit;
                Piece vic = trap_search.captures[i].victim;
                int len = trap_search.captures[i].length;
                for (int v=0; v < valuable_vid.length; v++)
                {
                    if (vid != valuable_vid[v]
                            && (vic > valuable_victim[v]
                                || (vic == valuable_victim[v]
                                    && len < valuable_length[v])))
                    {
                        int tvid = valuable_vid[v];
                        Piece tvic = valuable_victim[v];
                        int tlen = valuable_length[v];
                        ulong ttbits = valuable_traps[v];
                        valuable_vid[v] = vid;
                        valuable_victim[v] = vic;
                        valuable_length[v] = len;
                        valuable_traps[v] = tbit;
                        vid = tvid;
                        vic = tvic;
                        tbit = ttbits;
                        len = tlen;
                    } else if (vid == valuable_vid[v])
                    {
                        if (valuable_length[v] > len)
                        {
                            valuable_length[v] = len;
                        }
                        valuable_traps[v] |= tbit;
                        break;
                    }
                }
            }

            if (valuable_victim[0] == valuable_victim[1]
                    && valuable_length[0] > valuable_length[1])
            {
                int l = valuable_length[0];
                valuable_length[0] = valuable_length[1];
                valuable_length[1] = l;
            }
            if (valuable_victim[1] == valuable_victim[2]
                    && valuable_length[1] > valuable_length[2])
            {
                int l = valuable_length[1];
                valuable_length[1] = valuable_length[2];
                valuable_length[2] = l;
            }

            int attacksteps = 0;
            if (side == pos.side)
                attacksteps = pos.stepsLeft;

            int[3] valuable_value;
            for (int i=0; i < valuable_victim.length; i++)
            {
                if (valuable_victim[i] != 0)
                {
                    int vcnt = pop2count(pop, valuable_victim[i]) - 1;
                    int vpop = pop & ~(pop_mask[valuable_victim[i]] << pop_offset[valuable_victim[i]]);
                    vpop |= vcnt << pop_offset[valuable_victim[i]];
                    valuable_value[i] = fscore - fame.score(vpop);
                    if (attacksteps)
                    {
                        if (valuable_length[i] <= attacksteps)
                        {
                            attacksteps -= valuable_length[i];
                            valuable_length[i] = 0;
                        } else {
                            valuable_length[i] -= attacksteps;
                            attacksteps = 0;
                        }
                    }
                    valuable_length[i] = (valuable_length[i] < 12) ? valuable_length[i] : 12;
                }
            }

            const static real[] victim_per = [0.5, 0.6, 0.7];
            const static real[] trap_num = [0, 1.0, 1.5, 1.5, 1.5];
            const static real[] length_per = [1.0,
                1.0, 1.0, 0.9, 0.9,
                0.6, 0.5, 0.4, 0.3,
                0.1, 0.1, 0.05, 0.05];
            const static real[] defense_per = [1.0, 0.80, 0.66, 0.50, 0.33];
            const static real max_victim_per = 0.9;
            real defense_mul = (side != pos.side) ? defense_per[pos.stepsLeft] : defense_per[4];
            for (int i=0; i < 3; i++)
            {
                if (valuable_victim[i] != 0)
                {
                    real val = valuable_value[i] * length_per[valuable_length[i]];
                    if (valuable_length[i])
                        val *= defense_mul * victim_per[i] * trap_num[popcount(valuable_traps[i])];
                    else
                        val *= max_victim_per;
                        
                    score -= val;
                }
            }

            debug (eval_trap)
            {
                writefln("trap:\n%s\n%s", "wb"[pos.side^1], pos.to_long_str());
                writefln("lf %d, lp %d, ip %d", pos.lastfrom, pos.lastpiece, pos.inpush);
                writefln("score %d, num %d", score, trap_search.num_captures);
                writefln("mvv %d, svv %d, tvv %d", valuable_victim[0], valuable_victim[1], valuable_victim[2]);
                writefln("mvl %d, svl %d, tvl %d", valuable_length[0], valuable_length[1], valuable_length[2]);
                for (int i=0; i < trap_search.num_captures; i++)
                {
                    writefln("v %d, l %d, t %X", trap_search.captures[i].victim, trap_search.captures[i].length,
                            trap_search.captures[i].trap_bit);
                }
            }
        } else {
            debug (eval_trap)
            {
                writefln("no trap:\n%s\n%s", "wb"[pos.side^1], pos.to_long_str());
                writefln("lf %d, lp %d, ip %d", pos.lastfrom, pos.lastpiece, pos.inpush);
                writefln("score %d", score);
            }
        }

        return score;
    }

    int goal_threat(Position pos)
    {
        // this.goal_searcher must already be setup for the position passed in

        const int[18] GOAL_THREAT = [10000, 10000, 10000, 8000, 6000,
              1000, 1000, 800, 600,
              100, 100, 80, 60,
              10, 10, 8, 6, 0];
        const real[] DEFENSE_PER = [1.0, 0.8, 0.66, 0.5, 0.33];
        int score = 0;
        if (goal_searcher.goals_found[pos.side])
        {
            int extrasteps = goal_searcher.goal_depth[pos.side][0] - pos.stepsLeft;
            extrasteps = (extrasteps < 17) ? extrasteps : 17;
            score += GOAL_THREAT[extrasteps] * DEFENSE_PER[4] * goal_w;
        }
        if (goal_searcher.goals_found[pos.side^1])
        {
            int togoal = goal_searcher.goal_depth[pos.side^1][0];
            togoal = (togoal < 17) ? togoal : 17;
            score -= GOAL_THREAT[togoal] * DEFENSE_PER[pos.stepsLeft] * goal_w;
        }

        return score;
    }

    int static_eval(Position pos)
    {
        goal_searcher.set_start(pos);
        goal_searcher.find_goals(16);
        if (goal_searcher.goals_found[pos.side]
                && goal_searcher.goal_depth[pos.side][0] <= pos.stepsLeft)
        {
            return WIN_SCORE - goal_searcher.goal_depth[pos.side][0];
        }

        int pop = population(pos);
        int fscore = fame.score(pop); // first pawn worth ~196
                                     // only a pawn left ~31883
        int score = fscore;
        score += static_trap_eval(pos, cast(Side)(pos.side^1), pop, fscore) * static_otrap_w;
        score += static_trap_eval(pos, pos.side, pop, fscore) * static_strap_w;

        int[64] pstrengths;
        score += piece_strength(pos, pstrengths) * pstrength_w;
        score += mobility(pos, pstrengths, blockade_w, hostage_w);
        score += rabbit_strength(pos, goal_searcher, rweak_w, rstrong_w);
        score += rabbit_wall(pos) * rwall_w;
        score += rabbit_open(pos) * ropen_w;
        score += rabbit_home(pos) * rhome_w;
        score += frozen_pieces(pos) * frozen_w;
        score += map_elephant(pos) * map_e_w;
        score += trap_safety(pos) * tsafety_w;
        score += on_trap(pos) * ontrap_w;

        if (pos.side == Side.BLACK)
            score = -score;

        score += goal_threat(pos);

        // clamp the evaluation to be less than a win
        score = (score < WIN_SCORE-10) ? ((score > -(WIN_SCORE-10)) ? score : -(WIN_SCORE-10)) : WIN_SCORE-10;
        return score;
    }

    int logged_eval(Position pos)
    {
        goal_searcher.set_start(pos);
        goal_searcher.find_goals(16);
        if (goal_searcher.goals_found[pos.side]
                && goal_searcher.goal_depth[pos.side][0] <= pos.stepsLeft)
        {
            logger.log("Found goal in %d steps", goal_searcher.goal_depth[pos.side][0]);
            return WIN_SCORE - goal_searcher.goal_depth[pos.side][0];
        }

        int pop = population(pos);
        int fscore = fame.score(pop); // first pawn worth ~196
                                     // only a pawn left ~31883
        logger.log("Fame %d", fscore);
        int score = fscore;
        int pscore = fscore;
        score += static_trap_eval(pos, cast(Side)(pos.side^1), pop, fscore) * static_otrap_w;
        logger.log("static otrap %d", score-pscore);
        pscore = score;
        score += static_trap_eval(pos, pos.side, pop, fscore) * static_strap_w;
        logger.log("static strap %d", score-pscore);
        pscore = score;

        int[64] pstrengths;
        score += piece_strength(pos, pstrengths) * pstrength_w;
        logger.log("piece strength %d", score-pscore);
        pscore = score;
        score += mobility(pos, pstrengths, blockade_w, hostage_w);
        logger.log("mobility %d", score-pscore);
        pscore = score;
        score += rabbit_strength(pos, goal_searcher, rweak_w, rstrong_w);
        logger.log("rabbit strength %d", score-pscore);
        pscore = score;
        score += rabbit_wall(pos) * rwall_w;
        logger.log("rabbit wall %d", score-pscore);
        pscore = score;
        score += rabbit_open(pos) * ropen_w;
        logger.log("rabbit open %d", score-pscore);
        pscore = score;
        score += rabbit_home(pos) * rhome_w;
        logger.log("rabbit home %d", score-pscore);
        pscore = score;
        score += frozen_pieces(pos) * frozen_w;
        logger.log("frozen pieces %d", score-pscore);
        pscore = score;
        score += map_elephant(pos) * map_e_w;
        logger.log("map elephant %d", score-pscore);
        pscore = score;
        score += trap_safety(pos) * tsafety_w;
        logger.log("trap safety %d", score-pscore);
        pscore = score;
        score += on_trap(pos) * ontrap_w;
        logger.log("on trap %d", score-pscore);

        if (pos.side == Side.BLACK)
            score = -score;

        pscore = score;
        score += goal_threat(pos);
        logger.log("goal threat (side to move) %d", score-pscore);
        pscore = score;

        // clamp the evaluation to be less than a win
        score = (score < WIN_SCORE-10) ? ((score > -(WIN_SCORE-10)) ? score : -(WIN_SCORE-10)) : WIN_SCORE-10;
        logger.log("Final (clamped) score %d", score);
        return score;
    }
}

class PositionNode
{
    private static PositionNode cache_head;
    static int allocated;
    static int reserved;

    PositionNode prev;
    PositionNode next;

    Position pos;
    StepList move;
    int last_score;

    this()
    {
        allocated++;
    }

    static PositionNode allocate()
    {
        if (cache_head !is null)
        {
            PositionNode n = cache_head;
            cache_head = n.next;
            n.next = null;
            reserved--;
            return n;
        }

        return new PositionNode();
    }

    static void free(PositionNode n)
    {
        n.pos = null;
        n.prev = null;
        n.next = cache_head;
        cache_head = n;
        reserved++;
    }
}

class Engine : AEIEngine
{
    ABSearch searcher;
    PositionNode pos_list;
    PositionNode loss_list;
    PositionNode next_pos;
    int num_moves;
    int checked_moves;
    int num_best;

    int depth;
    int best_score;

    bool in_step;
    int last_score;
    PositionNode last_best;

    int max_depth;

    const static int BOOK_SIZE = 1000000;
    PositionRecord[] opening_book;
    bool position_record = false;

    const static uint MAX_ABORT_REPORTS = 4;
    uint aborts_reported = 0;

    bool root_lmr = true;
    int last_search_margin = 350; // between a cat and a dog

    this(Logger l)
    {
        super(l);
        searcher = new FullSearch(l);
        //searcher = new ScoreSearch();
        in_step = false;
        max_depth = -1;
    }

    bool set_option(char[] option, char[] value)
    {
        bool handled = true;
        switch (option)
        {
            case "opening_book":
                position_record = cast(bool)toInt(value);
                if (position_record)
                {
                    if (opening_book.length == 0)
                        opening_book.length = BOOK_SIZE;
                }
                break;
            case "root_lmr":
                root_lmr = cast(bool)toInt(value);
                break;
            case "reduce_search_margin":
                last_search_margin = toInt(value);
                break;
            default:
                handled = searcher.set_option(option, value);
        }
        return handled;
    }

    void new_game()
    {
        if (position_record && past.length > 3)
        {
            int record_length = (past.length < 60) ? past.length : 60;
            for (int i=3; i < record_length; i++)
            {
                int key = past[i].zobrist % opening_book.length;
                if (opening_book[key].position_key != past[i].zobrist)
                {
                    opening_book[key].position_key = past[i].zobrist;
                    opening_book[key].total_seen = 0;
                    opening_book[key].gold_wins = 0;
                }
                opening_book[key].total_seen++;
                if (position.side == Side.WHITE)
                    opening_book[key].gold_wins++;
            }
        }
        super.new_game();
    }

    void start_search()
    {
        if (ply == 1) // white setup move
        {
            bestmove = "Ra1 Rb1 Rc1 Rd1 Re1 Rf1 Rg1 Rh1 Da2 Hb2 Cc2 Md2 Ee2 Cf2 Hg2 Dh2";
            state = EngineState.MOVESET;
        } else if (ply == 2)
        {
            if (position.pieces[11] == Piece.WELEPHANT)
            {
                bestmove = "ra8 rb8 rc8 rd8 re8 rf8 rg8 rh8 da7 hb7 cc7 ed7 me7 cf7 hg7 dh7";
            } else {
                bestmove = "ra8 rb8 rc8 rd8 re8 rf8 rg8 rh8 da7 hb7 cc7 md7 ee7 cf7 hg7 dh7";
            }
            state = EngineState.MOVESET;
        } else {
            PosStore pstore = position.get_moves();
            PositionNode last_pos;
            PositionNode repeated;
            int[ulong] repetitions;
            for (int i=0; i < past.length; i++)
            {
                repetitions[past[i].zobrist] += 1;
            }
            foreach (Position pos; pstore)
            {
                PositionNode n = PositionNode.allocate();
                n.pos = pos;
                n.move = pstore.getpos(pos);
                n.last_score = MAX_SCORE;

                if ((pos.zobrist in repetitions) && (repetitions[pos.zobrist] > 1))
                {
                    if (repeated !is null)
                    {
                        Position.free(repeated.pos);
                        StepList.free(repeated.move);
                        PositionNode.free(repeated);
                    }
                    repeated = n;
                    continue;
                }

                num_moves++;

                n.prev = last_pos;
                if (last_pos !is null)
                {
                    last_pos.next = n;
                } else {
                    pos_list = n;
                }
                last_pos = n;
            }
            delete pstore;

            if (pos_list is null)
            {
                // only repetition moves available
                pos_list = repeated;
                num_moves = 1;
            }
            next_pos = pos_list;
            best_score = MIN_SCORE;
            depth = 0;
            checked_moves = 0;
            num_best = 0;
            searcher.set_depth(4);
            searcher.prepare();
            state = EngineState.SEARCHING;
        }
    }

    void search(int check_nodes)
    {
        in_step = true;
        d_time start_time = getUTCtime();
        searcher.check_interval = check_nodes;
        int stop_nodes = searcher.nodes_searched + check_nodes;
        while (searcher.nodes_searched < stop_nodes)
        {
            Position pos = next_pos.pos;
            searcher.nullmove = pos.dup;
            searcher.nullmove.do_step(NULL_STEP);
            int score;
            if (root_lmr && depth > 2
                    && checked_moves > num_best)
            {
                int firstdepth = depth - 1;
                if ((firstdepth > 2) && (next_pos.move.numsteps < 4))
                    firstdepth--;
                if ((firstdepth > 3) && (next_pos.move.steps[next_pos.move.numsteps-1] == NULL_STEP))
                    firstdepth--;
                if ((firstdepth > 3) && (next_pos.last_score < (best_score - last_search_margin)))
                    firstdepth--;
                score = -searcher.alphabeta(pos, firstdepth, -(best_score+1), -best_score);
            } else {
                score = best_score +1;
            }

            if (score > best_score && score != -ABORT_SCORE)
            {
                score = -searcher.alphabeta(pos, depth, MIN_SCORE, -best_score);
            }
            next_pos.last_score = score;
            Position.free(searcher.nullmove);
            searcher.nodes_searched++;
            checked_moves++;

            if (score == ABORT_SCORE
                    || score == -ABORT_SCORE)
            {
                d_time now = getUTCtime();
                if (aborts_reported < MAX_ABORT_REPORTS)
                {
                    logger.log("Aborted long search after %d seconds.", (now - start_time) / TicksPerSecond);
                    aborts_reported += 1;
                }
                break;
            }

            if (position_record)
            {
                int key = pos.zobrist % opening_book.length;
                if (opening_book[key].position_key == pos.zobrist
                        && opening_book[key].total_seen)
                {
                    int val = (opening_book[key].gold_wins - 
                            (opening_book[key].total_seen - opening_book[key].gold_wins)) * 10;
                    if (pos.side == Side.BLACK)
                        val = -val;
                    score += val;
                    logger.console("Saw position in book added %d to %d score.", val, score);
                }
            }

            if (score == -WIN_SCORE
                    && next_pos !is pos_list)
            {
                PositionNode n = next_pos;

                if (next_pos.next !is null)
                    next_pos.next.prev = next_pos.prev;

                next_pos.prev.next = next_pos.next;
                next_pos = next_pos.prev;

                n.prev = null;
                n.next = loss_list;
                if (loss_list !is null)
                    loss_list.prev = n;
                loss_list = n;
            }

            if (score > best_score)
            {
                best_score = score;
                
                if (next_pos !is pos_list)
                {
                    PositionNode n = next_pos;
                    next_pos = n.prev;

                    if (n.next !is null)
                        n.next.prev = n.prev;
                    n.prev.next = n.next;
                    n.next = pos_list;
                    n.prev = null;
                    pos_list.prev = n;
                    pos_list = n;
                }

                if (score >= WIN_SCORE)
                {
                    break;
                }

                if (checked_moves > num_best)
                {
                    num_best++;
                }
            }

            if (next_pos.next is null)
            {
                depth++;
                checked_moves = 0;
                searcher.set_depth(depth);
                last_score = best_score;
                last_best = pos_list;
                best_score = MIN_SCORE;
                next_pos = pos_list;
                in_step = false;
                break;
            }

            next_pos = next_pos.next;
        }
    }

    void set_bestmove()
    {
        bestmove = pos_list.move.to_move_str(position);
    }

    StepList get_bestline()
    {
        StepList bestline = pos_list.move.dup;
        Position pos = pos_list.pos.dup;
        TTNode* n = searcher.ttable.get(pos);
        for (int pvdepth = 0; pvdepth < depth * 2; pvdepth++)
        {
            if (n.zobrist != pos.zobrist 
                || (n.beststep.frombit == 0 && n.beststep.tobit == 0))
            {
                break;
            }
            Step* next_step = bestline.newstep();
            next_step.copy(n.beststep);
            pos.do_step(n.beststep);
            n = searcher.ttable.get(pos);
        }

        Position.free(pos);
        return bestline;
    }

    void cleanup_search()
    {
        while (pos_list !is null)
        {
            Position.free(pos_list.pos);
            StepList.free(pos_list.move);
            PositionNode n = pos_list;
            pos_list = n.next;
            PositionNode.free(n);
        }
        while (loss_list !is null)
        {
            Position.free(loss_list.pos);
            StepList.free(loss_list.move);
            PositionNode n = loss_list;
            loss_list = n.next;
            PositionNode.free(n);
        }
        next_pos = null;
        pos_list = null;
        last_best = null;
        num_moves = 0;
        last_score = MIN_SCORE;
        best_score = MIN_SCORE;
        aborts_reported = 0;
        searcher.cleanup();
    }

}

int main(char[][] args)
{
    char[] ip = "127.0.0.1";
    ushort port = 40007;

    if (args.length > 1)
        ip = args[1].dup;
    if (args.length > 2)
        port = toUshort(args[2]);

    d_time report_interval = 60 * std.date.TicksPerSecond;
    d_time nextreport = 0;
    int report_depth = 0;

    Logger logger = new Logger();
    ServerInterface server;
    try
    {
        server = new ServerInterface(new SocketServer(ip, port),
            BOT_NAME, BOT_AUTHOR);
    } catch (ConnectException e)
    {
        writefln("Error connecting to server: %s", e.msg);
        return 1;
    }
    logger.register(server);
    Engine engine = new Engine(logger);

    int tc_permove = 0;         // time given per move
    int tc_maxreserve = 0;      // maximum reserve size
    int tc_maxmove = 0;         // maximum time for a single move
    int tc_wreserve = 0;        // white's reserve time
    int tc_breserve = 0;        // black's reserve time
    int tc_lastmove = 0;        // time used by opponent for last move
    int tc_safety_margin = 10;  // safety margin in seconds to end the search
    real tc_min_search_per = 0.66;  // minimum percentage of permove time to search
    real tc_confidence_denom = 3;
    real tc_time_left_denom = 3;
    
    d_time search_time = 0;
    d_time search_max = 0;
    int search_num = 0;
    d_time search_start;
    d_time move_start;

    int tc_min_search;
    int tc_max_search;
    d_time last_decision_change;

    bool pondering = false;

    int check_num = 0;
    while (true)
    {
        try
        {
            if (engine.state == EngineState.IDLE)
            {
                server.check(10);
            } else {
                server.check();
            }
        } catch (UnknownCommand e)
        {
            logger.warn("Received unknown command: %s", e.command);
        }

        while (server.current_cmd !is null)
        {
            switch (server.current_cmd.type)
            {
                case ServerCmd.CmdType.ISREADY:
                    server.readyok();
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.QUIT:
                    logger.log("Exiting by server command.");
                    return 0;
                case ServerCmd.CmdType.NEWGAME:
                    logger.log("Starting new game.");
                    if (engine.state != EngineState.IDLE)
                    {
                        engine.cleanup_search();
                        engine.state = EngineState.IDLE;
                    }
                    engine.new_game();
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.GO:
                    GoCmd gcmd = cast(GoCmd)server.current_cmd;
                    if (engine.state != EngineState.IDLE)
                    {
                        engine.cleanup_search();
                        engine.state = EngineState.IDLE;
                    }
                    logger.log("Starting search");
                    logger.console("%s\n%s", "wb"[engine.position.side], engine.position.to_long_str);
                    search_start = getUTCtime();
                    engine.start_search();
                    last_decision_change = search_start;
                    nextreport = getUTCtime() + report_interval;
                    report_depth = 0;
                    if (gcmd.option == GoCmd.Option.PONDER)
                    {
                        pondering = true;
                    } else {
                        pondering = false;
                    }
                    if (tc_permove)
                    {
                        Side myside = engine.position.side;
                        int myreserve = (myside == Side.WHITE) ? tc_wreserve : tc_breserve;
                        int maxuse = (tc_maxreserve > tc_maxmove - tc_permove) ? tc_maxreserve : tc_maxmove - tc_permove;
                        real reserve_fill = cast(real)myreserve / maxuse;
                        tc_min_search = cast(int)(tc_permove * tc_min_search_per);
                        tc_min_search += cast(int)((tc_permove * (1-tc_min_search_per)) * reserve_fill);
                        
                        tc_max_search = tc_permove + myreserve;
                        if (tc_maxmove && (tc_max_search > tc_maxmove))
                        {
                            tc_max_search = tc_maxmove;
                        }
                        tc_max_search -= tc_safety_margin;
                        logger.log("Min search: %d Max: %d", tc_min_search, tc_max_search);
                    } else {
                        tc_min_search = 0;
                        tc_max_search = 0;
                    }
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.STOP:
                    if (engine.state == EngineState.SEARCHING)
                    {
                        engine.set_bestmove();
                        engine.state = EngineState.MOVESET;
                    }
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.MAKEMOVE:
                    MoveCmd mcmd = cast(MoveCmd)server.current_cmd;
                    if (engine.state != EngineState.IDLE)
                    {
                        engine.cleanup_search();
                        engine.state = EngineState.IDLE;
                    }
                    engine.make_move(mcmd.move);
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.SETPOSITION:
                    PositionCmd pcmd = cast(PositionCmd)server.current_cmd;
                    engine.set_position(pcmd.side, pcmd.pos_str);
                    logger.console("set position\n%s\n%s", 
                            "wb"[engine.position.side], 
                            engine.position.to_long_str());
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.CHECKEVAL:
                    CheckCmd chkcmd = cast(CheckCmd)server.current_cmd;
                    Position pos = parse_short_str(chkcmd.side, 4, chkcmd.pos_str);
                    server.clear_cmd();
                    engine.searcher.logged_eval(pos);
                    Position.free(pos);
                    break;
                case ServerCmd.CmdType.SETOPTION:
                    OptionCmd scmd = cast(OptionCmd)server.current_cmd;
                    switch (scmd.name)
                    {
                        case "depth":
                            if (scmd.value == "infinite")
                            {
                                engine.max_depth = -1;
                                logger.log("Search depth set to infinite");
                            } else {
                                int depth = toInt(scmd.value);
                                engine.max_depth = (depth > 3) ? depth - 4 : 0;
                                logger.log("Search depth set to %d", engine.max_depth+4);
                            }
                            break;
                        case "tcmove":
                            tc_permove = toInt(scmd.value);
                            break;
                        case "tcmax":
                            tc_maxreserve = toInt(scmd.value);
                            break;
                        case "tcturntime":
                            tc_maxmove = toInt(scmd.value);
                            break;
                        case "wreserve":
                            tc_wreserve = toInt(scmd.value);
                            break;
                        case "breserve":
                            tc_breserve = toInt(scmd.value);
                            break;
                        case "tclastmoveused":
                            tc_lastmove = toInt(scmd.value);
                            break;
                        case "tcmoveused":
                            move_start = getUTCtime() - (cast(d_time)(toInt(scmd.value)) * TicksPerSecond);
                            break;
                        case "log_console":
                            logger.to_console = cast(bool)toInt(scmd.value);
                            break;
                        default:
                            engine.set_option(scmd.name, scmd.value);
                            break;
                    }
                    server.clear_cmd();
                    break;
                default:
                    throw new Exception("Unhandled server command in main loop.");
            }
        }

        d_time length = getUTCtime() - search_start;
        switch (engine.state)
        {
            case EngineState.MOVESET:
                if (length > search_max)
                {
                    search_max = length;
                }
                real seconds = cast(real)length/TicksPerSecond;
                if (engine.ply > 2)
                {
                    search_time += length;
                    search_num += 1;
                    if (engine.best_score >= WIN_SCORE)
                    {
                        logger.log("Sending forced win move in %.2f seconds.", seconds);
                    } else if (engine.pos_list.next is null)
                    {
                        logger.log("Sending forced move, or in forced loss, after %.2f seconds.", seconds);
                    }
                }
                real average = 0;
                if (search_num)
                {
                    average = (cast(real)search_time / TicksPerSecond) / search_num;
                }
                real max_seconds = cast(real)search_max / TicksPerSecond;
                logger.log("Searched %d nodes, %.0f nps, %d tthits.",
                        engine.searcher.nodes_searched, engine.searcher.nodes_searched/seconds, engine.searcher.tthits);
                logger.log("Finished search in %.2f seconds, average %.2f, max %.2f.", seconds, average, max_seconds);
                logger.console("Sending move %s", engine.bestmove);
                if (!pondering)
                {
                    server.bestmove(engine.bestmove);
                }
                engine.cleanup_search();
                logger.log("Positions allocated %d, in reserve %d (%.0fMB).",
                        Position.allocated, Position.reserved, Position.reserve_size);
                logger.log("PNodes allocated %d, in reserve %d.", PositionNode.allocated, PositionNode.reserved);
                engine.state = EngineState.IDLE;
                break;
            case EngineState.SEARCHING:
                d_time start_run = getUTCtime();
                PositionNode cur_best = engine.pos_list;
                int check_nodes;
                if (engine.searcher.nodes_searched && (length > (TicksPerSecond * 2)))
                {
                    check_nodes = engine.searcher.nodes_searched / (length / TicksPerSecond);
                } else {
                    check_nodes = START_SEARCH_NODES;
                }
                if (tc_max_search)
                {
                    d_time abort_time = ((tc_min_search + 20) * TicksPerSecond) + move_start;
                    d_time max_time_limit = (tc_max_search * TicksPerSecond) + move_start;
                    if (pondering)
                    {
                        abort_time = (20 * TicksPerSecond) + start_run;
                    }
                    if (abort_time > max_time_limit)
                        abort_time = max_time_limit;
                    engine.searcher.abort_time = abort_time;
                }
                engine.search(check_nodes);
                check_num += 1;
                d_time now = getUTCtime();
                if (cur_best != engine.pos_list)
                {
                    last_decision_change = now;
                }
                if (!pondering)
                {
                    if (((engine.max_depth != -1) && (engine.depth > engine.max_depth))
                        || (engine.best_score >= WIN_SCORE)
                        || (engine.pos_list.next is null)
                        || (tc_permove && (now >= ((tc_max_search * TicksPerSecond) + move_start))))
                    {
                        engine.set_bestmove();
                        engine.state = EngineState.MOVESET;
                    } else if (tc_permove && (now > ((tc_min_search * TicksPerSecond) + move_start)))
                    {
                        logger.log("Min search time reached");
                        d_time decision_length = now - last_decision_change;
                        d_time move_length = now - move_start;
                        d_time time_left = (move_start + (tc_max_search * TicksPerSecond)) - now;
                        if (decision_length < move_length * (1.0/tc_confidence_denom)
                                && decision_length < time_left * (1.0/tc_time_left_denom))
                        {
                            logger.log("move_length %d, decision_length %d, time_left %d", 
                                        (move_length / TicksPerSecond),
                                        (decision_length / TicksPerSecond),
                                        (time_left / TicksPerSecond));
                            real tc_cd = 1.0 / (tc_confidence_denom-1);
                            real tc_tld = 1.0 / (tc_time_left_denom-1);
                            d_time length_cutoff = cast(d_time)((last_decision_change - move_start) * tc_cd) + last_decision_change;
                            d_time reserve_cutoff = cast(d_time)(((move_start + (tc_max_search * TicksPerSecond))
                                        - last_decision_change) * tc_tld) + last_decision_change;
                            d_time end_search = (length_cutoff < reserve_cutoff) ? length_cutoff : reserve_cutoff;
                            end_search += cast(d_time)(0.1 * TicksPerSecond);
                            tc_min_search = (end_search - move_start) / TicksPerSecond;
                            logger.log("next min_search set to %d", tc_min_search);
                        } else {
                            logger.log("last decision change %d seconds ago", decision_length / TicksPerSecond);
                            engine.set_bestmove();
                            engine.state = EngineState.MOVESET;
                        }
                    }
                    if (now > nextreport 
                            || engine.depth > report_depth 
                            || cur_best !is engine.pos_list)
                    {
                        if (engine.in_step)
                        {
                            logger.info("depth %d+", engine.depth+3);
                        } else {
                            logger.info("depth %d", engine.depth+3);
                        }
                        logger.info("time %d", (now-search_start)/TicksPerSecond);
                        logger.info("nodes %d", engine.searcher.nodes_searched);
                        if (engine.in_step)
                        {
                            logger.info("score cr %d", cast(int)(engine.best_score / 1.96));
                        } else {
                            logger.info("score cr %d", cast(int)(engine.last_score / 1.96));
                        }
                        StepList bestline = engine.get_bestline();
                        logger.info("pv %s", bestline.to_move_str(engine.position));
                        StepList.free(bestline);
                        check_num = 0;
                        nextreport = now + report_interval;
                        report_depth = engine.depth;
                    }
                }
                break;
            default:
                break;
        }
    }
}


