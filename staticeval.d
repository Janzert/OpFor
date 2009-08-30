
import std.conv;
import std.stdio;

import alphabeta;
import goalsearch;
import logging;
import movement;
import position;
import trapmoves;

struct SCNode
{
    ulong zobrist;
    int score;
}

class ScoreCache
{
    SCNode[] cache;

    this(int size)
    {
        cache.length = size;
    }

    void set_size(int size)
    {
        cache.length = size;
    }

    SCNode* get(Position pos)
    {
        return &cache[pos.zobrist % cache.length];
    }
}

class StaticEval
{
    Logger logger;

    Position pos;
    FastFAME fame;
    GoalSearchDT goals;
    TrapGenerator trap_search;

    ulong[2] safe_traps;
    ulong[2] active_traps;
    int[64] pstrengths;
    ulong hostages;
    ulong frames;
    ulong weakframers;

    ScoreCache sc_cache;

    real map_e_w = 2;
    real tsafety_w = 4;
    real ontrap_w = 2;
    real frozen_w = 3;
    real rwall_w = 1;
    real ropen_w = 2;
    real rhome_w = 5;
    real rweak_w = 1;
    real rstrong_w = 0.04;
    real pstrength_w = 0.0001;
    real goal_w = 1;
    real static_otrap_w = 0.8;
    real static_strap_w = 0.6;
    real blockade_w = 1;
    real hostage_w = 1;
    real mobility_w = 1;

    this(Logger l, GoalSearchDT g, TrapGenerator t)
    {
        logger = l;
        goals = g;
        trap_search = t;
        fame = new FastFAME(0.1716);
        sc_cache= new ScoreCache(200000);
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
            case "eval_mobility":
                mobility_w = toReal(value);
                break;
            case "eval_cache_size":
                sc_cache.set_size(toInt(value));
                break;
            default:
                handled = false;
        }
        return handled;
    }

    int trap_safety()
    {
        static const int[] BOTH_SAFE = [-1, 1];
        static const int[] WHITE_SAFE = [2, 10];
        static const int[] BLACK_SAFE = [-10, -2];

        int score = 0;

        safe_traps[Side.WHITE] = 0;
        safe_traps[Side.BLACK] = 0;
        ulong traps = TRAPS;
        while (traps)
        {
            ulong trap = traps & -traps;
            traps ^= trap;
            bitix tix = bitindex(trap);
            Side tside = (trap > TRAP_C3) ? Side.BLACK : Side.WHITE;

            ulong neighbors = neighbors_of(trap);
            int[2] n_pop;
            n_pop[Side.WHITE] = popcount(neighbors & pos.placement[Side.WHITE]);
            n_pop[Side.BLACK] = popcount(neighbors & pos.placement[Side.BLACK]);
            Piece[2] strongest_near;
            strongest_near[Side.WHITE] = pos.strongest[Side.WHITE][tix];
            strongest_near[Side.BLACK] = pos.strongest[Side.BLACK][tix];
            while (neighbors)
            {
                ulong nbit = neighbors & -neighbors;
                neighbors ^= nbit;
                bitix nix = bitindex(nbit);
                if (pos.strongest[Side.WHITE][nix] > strongest_near[Side.WHITE])
                    strongest_near[Side.WHITE] = pos.strongest[Side.WHITE][nix];
                if (pos.strongest[Side.BLACK][nix] > strongest_near[Side.BLACK])
                    strongest_near[Side.BLACK] = pos.strongest[Side.BLACK][nix];
            }
            int trap_safe = 0;
            if (!(active_traps[Side.BLACK] & trap)
                    && pos.strongest[Side.WHITE][tix] != Piece.EMPTY
                    && (pos.strongest[Side.WHITE][tix] + 6 >= strongest_near[Side.BLACK]
                        || n_pop[Side.WHITE] > 1))
                trap_safe |= 1;
            if (!(active_traps[Side.WHITE] & trap)
                    && pos.strongest[Side.BLACK][tix] != Piece.EMPTY
                    && (pos.strongest[Side.BLACK][tix] - 6 >= strongest_near[Side.WHITE]
                        || n_pop[Side.BLACK] > 1))
                trap_safe |= 2;
            switch (trap_safe)
            {
                case 0:
                    break;
                case 1:
                    score += WHITE_SAFE[tside];
                    safe_traps[Side.WHITE] |= trap;
                    break;
                case 2:
                    score += BLACK_SAFE[tside];
                    safe_traps[Side.BLACK] |= trap;
                    break;
                case 3:
                    score += BOTH_SAFE[tside];
                    safe_traps[Side.WHITE] |= trap;
                    safe_traps[Side.BLACK] |= trap;
                    break;
            }
        }
        return score;
    }

    // penalty for piece on trap, pinned or framed
    int on_trap()
    {
        const int ON_TRAP[13] = [0, -6, -9, -12, -18, -33, -88, 6, 9, 12, 18, 33, 88];
        const int FRAMED[13] = [0, -50, -75, -100, -175, -225, -400,
              50, 75, 100, 175, 225, 400];
        const int PINNED[13] = [0, 0, -2, -3, -5, -8, -22, 0, 2, 3, 5, 8, 22];
        const int FRAMER[13] = [0, 0, -1, -2, -3, -4, -11, 0, 1, 2, 3, 4, 11];

        frames = 0;
        weakframers = 0;
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

            if (safe_traps[tside] & tbit)
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
                    ulong wframers;
                    real framing_score = 0;
                    while (tneighbors)
                    {
                        ulong ebit = tneighbors & -tneighbors;
                        tneighbors ^= ebit;
                        bitix eix = bitindex(ebit);
                        if (tpiece + pieceoffset > pos.pieces[eix])
                        {
                            wframers |= ebit;
                            if (neighbors_of(ebit) & pos.bitBoards[Piece.EMPTY])
                            {
                                framed = false;
                                break;
                            }
                        }
                        Piece epiece;
                        epiece = pos.pieces[eix];
                        framing_score += FRAMER[epiece];
                    }
                    if (framed)
                    {
                        weakframers |= wframers;
                        frames |= tbit;
                        score += FRAMED[tpiece];
                        score += framing_score;
                    }
                }
            }
        }
        return score;
    }

    int map_elephant()
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

    int rabbit_wall()
    {
        const int[2] BLOCKING_BONUS = [2, -2];

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

    int rabbit_open()
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

    int rabbit_home()
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

    real rabbit_strength()
    {
        // Depends on goal search and trap safety being done first
        const static int[] pieceval = [0, 0, 45, 60, 150, 200, 300,
              0, -45, -60, -150, -200, -300];
        const static int[] distval = [100, 100, 90, 75, 60,
              30, 25, 15, 10, 2, 2, 1, 1, 1, 0, 0];
        const static real[][] rankval = [[0, 0, 0, 0.2, 0.4, 1.0, 1.2, 0],
              [0, -1.2, -1.0, -0.5, -0.2, 0, 0, 0]];
        const static int[][] weakval = [[0, 0, -15, -30, -35, -40, -30, 0],
             [0, 30, 40, 35, 30, 15, 0, 0]];
        const static int power_balance = 1000;
        const static real full_weak = 6000;
        const static int full_strong = 8000;
        const ulong[] DEFENSE_SECTORS = [0xF8F8F8, 0x1F1F1F];
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

                if (power <= 0)
                {
                    real sfactor = -power / full_weak;
                    sfactor = (sfactor < 1) ? sfactor : 1;
                    debug (rabbit_strength)
                    {
                        writefln("weak r at %s, pf %.2f", ix_to_alg(rix), sfactor);
                    }
                    wscore += weakval[s][rix/8] * sfactor;
                } else {
                    power = (power < full_strong) ? power : full_strong;
                    real rv = rankval[s][rix/8];
                    real rval = power * rv;
                    if (rbit & TRAPS)
                        rval /= 2;
                    uint rfile = rix % 8;
                    ulong sector;
                    if (rfile < 6)
                        sector = DEFENSE_SECTORS[1];
                    if (rfile > 1)
                        sector |= DEFENSE_SECTORS[0];
                    if (s == Side.WHITE)
                    {
                        sector <<= 40;
                    }
                    if (!((safe_traps[s] & ~safe_traps[s^1]) & sector))
                        rval *= 0.4;
                    debug (rabbit_strength)
                    {
                        writefln("strong r at %s, val %.2f final %d sector %X st %X", ix_to_alg(rix), rval, cast(int)(rval*rstrong_w),
                                sector, safe_traps[s^1]);
                    }
                    sscore += rval;
                }
            }
        }
        return (wscore * rweak_w) + (sscore * rstrong_w);
    }

    int piece_strength()
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

    int frozen_pieces()
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

    int block_and_hostage()
    {
        // Depends on piece strength done first
        static const int[] BLOCKADE_VAL = [0, -1, -5, -10, -20, -35, -90,
                                    1, 5, 10, 20, 35, 90];
        static const int[] HOSTAGE_VAL = [0, -10, -25, -39, -61, -150, -264,
                                    10, 25, 39, 61, 150, 264];
        static const int[] HOLDER_PENALTY = [0, 0, -4, -5, -10, -18, -44,
                                    0, 4, 5, 10, 18, 44];
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

        hostages = 0;
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


                Piece strong_holder = pos.strongest[side^1][pix];
                hscore += HOLDER_PENALTY[strong_holder];
                if (pos.pieces[pix] >= (strong_holder + enemyoffset))
                {
                    // the piece is blockaded
                    debug (mobility)
                    {
                        logger.log("blockaded piece %d", pos.pieces[pix]);
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
                        logger.log("pseudo-blockade piece %s%s, pp %.2f", ".RCDHMErcdhme"[pos.pieces[pix]],
                                ix_to_alg(pix), power_mul);
                    }
                    hscore += HOSTAGE_VAL[pos.pieces[pix]] * TRAP_DIST_MUL[pix] * power_mul;
                    // it's not actually frozen but should carry the same penalty as if it were
                    hscore += FROZEN_PENALTY[pos.pieces[pix]] * 3; // magic number is frozen_w
                    hostages |= pbit;
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
                        hscore += HOSTAGE_VAL[pos.pieces[pix]] * TRAP_DIST_MUL[pix] * power_mul;
                        debug (mobility)
                        {
                            logger.log("hostage piece %s%s, pp %.2f, sc %.2f", ".RCDHMErcdhme"[pos.pieces[pix]],
                                    ix_to_alg(pix), power_mul,
                                    HOSTAGE_VAL[pos.pieces[pix]] * TRAP_DIST_MUL[pix] * power_mul);
                        }

                        Piece strong_holder = pos.strongest[side^1][pix];
                        hscore += HOLDER_PENALTY[strong_holder];
                        hostages |= pbit;
                    }
                }
            }
        }

        return cast(int)((bscore * blockade_w) + (hscore * hostage_w));
    }

    int mobility()
    {
        static const int[] BLOCKADE_VAL = [0, -1, -10, -15, -120, -200, -375,
                     1, 10, 15, 120, 200, 375];
        static const real[] MOBILITY_MUL = [1.0, 1.0, 0.8, 0.4, 0.1];
        static const real[] BLOCK_STRONGER_CL = [1.0, 0.4, 0.2, 0.1, 0.1];
        static const real[] BLOCK_STRONGER_FAR = [1.0, 0.6, 0.4, 0.3, 0.1];
        static const real[] BLOCK_EVEN_CL = [1.0, 0.6, 0.4];
        static const real[] BLOCK_EVEN_FAR = [1.0, 0.8, 0.6];
        static const real[] BLOCK_WEAK_CL = [1.0, 0.8, 0.6];
        static const real[] BLOCK_WEAK_FAR = [1.0, 0.9, 0.8];

        static const int[] MOBILE_VAL = [0, 10, 4, 1];
        static const real[] SIDE_MUL = [0.1, -0.1];

        static const int[] AREA_VAL = [0, 0, 2, 1];
        static const real[] AREA_MUL = [-0.2, 0.2];

        static const int[] NK_TOUCH_THREAT = [0, -7, -22, -30, -45, -80, -200,
                     7, 22, 30, 45, 80, 200];
        static const int[] NK_CLOSE_THREAT = [0, -5, -15, -20, -30, -64, -100,
                     5, 15, 20, 30, 64, 100];
        static const int[] NK_FAR_THREAT = [0, -2, -7, -10, -15, -28, -50,
                     2, 7, 10, 15, 28, 50];
        static const int[] KP_THREAT = [0, -1, -4, -5, -7, -14, -25,
                     1, 4, 5, 7, 14, 25];
        static const real threat_mul = 0.6;

        real score = 0;
        int[4][2] strongest_left;
        ulong[4][4][2] threat_map;
        for (Side side = Side.WHITE; side <= Side.BLACK; side++)
        {
            int pieces_checked;
            int pieceoffset = 0;
            int enemyoffset = -6;
            int pcorr = -6;
            int mcorr = 0;
            if (side == Side.BLACK)
            {
                pieceoffset = 6;
                enemyoffset = 6;
                pcorr = 0;
                mcorr = -6;
            }

            ulong freezers;
            for (int p = Piece.WELEPHANT + pieceoffset; p > Piece.WCAT + pieceoffset; p--)
            {
                int epiece = p + mcorr;
                int cutpiece = p + mcorr - 1;
                ulong pieces = pos.bitBoards[p];
                if (pieces)
                {
                    pieces_checked++;
                    if (pieces_checked < 4)
                        strongest_left[side][pieces_checked] = epiece;
                }
                pieces &= ~pos.frozen;
                while (pieces)
                {
                    ulong pbit = pieces & -pieces;
                    pieces ^= pbit;
                    ulong p_neighbors = neighbors_of(pbit);

                    ulong[5] tosquares;
                    ulong pfrozen;
                    piece_mobility(pos, pbit, freezers, tosquares, pfrozen);
                    int mobility = popcount(tosquares[4] & ~pfrozen);
                    if (pieces_checked < 4)
                    {
                        if (mobility > 4)
                        {
                            score += (MOBILE_VAL[pieces_checked] * mobility) * SIDE_MUL[side];
                        }
                        else if (pbit & ~pos.frozen)
                        {
                            real sc = BLOCKADE_VAL[p] * MOBILITY_MUL[mobility];
                            ulong[2] blockaders;
                            blockaders[0] = neighbors_of(tosquares[4]);
                            blockaders[1] = neighbors_of(blockaders[0]);
                            int blk_num = popcount(blockaders[0] & freezers);
                            blk_num = blk_num > 4 ? 4 : blk_num;
                            sc *= BLOCK_STRONGER_CL[blk_num];
                            blk_num = popcount(blockaders[1] & freezers);
                            blk_num = blk_num > 4 ? 4 : blk_num;
                            sc *= BLOCK_STRONGER_FAR[blk_num];
                            blk_num = popcount(blockaders[0] & pos.bitBoards[epiece]);
                            assert (blk_num < 3);
                            sc *= BLOCK_EVEN_CL[blk_num];
                            blk_num = popcount(blockaders[1] & pos.bitBoards[epiece]);
                            assert (blk_num < 3);
                            sc *= BLOCK_EVEN_FAR[blk_num];
                            blk_num = popcount(blockaders[0] & pos.bitBoards[epiece-1]);
                            blk_num = blk_num > 2 ? 2 : blk_num;
                            sc *= BLOCK_WEAK_CL[blk_num];
                            blk_num = popcount(blockaders[1] & pos.bitBoards[epiece-1]);
                            blk_num = blk_num > 2 ? 2 : blk_num;
                            sc *= BLOCK_WEAK_FAR[blk_num];
                            score += sc;
                            debug (mobility)
                            {
                                bitix pix = bitindex(pbit);
                                Piece ppiece = pos.pieces[pix];
                                logger.log("Found blockade of %s%s to be worth %f",
                                        ".RCDHMErcdhme"[ppiece], ix_to_alg(pix), sc);
                            }
                        }
                    }

                    int kept_piece;
                    ulong held = p_neighbors & hostages & pos.placement[side^1];
                    while (held && kept_piece < cutpiece)
                    {
                        ulong hbit = held & -held;
                        held ^= hbit;
                        Piece hpiece = pos.pieces[bitindex(hbit)];
                        if (kept_piece < hpiece + pcorr)
                            kept_piece = hpiece + pcorr;
                    }
                    held = p_neighbors & frames & pos.placement[side^1];
                    if (held && kept_piece < cutpiece)
                    {
                        assert(popcount(held)==1);
                        Piece hpiece = pos.pieces[bitindex(held)];
                        if (kept_piece < hpiece + pcorr)
                            kept_piece = hpiece + pcorr;
                    }
                    held = neighbors_of(p_neighbors & weakframers) & frames & pos.placement[side^1];
                    while (held && kept_piece < cutpiece)
                    {
                        ulong hbit = held & -held;
                        held ^= hbit;
                        Piece hpiece = pos.pieces[bitindex(hbit)];
                        if (kept_piece < hpiece + pcorr)
                            kept_piece = hpiece + pcorr;
                    }
                    held = TRAPS & p_neighbors;
                    held = (neighbors_of(held) | neighbors_of(neighbors_of(held)))
                        & hostages & pos.placement[side];
                    while (held && kept_piece < cutpiece)
                    {
                        ulong hbit = held & -held;
                        held ^= hbit;
                        Piece hpiece = pos.pieces[bitindex(hbit)];
                        if (kept_piece < hpiece + mcorr)
                            kept_piece = hpiece + mcorr;
                    }
                    held = p_neighbors & frames & pos.placement[side];
                    if (held && kept_piece < cutpiece)
                    {
                        assert(popcount(held)==1);
                        Piece hpiece = pos.pieces[bitindex(held)];
                        if (kept_piece < hpiece + mcorr)
                            kept_piece = hpiece + mcorr;
                    }

                    int spiece = kept_piece + 1;
                    for (int tp = Piece.WCAT; tp < epiece; tp++)
                    {
                        if (tp < spiece)
                        {
                            if (!(p_neighbors & frames & pos.placement[side]))
                                threat_map[side^1][tp-2][3] |= tosquares[1]
                                    & ~pfrozen;
                        } else {
                            threat_map[side^1][tp-Piece.WCAT][0] |= tosquares[0];
                            threat_map[side^1][tp-Piece.WCAT][1] |= tosquares[2]
                                & ~pfrozen & ~tosquares[0];
                            threat_map[side^1][tp-Piece.WCAT][2] |= tosquares[4]
                                & ~pfrozen & ~tosquares[2];
                        }
                    }
                }
                freezers |= pos.bitBoards[p - enemyoffset];
            }
        }
        debug (mobility)
        {
            logger.log("Mobility and blockade only: %f", score);
        }

        for (Side side = Side.WHITE; side <= Side.BLACK; side++)
        {
            for (int rank=2; rank < 4; rank++)
            {
                int strength = strongest_left[side][rank];
                if (!strength)
                    continue;
                int threat_ix = strength - Piece.WCAT;
                ulong threat_area = neighbors_of(threat_map[side][threat_ix][0]
                        | threat_map[side][threat_ix][1]
                        | threat_map[side][threat_ix][2]
                        | threat_map[side][threat_ix][3]);
                score += popcount(threat_area) * AREA_VAL[rank] * AREA_MUL[side];
            }
        }

        debug (mobility)
        {
            logger.log("Mobility, blockade and threat area: %f", score);
        }

        real threat_score = 0;
        for (Side side = Side.WHITE; side <= Side.BLACK; side++)
        {
            int eside = side^1;
            int enemyoffset = (side == Side.WHITE) ? -6 : 6;
            int pcorr = (side == Side.WHITE) ? 0 : 6;

            for (int p = Piece.WCAT; p < Piece.WELEPHANT; p++)
            {
                int threat_ix = p - Piece.WCAT;
                ulong cover = threat_map[side^1][threat_ix][0]
                    | threat_map[side^1][threat_ix][1]
                    | threat_map[side^1][threat_ix][3];
                ulong pieces = pos.bitBoards[p + pcorr];
                ulong handled;
                ulong threatened = neighbors_of(threat_map[side][threat_ix][0]) & pieces;
                threat_score += NK_TOUCH_THREAT[p + pcorr] * popcount(threatened);
                threat_score -= (NK_TOUCH_THREAT[p + pcorr]  * popcount(threatened & cover)) / 2;
                handled = threatened;
                threatened = neighbors_of(threat_map[side][threat_ix][3]) & pieces & ~handled;
                threat_score += KP_THREAT[p + pcorr] * popcount(threatened);
                threat_score -= (KP_THREAT[p + pcorr]  * popcount(threatened & cover)) / 2;
                handled |= threatened;
                threatened = neighbors_of(threat_map[side][threat_ix][1]) & pieces & ~handled;
                threat_score += NK_CLOSE_THREAT[p + pcorr] * popcount(threatened);
                threat_score -= (NK_CLOSE_THREAT[p + pcorr]  * popcount(threatened & cover)) / 2;
                handled |= threatened;
                cover |= threat_map[side^1][threat_ix][2];
                threatened = neighbors_of(threat_map[side][threat_ix][2]) & pieces & ~handled;
                threat_score += KP_THREAT[p + pcorr] * popcount(threatened & neighbors_of(pos.placement[side]));
                threat_score += NK_FAR_THREAT[p + pcorr] * popcount(threatened & ~neighbors_of(pos.placement[side]));
                threat_score -= (NK_FAR_THREAT[p + pcorr]  * popcount(threatened & cover)) / 4;

                debug (mobility)
                {
                    handled = 0;
                    threatened = neighbors_of(threat_map[side][threat_ix][0]) & pieces;
                    int threatened_pop = popcount(threatened);
                    if (threatened_pop)
                        logger.log("NK_TOUCH_THREAT to %d %s for %d", threatened_pop,
                                ".RCDHMErcdhme"[p + pcorr],
                                NK_TOUCH_THREAT[p + pcorr] * threatened_pop);
                    handled = threatened;
                    threatened = neighbors_of(threat_map[side][threat_ix][1])
                        & pieces & ~handled;
                    threatened_pop = popcount(threatened);
                    if (threatened_pop)
                        logger.log("NK_CLOSE_THREAT to %d %s for %d", threatened_pop,
                                ".RCDHMErcdhme"[p + pcorr],
                                NK_CLOSE_THREAT[p + pcorr] * threatened_pop);
                    handled |= threatened;
                    threatened = neighbors_of(threat_map[side][threat_ix][2])
                        & pieces & ~handled;
                    threatened_pop = popcount(threatened);
                    if (threatened_pop)
                        logger.log("NK_FAR_THREAT to %d %s", threatened_pop,
                                ".RCDHMErcdhme"[p + pcorr]);
                    handled |= threatened;
                    threatened = neighbors_of(threat_map[side][threat_ix][3])
                        & pieces & ~handled;
                    threatened_pop = popcount(threatened);
                    if (threatened_pop)
                        logger.log("KP_THREAT to %d %s for %d", threatened_pop,
                                ".RCDHMErcdhme"[p + pcorr],
                                KP_THREAT[p + pcorr] * threatened_pop);
                }
            }
        }
        score += threat_score * threat_mul;

        debug (mobility)
        {
            logger.log("Final mobility and threat: %f", score);
        }

        return cast(int)score;
    }

    int static_trap_eval(Side side, int pop, int fscore)
    {
        active_traps[side] = 0;

        int score = 0;
        if (trap_search.find_captures(pos, side))
        {
            ulong[3] valuable_vbit;
            Piece[3] valuable_victim;
            int[3] valuable_length;
            ulong[3] valuable_traps;
            for (int i=0; i < trap_search.num_captures; i++)
            {
                ulong vbit = trap_search.captures[i].victim_bit;
                ulong tbit = trap_search.captures[i].trap_bit;
                active_traps[side] |= tbit;
                Piece vic = trap_search.captures[i].victim;
                int len = trap_search.captures[i].length;
                for (int v=0; v < valuable_vbit.length; v++)
                {
                    if (vbit != valuable_vbit[v]
                            && (vic > valuable_victim[v]
                                || (vic == valuable_victim[v]
                                    && len < valuable_length[v])))
                    {
                        ulong tvbit = valuable_vbit[v];
                        Piece tvic = valuable_victim[v];
                        int tlen = valuable_length[v];
                        ulong ttbits = valuable_traps[v];
                        valuable_vbit[v] = vbit;
                        valuable_victim[v] = vic;
                        valuable_length[v] = len;
                        valuable_traps[v] = tbit;
                        vbit = tvbit;
                        vic = tvic;
                        tbit = ttbits;
                        len = tlen;
                    } else if (vbit == valuable_vbit[v])
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
                ulong b = valuable_vbit[0];
                valuable_vbit[0] = valuable_vbit[1];
                valuable_vbit[1] = b;
            }
            if (valuable_victim[1] == valuable_victim[2]
                    && valuable_length[1] > valuable_length[2])
            {
                int l = valuable_length[1];
                valuable_length[1] = valuable_length[2];
                valuable_length[2] = l;
                ulong b = valuable_vbit[1];
                valuable_vbit[1] = valuable_vbit[2];
                valuable_vbit[2] = b;
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

            // frozen victim
            // multiple traps for one victim
            // multiple victims one trap
            // nearness stronger or even piece
            const static real[] victim_per = [0.65, 0.75, 0.85];
            const static real[] length_per = [1.0,
                1.0, 1.0, 0.9, 0.9,
                0.3, 0.3, 0.2, 0.1,
                0.05, 0.05, 0.01, 0.01];
            const static real[] defense_per = [1.0, 0.9, 0.8, 0.6, 0.4];
            const static real frozen_per = 0.2;
            const static real multivic_per = 0.9;
            const static real multitrap_per = 1.5;
            const static real max_victim_per = 0.9;
            real defense_mul = (side != pos.side) ? defense_per[pos.stepsLeft] : defense_per[4];
            ulong used_traps = 0;
            ulong future_victims = 0;
            for (int i=0; i < 3; i++)
            {
                if (valuable_victim[i] != 0)
                {
                    real val;
                    if (valuable_length[i])
                    {
                        real per = victim_per[future_victims];
                        if (valuable_vbit[i] & pos.frozen)
                        {
                            per += frozen_per;
                        }
                        if ((valuable_traps[i] & used_traps) == valuable_traps[i])
                        {
                            per *= multivic_per;
                        }
                        if (popcount(valuable_traps[i]) > 1)
                        {
                            per *= multitrap_per;
                        }
                        per *= length_per[valuable_length[i]] * defense_mul;
                        per = (per < max_victim_per) ? per : max_victim_per;
                        val = valuable_value[i] * per;
                        future_victims++;
                    } else {
                        val = valuable_value[i] * max_victim_per;
                    }

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
        trap_search.clear();

        return score;
    }

    int goal_threat()
    {
        // Depends on goal search being done first
        const int[18] GOAL_THREAT = [10000, 800, 750, 650, 600,
              100, 100, 80, 80,
              40, 40, 30, 30,
              10, 10, 5, 5, 0];
        const real[] DEFENSE_STEPS = [1.0, 0.8, 0.66, 0.5, 0.33];
        const real[] DEFENSE_NUM = [1.0, 0.8, 0.7, 0.4, 0.2, 0.1, 0.05, 0.01, 0.01];
        const ulong[] DEFENSE_SECTORS = [0xF8F8F8, 0x1F1F1F];
        const ulong MIDDLE_SECTOR = 0x181818;
        const ulong[] GOAL_RANK = [RANK_8, RANK_1];
        const int[] SIDE_MUL = [1, -1];

        int score = 0;
        for (Side s = Side.WHITE; s <= Side.BLACK; s++)
        {
            if (goals.shortest[s] != goals.NOT_FOUND)
            {
                uint num_threats = 0;
                uint dsteps = 4;
                uint extrasteps = goals.shortest[s];
                if (s == pos.side)
                    extrasteps -= pos.stepsLeft;
                else
                    dsteps = pos.stepsLeft;

                int sector_shift = 0;
                ulong orabbits = pos.bitBoards[Piece.WRABBIT];
                if (s == Side.WHITE)
                {
                    sector_shift = 40;
                    orabbits = pos.bitBoards[Piece.BRABBIT];
                }
                ulong defenders = pos.placement[s^1] & ~orabbits;
                int defender_num;
                if (goals.goal_squares & ~(MIDDLE_SECTOR << sector_shift) & GOAL_RANK[s])
                {
                    ulong sector = DEFENSE_SECTORS[0] << sector_shift;;
                    int[2] sector_defenders;
                    if (goals.goal_squares & sector & GOAL_RANK[s])
                    {
                        sector_defenders[0] = popcount(sector & defenders);
                        if (sector & (safe_traps[s^1] & ~safe_traps[s]))
                            sector_defenders[0] >>= 1;
                        num_threats++;
                    } else {
                        sector_defenders[0] = 8;
                    }
                    sector = DEFENSE_SECTORS[1] << sector_shift;
                    if (goals.goal_squares & sector & GOAL_RANK[s])
                    {
                        sector_defenders[1] = popcount(sector & defenders);
                        if (sector & (safe_traps[s^1] & ~safe_traps[s]))
                            sector_defenders[1] >>= 1;
                        num_threats++;
                    } else {
                        sector_defenders[1] = 8;
                    }
                    defender_num = sector_defenders[0] < sector_defenders[1] ? sector_defenders[0] : sector_defenders[1];
                } else {
                    ulong sector = 0xFFFFFF << sector_shift;
                    defender_num = popcount(defenders & sector);
                    if (sector & (safe_traps[s^1] & ~safe_traps[s]))
                        defender_num >>= 1;
                    num_threats++;
                    if (goals.goal_squares & (0x030303 << sector_shift))
                        num_threats++;
                    if (goals.goal_squares & (0xC0C0C0 << sector_shift))
                        num_threats++;
                }
                switch (num_threats)
                {
                    case 2:
                        dsteps >>= 1;
                        break;
                    case 3:
                        dsteps >>= 1;
                        defender_num >>= 1;
                        break;
                    default:
                }
                score += GOAL_THREAT[extrasteps] * DEFENSE_STEPS[dsteps] * DEFENSE_NUM[defender_num] * SIDE_MUL[s];
            }
        }
        return score;
    }

    int static_eval(Position pos)
    {
        // check if the score is cached for this position
        SCNode* sc_entry = sc_cache.get(pos);
        if (sc_entry.zobrist == pos.zobrist)
            return sc_entry.score;

        int score;
        if (pos.is_endstate() && pos.is_goal(cast(Side)(pos.side^1)))
        {
            // the only time static eval should end up called with a endstate is when there is an opposing rabbit
            // on the goal line that might still get pulled back off before the end of the turn
            score = -(WIN_SCORE - pos.stepsLeft);
            sc_entry.zobrist = pos.zobrist;
            sc_entry.score = score;
            return score;
        }

        this.pos = pos;
        goals.set_start(pos);
        goals.find_goals();
        if ((goals.shortest[pos.side] != goals.NOT_FOUND)
                && goals.shortest[pos.side] <= pos.stepsLeft)
        {
            score = WIN_SCORE - goals.shortest[pos.side];
            sc_entry.zobrist = pos.zobrist;
            sc_entry.score = score;
            return score;
        }

        int pop = population(pos);
        int fscore = fame.score(pop); // first pawn worth ~196
                                     // only a pawn left ~31883
        score = fscore;
        score += static_trap_eval(cast(Side)(pos.side^1), pop, fscore) * static_otrap_w;
        score += static_trap_eval(pos.side, pop, fscore) * static_strap_w;

        score += trap_safety() * tsafety_w;
        score += piece_strength() * pstrength_w;
        score += on_trap() * ontrap_w;
        score += block_and_hostage();
        score += mobility() * mobility_w;
        score += rabbit_strength();
        score += rabbit_wall() * rwall_w;
        score += rabbit_open() * ropen_w;
        score += rabbit_home() * rhome_w;
        score += frozen_pieces() * frozen_w;
        score += map_elephant() * map_e_w;
        score += goal_threat() * goal_w;

        if (pos.side == Side.BLACK)
            score = -score;

        // clamp the evaluation to be less than a win
        score = (score < MAX_EVAL_SCORE) ? ((score > -(MAX_EVAL_SCORE)) ? score : -(MAX_EVAL_SCORE)) : MAX_EVAL_SCORE;

        // Enter the score into the cache
        sc_entry.zobrist = pos.zobrist;
        sc_entry.score = score;
        return score;
    }

    int logged_eval(Position pos)
    {
        if (pos.is_endstate() && pos.is_goal(cast(Side)(pos.side^1)))
        {
            return -(WIN_SCORE - pos.stepsLeft);
        }

        this.pos = pos;
        goals.set_start(pos);
        goals.find_goals();
        if ((goals.shortest[pos.side] != goals.NOT_FOUND)
                && goals.shortest[pos.side] <= pos.stepsLeft)
        {
            logger.log("Found goal in %d steps", goals.shortest[pos.side]);
            return WIN_SCORE - goals.shortest[pos.side];
        }

        int pop = population(pos);
        int fscore = fame.score(pop); // first pawn worth ~196
                                     // only a pawn left ~31883
        logger.log("Fame %d", fscore);
        int score = fscore;
        int pscore = fscore;
        score += static_trap_eval(cast(Side)(pos.side^1), pop, fscore) * static_otrap_w;
        logger.log("static otrap %d", score-pscore);
        pscore = score;
        score += static_trap_eval(pos.side, pop, fscore) * static_strap_w;
        logger.log("static strap %d", score-pscore);
        pscore = score;

        score += trap_safety() * tsafety_w;
        logger.log("trap safety %d", score-pscore);
        pscore = score;
        score += piece_strength() * pstrength_w;
        logger.log("piece strength %d", score-pscore);
        pscore = score;
        score += on_trap() * ontrap_w;
        logger.log("on trap %d", score-pscore);
        score += block_and_hostage();
        logger.log("blockade and hostage %d", score-pscore);
        pscore = score;
        score += mobility() * mobility_w;
        logger.log("mobility %d", score-pscore);
        pscore = score;
        score += rabbit_strength();
        logger.log("rabbit strength %d", score-pscore);
        pscore = score;
        score += rabbit_wall() * rwall_w;
        logger.log("rabbit wall %d", score-pscore);
        pscore = score;
        score += rabbit_open() * ropen_w;
        logger.log("rabbit open %d", score-pscore);
        pscore = score;
        score += rabbit_home() * rhome_w;
        logger.log("rabbit home %d", score-pscore);
        pscore = score;
        score += frozen_pieces() * frozen_w;
        logger.log("frozen pieces %d", score-pscore);
        pscore = score;
        score += map_elephant() * map_e_w;
        logger.log("map elephant %d", score-pscore);
        pscore = score;

        if (pos.side == Side.BLACK)
            score = -score;

        pscore = score;
        score += goal_threat();
        logger.log("goal threat (side to move) %d", score-pscore);
        pscore = score;

        // clamp the evaluation to be less than a win
        score = (score < MAX_EVAL_SCORE) ? ((score > -(MAX_EVAL_SCORE)) ? score : -(MAX_EVAL_SCORE)) : MAX_EVAL_SCORE;
        logger.log("Final (clamped) score %d", score);
        logger.info("score cr %d", cast(int)(score/1.96));
        return score;
    }
}
