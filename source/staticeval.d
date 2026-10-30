
import std.conv : to;

import alphabeta;
import goalsearch;
import logging;
import movement;
import position;
import trapmoves;
static import tunables;

struct SCNode
{
    ulong zobrist;
    int score;
    // goals.shortest for the position, which the quiescence search reads
    // after static_eval
    byte[2] shortest;

    void set(ulong zobrist, int score, ref const int[2] shortest)
    {
        this.zobrist = zobrist;
        this.score = score;
        this.shortest[0] = cast(byte)shortest[0];
        this.shortest[1] = cast(byte)shortest[1];
    }
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

    void clear()
    {
        cache[] = SCNode.init;
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
    int[13] piece_value;
    ulong hostages;
    ulong frames;
    ulong weakframers;

    ScoreCache sc_cache;

    double map_e_w = 5.968485;
    double tsafety_w = 0.449359;
    double ontrap_w = 0.221773;
    double frozen_w = -0.076083;
    double rwall_w = 3.895628;
    double ropen_w = 2.415587;
    double rhome_w = 7.199276;
    double rweak_w = -0.568718;
    double rstrong_w = 0.330797;
    double pstrength_w = 237.865468 * 0.00001;  // eval_pstrength 237.865468
    double goal_w = 3.221802;
    double static_otrap_w = 0.571653;
    double static_strap_w = 0.484686;
    double hostage_w = 0.942175;
    double frame_w = 1.029407;
    double mobility_w = 0.669584;
    double threat_w = 0.529335;
    // Longer goal terms, off by default (see goal_estimate, goal_five).
    double goalest_w = 1;
    double goal5_w = 0;
    private GoalSearchDT five_search; // goal_five's, so goals is left as it is

    this(Logger l, GoalSearchDT g, TrapGenerator t)
    {
        logger = l;
        goals = g;
        trap_search = t;
        fame = new FastFAME(0.1716);
        sc_cache= new ScoreCache(200000);
    }

    bool set_option(string option, string value)
    {
        bool handled = true;
        switch (option)
        {
            case "eval_map_e":
                map_e_w = to!double(value);
                break;
            case "eval_tsafety":
                tsafety_w = to!double(value);
                break;
            case "eval_frozen":
                frozen_w = to!double(value);
                break;
            case "eval_ontrap":
                ontrap_w = to!double(value);
                break;
            case "eval_rwall":
                rwall_w = to!double(value);
                break;
            case "eval_ropen":
                ropen_w = to!double(value);
                break;
            case "eval_rhome":
                rhome_w = to!double(value);
                break;
            case "eval_rweak":
                rweak_w = to!double(value);
                break;
            case "eval_rstrong":
                rstrong_w = to!double(value);
                break;
            case "eval_pstrength":
                pstrength_w = to!double(value) * 0.00001;
                break;
            case "eval_goal":
                goal_w = to!double(value);
                break;
            case "eval_static_otrap":
                static_otrap_w = to!double(value);
                break;
            case "eval_static_strap":
                static_strap_w = to!double(value);
                break;
            case "eval_hostage":
                hostage_w = to!double(value);
                break;
            case "eval_frame":
                frame_w = to!double(value);
                break;
            case "eval_mobility":
                mobility_w = to!double(value);
                break;
            case "eval_threat":
                threat_w = to!double(value);
                break;
            case "eval_goalest":
                goalest_w = to!double(value);
                break;
            case "eval_goal5":
                goal5_w = to!double(value);
                break;
            case "eval_cache_size":
                sc_cache.set_size(to!(int)(value));
                break;
            default:
                handled = tunables.set_option(option, value);
        }
        return handled;
    }

    int trap_safety()
    {
        alias BOTH_SAFE = tunables.BOTH_SAFE;
        alias WHITE_SAFE = tunables.WHITE_SAFE;
        alias BLACK_SAFE = tunables.BLACK_SAFE;

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
                default:
                    break;
            }
        }
        return score;
    }

    // penalty for piece on trap
    int on_trap()
    {
        //const int ON_TRAP[13] = [0, -6, -9, -12, -18, -33, -88,
        //      6, 9, 12, 18, 33, 88];
        static immutable double ON_TRAP_MUL = 0.02;

        double score = 0;
        ulong occupied_traps = ~pos.bitBoards[Piece.EMPTY] & TRAPS;
        while (occupied_traps)
        {
            ulong tbit = occupied_traps & -occupied_traps;
            occupied_traps ^= tbit;
            bitix tix = bitindex(tbit);
            Piece tpiece = pos.pieces[tix];
            Side tside = (tpiece > Piece.WELEPHANT) ? Side.BLACK : Side.WHITE;

            if (safe_traps[tside] & tbit)
            {
                score -= piece_value[tpiece] * ON_TRAP_MUL / 2.0;
            } else {
                score -= piece_value[tpiece] * ON_TRAP_MUL;
            }

        }
        return cast(int)score;
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
        alias NORABBIT_FILE = tunables.NORABBIT_FILE;
        alias NORABBIT_ADJ = tunables.NORABBIT_ADJ;
        alias OPEN_FILE = tunables.OPEN_FILE;
        alias OPEN_ADJ = tunables.OPEN_ADJ;

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
        static immutable int[] side_mul = [1, -1];
        static immutable ulong[][] side_rank = [[RANK_1, RANK_2], [RANK_8, RANK_7]];
        alias FIRST_ROW = tunables.RHOME_FIRST_ROW;

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

    double rabbit_strength()
    {
        // Depends on goal search and trap safety being done first
        alias pieceval = tunables.RS_PIECEVAL;
        alias distval = tunables.RS_DISTVAL;
        alias rankval = tunables.RS_RANKVAL;
        alias WEAK_MUL = tunables.RS_WEAK_MUL;
        // Try to encourage rabbits to the edges.
        alias rsq = tunables.RS_SQ;
        alias INIT_BALANCE = tunables.RS_INIT_BALANCE;
        alias WEAK_SPAN = tunables.RS_WEAK_SPAN;
        alias STRONG_SPAN = tunables.RS_STRONG_SPAN;
        alias STRONG_VAL = tunables.RS_STRONG_VAL;
        const ulong[] DEFENSE_SECTORS = [0xF8F8F8, 0x1F1F1F];
        static immutable int[] rforward = [8, -8];
        static immutable double[] side_mul = [1, -1];

        double wscore = 0;
        double sscore = 0;
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
            Piece rabbit_piece;
            if (s == Side.WHITE)
            {
                rabbit_piece = Piece.WRABBIT;
                rabbits = pos.bitBoards[Piece.WRABBIT] & ~RANK_1;
            } else {
                rabbit_piece = Piece.BRABBIT;
                rabbits = pos.bitBoards[Piece.BRABBIT] & ~RANK_8;
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
                power = cast(int)(power * (side_mul[s]));

                uint rfile = rix % 8;
                ulong sector;
                if (rfile < 5)
                    sector = DEFENSE_SECTORS[1];
                if (rfile > 2)
                    sector |= DEFENSE_SECTORS[0];
                if (s == Side.WHITE)
                    sector <<= 40;
                int power_balance = INIT_BALANCE + (popcount(
                        pos.placement[s^1] & sector) * tunables.RS_DEFENDER_BALANCE);
                power -= power_balance;

                // encourage rabbits to the edges
                int rsi = rix;
                if (s == Side.BLACK)
                    rsi = 63 - rsi;
                wscore += -piece_value[rabbit_piece] * rsq[rsi];
                if (power < 0)
                {
                    double full_weak = WEAK_SPAN + power_balance;
                    double sfactor = -power / full_weak;
                    sfactor = (sfactor < 1) ? sfactor : 1;
                    double rval = -piece_value[rabbit_piece] * WEAK_MUL[s][rix/8]
                        * sfactor;
                    wscore += rval;
                    debug (rabbit_strength)
                    {
                        logger.log("weak r at {}, pf {}, rval {}",
                                ix_to_alg(rix), sfactor, rval);
                    }
                }
                else if (power > 0)
                {
                    int full_strong = STRONG_SPAN + power_balance;
                    power = (power < full_strong) ? power : full_strong;
                    double sfactor = cast(double) power / full_strong;
                    double rv = rankval[s][rix/8];
                    double rval = STRONG_VAL * rv * sfactor;
                    if (rbit & TRAPS)
                        rval *= tunables.RS_STRONG_TRAP_MUL;
                    if (!((safe_traps[s] & ~safe_traps[s^1]) & sector))
                        rval *= tunables.RS_STRONG_UNSAFE_MUL;
                    debug (rabbit_strength)
                    {
                        logger.log("strong r at {}, val {} final {} sector {:X} mst {:X} ost {:X}",
                                ix_to_alg(rix), rval, cast(int)(rval*rstrong_w),
                                sector, safe_traps[s], safe_traps[s^1]);
                    }
                    sscore += rval;
                }
            }
        }
        return (wscore * rweak_w) + (sscore * rstrong_w);
    }

    int piece_strength()
    {
        alias pieceval = tunables.PS_PIECEVAL;
        alias distval = tunables.PS_DISTVAL;
        static immutable int[][] pmul = [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
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
        alias MAX_POWER = tunables.PS_MAX_POWER; // == pieceval[Piece.WELEPHANT] * distval[0] * pmul;
        alias MIN_POWER = tunables.PS_MIN_POWER; // == pieceval[Piece.BELEPHANT] * distval[0] * pmul;

        bitix[16] ixs;
        int[16] value;
        Piece[16] piece;

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
                value[num_pieces] /= 8;
            ixs[num_pieces++] = pix;
        }

        debug (piece_strength)
        {
            logger.log("{}\n{}", "wb"[pos.side], pos.to_long_str());
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
                logger.log("piece {} at {} has {} power",
                        pos.pieces[pix], ix_to_alg(pix), ppower);
            }
        }
        debug (piece_strength)
        {
            logger.log("overall board piece strength {}", score);
        }
        return score;
    }

    int frozen_pieces()
    {
        alias FROZEN_PENALTY = tunables.FROZEN_PENALTY;
        alias POPULATION_MUL = tunables.POPULATION_MUL;

        int score = 0;
        // Stops before the silver elephant (12) to save a step: elephants
        // are never frozen. Gold's (6) is left in, since skipping it would
        // take an extra test.
        for (int p=1; p < 12; p++)
        {
            score += popcount(pos.bitBoards[p] & pos.frozen) * FROZEN_PENALTY[p];
        }

        uint total_pop = popcount(~pos.bitBoards[Piece.EMPTY]);
        assert (total_pop <= 32, "Less than 32 empty spaces on the board");

        return cast(int)(score * POPULATION_MUL[total_pop]);
    }

    int mobility()
    {

        double check_hostage(ulong pbit, Side side, int pieceoffset,
                ulong unsafe, ulong holders, int mobility)
        {
            //static immutable int[] HOSTAGE_VAL = [0, -10, -25, -39, -61, -150, -264,
            //                        10, 25, 39, 61, 150, 264];
            alias HOSTAGE_DIV = tunables.HOSTAGE_DIV;
            //static immutable int[] HOLDER_PENALTY = [0, 0, -4, -5, -10, -18, -44,
            //                        0, 4, 5, 10, 18, 44];
            alias HOLDER_DIV = tunables.HOLDER_DIV;
            alias FROZEN_HOLDER_DIV = tunables.FROZEN_HOLDER_DIV;
            static immutable double[] TRAP_DIST_MUL =
                                    [0.5, 0.5, 1.0, 0.5, 0.5, 1.0, 0.5, 0.5,
                                     0.5, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 0.5,
                                     1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0,
                                     0.5, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 0.5,
                                     0.5, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 0.5,
                                     1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0,
                                     0.5, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 0.5,
                                     0.5, 0.5, 1.0, 0.5, 0.5, 1.0, 0.5, 0.5];
            static immutable int[] NEAREST_TRAP =
                [18, 18, 18, 18, 21, 21, 21, 21,
                 18, 18, 18, 18, 21, 21, 21, 21,
                 18, 18, 18, 18, 21, 21, 21, 21,
                 18, 18, 18, 18, 21, 21, 21, 21,
                 42, 42, 42, 42, 45, 45, 45, 45,
                 42, 42, 42, 42, 45, 45, 45, 45,
                 42, 42, 42, 42, 45, 45, 45, 45,
                 42, 42, 42, 42, 45, 45, 45, 45];
            alias MOBILE_MUL = tunables.MOBILE_MUL;
            alias EON_TRAP = tunables.EON_TRAP;
            alias EN_OF_TRAP = tunables.EN_OF_TRAP;
            alias ENN_OF_TRAP = tunables.ENN_OF_TRAP;

            // FIXME: coverage does not include any rabbit movement
            ulong coverage = neighbors_of(pos.placement[side] & ~pbit
                    & ~pos.bitBoards[Piece.WRABBIT+pieceoffset] & ~pos.frozen)
                & pos.bitBoards[Piece.EMPTY] & ~unsafe;
            for (int steps = 0; steps < 2; steps++)
            {
                coverage |= neighbors_of(coverage) & pos.bitBoards[Piece.EMPTY]
                    & ~unsafe;
            }

            double score = 0;
            if (popcount(neighbors_of(pbit) & coverage) < 2)
            {
                bitix pix = bitindex(pbit);
                // The power around the hostage, from -1 (the other side's,
                // at the clamp) to 1 (its own side's). The more of it the
                // hostage's side has, the likelier a rescue, so power_mul
                // falls steadily from HOSTAGE_POWER_MUL by up to
                // HOSTAGE_POWER_SLOPE of it.
                double power = (side ? -pstrengths[pix] : pstrengths[pix])
                    / cast(double) tunables.PS_MAX_POWER;
                double power_mul = tunables.HOSTAGE_POWER_MUL
                    * (1 - tunables.HOSTAGE_POWER_SLOPE * (1 + power) / 2);
                auto hpiece_value = piece_value[pos.pieces[pix]];
                score = (-hpiece_value / HOSTAGE_DIV)
                    * TRAP_DIST_MUL[pix] * MOBILE_MUL[mobility] * power_mul;

                Piece strong_holder = pos.strongest[side^1][pix];
                score += -piece_value[strong_holder] / HOLDER_DIV;
                bool hfrozen = false;
                while (holders)
                {
                    ulong hbit = holders & -holders;
                    holders ^= hbit;
                    auto hix = bitindex(hbit);
                    if (pos.pieces[hix] == strong_holder)
                    {
                        if (hbit & pos.frozen)
                        {
                            hfrozen = true;
                        } else {
                            hfrozen = false;
                            break;
                        }
                    }
                }
                if (hfrozen)
                    score /= FROZEN_HOLDER_DIV;
                ulong nearest_trap = 1UL << NEAREST_TRAP[pix];
                if (nearest_trap & pos.placement[side])
                    score *= EON_TRAP;
                ulong near_neighbors = neighbors_of(nearest_trap)
                    & pos.placement[side] & ~pbit;
                int neighbor_count = popcount(near_neighbors);
                for (int i=0; i < neighbor_count; i++)
                    score *= EN_OF_TRAP;
                ulong far_neighbors = neighbors_of(near_neighbors)
                        & pos.placement[side] & ~nearest_trap;
                neighbor_count = popcount(far_neighbors);
                for (int i=0; i < neighbor_count; i++)
                    score *= ENN_OF_TRAP;

                hostages |= pbit;
                if ((hpiece_value > 0 && score > 0)
                        || (hpiece_value < 0 && score < 0))
                    score = 0;
                debug (mobility)
                {
                    logger.log("hostage piece {}{}, sc {}",
                            ".RCDHMErcdhme"[pos.pieces[pix]],
                            ix_to_alg(pix), score);
                }
            }
            return score * hostage_w;
        }

        double frame_check(ulong pbit, Side side, int enemyoffset)
        {
            /*
            static immutable int[13] FRAMED_VAL = [0,
                                        -100, -150, -200, -250, -325, -800,
                                        100, 150, 200, 250, 325, 800];
            static immutable int[13] PINNED_VAL = [0, 0, -8, -12, -20, -32, -88,
                                        0, 8, 12, 20, 32, 88];
            static immutable int[13] FRAMER_VAL = [0, 0, -2, -4, -6, -8, -22,
                         0, 2, 4, 6, 8, 22];
                         */
            alias FRAMED_DIV = tunables.FRAMED_DIV;
            alias PINNED_DIV = tunables.PINNED_DIV;
            alias FRAMER_DIV = tunables.FRAMER_DIV;

            bitix pix = bitindex(pbit);
            frames |= pbit;
            double score = 0;
            ulong framers = neighbors_of(pbit) & pos.placement[side^1];
            while (framers)
            {
                ulong frbit = framers & -framers;
                framers ^= frbit;
                bitix frix = bitindex(frbit);
                if (pos.pieces[pix]
                        < pos.pieces[frix] + enemyoffset)
                {
                    weakframers |= frbit;
                }
                score += -piece_value[pos.pieces[frix]] / FRAMER_DIV;
            }
            score += (-piece_value[pos.strongest[side][pix]] / PINNED_DIV)
                + (-piece_value[pos.pieces[pix]] / FRAMED_DIV);
            debug (mobility)
            {
                logger.log("Found frame of {}{} worth {}",
                        ".RCDHMErcdhme"[pos.pieces[pix]],
                        ix_to_alg(pix), score);
            }
            return score * frame_w;
        }

        //static immutable int[] BLOCKADE_VAL = [0, -1, -5, -10, -50, -150, -700,
        //             1, 5, 10, 50, 150, 700];
        alias BLOCKADE_DIV = tunables.BLOCKADE_DIV;
        alias MOBILITY_MUL = tunables.MOBILITY_MUL;
        alias CLOSE_BLOCKADER_DIV = tunables.CLOSE_BLOCKADER_DIV;
        alias FAR_BLOCKADER_DIV = tunables.FAR_BLOCKADER_DIV;
        // stronger close blockaders are possible hostage holders
        alias BLOCK_STRONGER_CL = tunables.BLOCK_STRONGER_CL;
        alias BLOCK_STRONGER_FAR = tunables.BLOCK_STRONGER_FAR;
        alias BLOCK_EVEN_CL = tunables.BLOCK_EVEN_CL;
        alias BLOCK_EVEN_FAR = tunables.BLOCK_EVEN_FAR;
        alias BLOCK_WEAK_CL = tunables.BLOCK_WEAK_CL;
        alias BLOCK_WEAK_FAR = tunables.BLOCK_WEAK_FAR;

        alias MOBILE_VAL = tunables.MOBILE_VAL;
        alias SIDE_MUL = tunables.MOBILE_SIDE_MUL;

        hostages = 0;
        frames = 0;
        weakframers = 0;
        double score = 0;
        int[4][2] strongest_left;
        ulong[5][16] reach_map;
        ulong[16] freezes;
        int pnum;
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

            ulong unsafe_traps = 0;
            ulong tbits = TRAPS;
            while (tbits)
            {
                ulong tbit = tbits & -tbits;
                tbits ^= tbit;

                if (popcount(neighbors_of(tbit) & pos.placement[side]) < 2)
                {
                    unsafe_traps |= tbit;
                }
            }

            ulong stronger;
            ulong blockader_penalized = 0UL;
            for (int p = Piece.WELEPHANT + pieceoffset;
                    p >= Piece.WCAT + pieceoffset; p--)
            {
                int epiece = p + mcorr;
                int cutpiece = p + mcorr - 1;
                // the enemy piece of the same rank
                ulong even = pos.bitBoards[p - enemyoffset];
                ulong pieces = pos.bitBoards[p];
                if (pieces)
                {
                    pieces_checked++;
                    if (pieces_checked < 4)
                        strongest_left[side][pieces_checked] = epiece;
                }
                while (pieces)
                {
                    ulong pbit = pieces & -pieces;
                    pieces ^= pbit;
                    ulong p_neighbors = neighbors_of(pbit);

                    piece_mobility(pos, pbit, stronger, reach_map[pnum],
                            freezes[pnum]);
                    int mobility = popcount(reach_map[pnum][4]);
                    // don't count the square the piece is on
                    mobility = mobility > 0 ? mobility - 1 : 0;
                    if (pieces_checked < 4)
                    {
                        score += (MOBILE_VAL[pieces_checked] * mobility)
                            * SIDE_MUL[side];
                    }
                    double fhscore = 0.;
                    if (mobility == 0 && (pbit & unsafe_traps))
                    {
                        fhscore = frame_check(pbit, side, enemyoffset);
                    }
                    else if (mobility <= 3 && (p_neighbors & stronger))
                    {
                        fhscore = check_hostage(pbit, side, pieceoffset,
                                unsafe_traps, p_neighbors & stronger,
                                mobility);
                    }
                    score += fhscore;
                    if (fhscore == 0 && mobility <= 3 && (pbit & ~pos.frozen))
                    {
                        double sc = (-piece_value[p] / BLOCKADE_DIV)
                            * MOBILITY_MUL[mobility];
                        ulong[2] blockaders;
                        blockaders[0] = neighbors_of(reach_map[pnum][4])
                            & pos.placement[side^1];
                        blockaders[1] = neighbors_of(blockaders[0])
                            & ~blockaders[0] & pos.placement[side^1];
                        int blk_num = popcount(blockaders[0] & stronger);
                        blk_num = blk_num > 4 ? 4 : blk_num;
                        sc *= BLOCK_STRONGER_CL[blk_num];
                        blk_num = popcount(blockaders[1] & stronger);
                        blk_num = blk_num > 4 ? 4 : blk_num;
                        sc *= BLOCK_STRONGER_FAR[blk_num];
                        blk_num = popcount(blockaders[0] & even);
                        assert (blk_num < 3);
                        sc *= BLOCK_EVEN_CL[blk_num];
                        blk_num = popcount(blockaders[1] & even);
                        assert (blk_num < 3);
                        sc *= BLOCK_EVEN_FAR[blk_num];
                        blk_num = popcount(blockaders[0] &
                                ~(stronger | even));
                        blk_num = (blk_num < 6) ? blk_num : 6;
                        sc *= BLOCK_WEAK_CL[blk_num];
                        blk_num = popcount(blockaders[1] &
                                ~(stronger | even));
                        blk_num = (blk_num < 8) ? blk_num : 8;
                        sc *= BLOCK_WEAK_FAR[blk_num];
                        double bpiece_penalty = 0;
                        while (blockaders[0]) {
                            ulong bbit = blockaders[0] & -blockaders[0];
                            blockaders[0] ^= bbit;
                            if (bbit & blockader_penalized)
                                continue;
                            blockader_penalized |= bbit;
                            bitix bix = bitindex(bbit);
                            bpiece_penalty += -piece_value[pos.pieces[bix]]
                                / CLOSE_BLOCKADER_DIV;
                            if (bbit & TRAPS
                                    & ~neighbors_of(pos.placement[side]
                                        & ~pbit))
                                bpiece_penalty /= tunables.BLOCKADER_TRAP_DIV;
                        }
                        while (blockaders[1]) {
                            ulong bbit = blockaders[1] & -blockaders[1];
                            blockaders[1] ^= bbit;
                            if (bbit & blockader_penalized)
                                continue;
                            blockader_penalized |= bbit;
                            bitix bix = bitindex(bbit);
                            bpiece_penalty += -piece_value[pos.pieces[bix]]
                                / FAR_BLOCKADER_DIV;
                            if (bbit & TRAPS
                                    & ~neighbors_of(pos.placement[side]
                                        & ~pbit))
                                bpiece_penalty /= tunables.BLOCKADER_TRAP_DIV;
                        }
                        if ((sc < 0 && sc + bpiece_penalty < 0)
                                || (sc > 0 && sc + bpiece_penalty > 0))
                            score += sc + bpiece_penalty;
                        debug (mobility)
                        {
                            bitix pix = bitindex(pbit);
                            Piece ppiece = pos.pieces[pix];
                            logger.log("Found blockade of {}{} to be worth {} + {}",
                                    ".RCDHMErcdhme"[ppiece],
                                    ix_to_alg(pix), sc, bpiece_penalty);
                        }
                    }
                    ++pnum;
                    assert(pnum <= 16,
                            "Had more than 16 pieces in mobility eval");
                }
                stronger |= pos.bitBoards[p - enemyoffset];
            }
        }

        pnum = 0;
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

            ulong stronger;
            for (int p = Piece.WELEPHANT + pieceoffset;
                    p >= Piece.WCAT + pieceoffset; p--)
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
                while (pieces)
                {
                    ulong pbit = pieces & -pieces;
                    pieces ^= pbit;
                    ulong p_neighbors = neighbors_of(pbit);

                    int kept_piece;
                    // hostages piece is holding
                    ulong held = p_neighbors & hostages
                        & pos.placement[side^1];
                    while (held && kept_piece < cutpiece)
                    {
                        ulong hbit = held & -held;
                        held ^= hbit;
                        Piece hpiece = pos.pieces[bitindex(hbit)];
                        if (kept_piece < hpiece + pcorr)
                            kept_piece = hpiece + pcorr;
                    }
                    // frames piece is directly framing
                    held = p_neighbors & frames & pos.placement[side^1];
                    if (held && kept_piece < cutpiece)
                    {
                        assert(popcount(held)==1);
                        Piece hpiece = pos.pieces[bitindex(held)];
                        if (kept_piece < hpiece + pcorr)
                            kept_piece = hpiece + pcorr;
                    }
                    // frames piece is framing by keeping a weakframer in
                    held = neighbors_of(p_neighbors & weakframers)
                        & frames & pos.placement[side^1];
                    while (held && kept_piece < cutpiece)
                    {
                        ulong hbit = held & -held;
                        held ^= hbit;
                        Piece hpiece = pos.pieces[bitindex(hbit)];
                        if (kept_piece < hpiece + pcorr)
                            kept_piece = hpiece + pcorr;
                    }
                    // hostages piece is protecting
                    held = TRAPS & p_neighbors;
                    held = (neighbors_of(held)
                            | neighbors_of(neighbors_of(held)))
                        & hostages & pos.placement[side];
                    while (held && kept_piece < cutpiece)
                    {
                        ulong hbit = held & -held;
                        held ^= hbit;
                        Piece hpiece = pos.pieces[bitindex(hbit)];
                        if (kept_piece < hpiece + mcorr)
                            kept_piece = hpiece + mcorr;
                    }
                    // frames piece is pinned to
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
                            if (!(p_neighbors & frames &
                                        pos.placement[side]))
                                threat_map[side^1][tp-2][3] |=
                                    reach_map[pnum][1] & ~freezes[pnum];
                        } else {
                            threat_map[side^1][tp-Piece.WCAT][0] |=
                                reach_map[pnum][0];
                            threat_map[side^1][tp-Piece.WCAT][1] |=
                                reach_map[pnum][2]
                                & ~freezes[pnum] & ~reach_map[pnum][0];
                            threat_map[side^1][tp-Piece.WCAT][2] |=
                                reach_map[pnum][4]
                                & ~freezes[pnum] & ~reach_map[pnum][2];
                        }
                    }
                    ++pnum;
                }
                stronger |= pos.bitBoards[p - enemyoffset];
            }
        }

        // check for rabbit frames
        for (Side side = Side.WHITE; side <= Side.BLACK; side++)
        {
            auto rabbit = Piece.WRABBIT;
            int enemyoffset = -6;
            if (side == Side.BLACK)
            {
                rabbit = Piece.BRABBIT;
                enemyoffset = 6;
            }

            ulong rbits = pos.bitBoards[rabbit] & TRAPS;
            while (rbits)
            {
                ulong rbit = rbits & -rbits;
                rbits ^= rbit;

                ulong holder = neighbors_of(rbit) & pos.placement[side];
                if (popcount(holder) > 1)
                    continue;
                ulong rsteps = rabbit_steps(side, rbit);
                if (!(rsteps & pos.bitBoards[Piece.EMPTY]))
                {
                    score += frame_check(rbit, side, enemyoffset);
                }
            }
        }
        score *= mobility_w;
        debug (mobility)
        {
            logger.log("Mobility and blockade only: {}", score);
        }

        alias NK_TOUCH_DIV = tunables.NK_TOUCH_DIV;
        alias NK_CLOSE_DIV = tunables.NK_CLOSE_DIV;
        alias NK_FAR_DIV = tunables.NK_FAR_DIV;
        alias KEPT_DIV = tunables.KEPT_DIV;
        alias COVER_DIV = tunables.THREAT_COVER_DIV;
        alias COVER_FAR_DIV = tunables.THREAT_COVER_FAR_DIV;
        /*
        static immutable int[] NK_TOUCH_THREAT = [0, -7, -22, -30, -45, -96, -150,
                     7, 22, 30, 45, 96, 150];
        static immutable int[] NK_CLOSE_THREAT = [0, -5, -15, -20, -30, -64, -100,
                     5, 15, 20, 30, 64, 100];
        static immutable int[] NK_FAR_THREAT = [0, -2, -7, -10, -15, -32, -50,
                     2, 7, 10, 15, 32, 50];
        static immutable int[] KP_THREAT = [0, -1, -4, -5, -7, -15, -25,
                     1, 4, 5, 7, 15, 25];
                     */

        double threat_score = 0;
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
                ulong threatened =
                    neighbors_of(threat_map[side][threat_ix][0]) & pieces;
                threat_score += (-piece_value[p + pcorr] / NK_TOUCH_DIV)
                    * popcount(threatened);
                threat_score -= ((-piece_value[p + pcorr] / NK_TOUCH_DIV)
                        * popcount(threatened & cover)) / COVER_DIV;
                debug (mobility)
                {
                    if (threatened)
                    {
                        auto tpop = popcount(threatened);
                        logger.log("NK_TOUCH_THREAT to {} {} for {}",
                                tpop,
                                ".RCDHMErcdhme"[p + pcorr],
                                (-piece_value[p + pcorr] / NK_TOUCH_DIV)
                                * tpop);
                    }
                }
                handled = threatened;
                threatened = neighbors_of(threat_map[side][threat_ix][1])
                    & pieces & ~handled;
                threat_score += (-piece_value[p + pcorr] / NK_CLOSE_DIV)
                    * popcount(threatened);
                threat_score -= ((-piece_value[p + pcorr] / NK_CLOSE_DIV)
                        * popcount(threatened & cover)) / COVER_DIV;
                debug (mobility)
                {
                    if (threatened)
                    {
                        auto tpop = popcount(threatened);
                        logger.log("NK_CLOSE_THREAT to {} {} for {}",
                                 tpop,
                                ".RCDHMErcdhme"[p + pcorr],
                                (-piece_value[p + pcorr] / NK_CLOSE_DIV)
                                * tpop);
                    }
                }
                handled |= threatened;
                cover |= threat_map[side^1][threat_ix][2];
                threatened = neighbors_of(threat_map[side][threat_ix][2])
                    & pieces & ~handled & ~neighbors_of(pos.placement[side]);
                threat_score += (-piece_value[p + pcorr] / NK_FAR_DIV)
                    * popcount(threatened);
                threat_score -= ((-piece_value[p + pcorr] / NK_FAR_DIV)
                        * popcount(threatened & cover)) / COVER_FAR_DIV;
                debug (mobility)
                {
                    if (threatened)
                    {
                        auto tpop = popcount(threatened);
                        logger.log("NK_FAR_THREAT to {} {} for {}",
                                tpop,
                                ".RCDHMErcdhme"[p + pcorr],
                                (-piece_value[p + pcorr] / NK_FAR_DIV)
                                * tpop);
                    }
                }
                handled |= threatened;
                threatened = neighbors_of(threat_map[side][threat_ix][3])
                    & pieces & ~handled;
                threat_score += (-piece_value[p + pcorr] / KEPT_DIV)
                    * popcount(threatened);
                threat_score -= ((-piece_value[p + pcorr] / KEPT_DIV)
                        * popcount(threatened & cover)) / COVER_DIV;
                debug (mobility)
                {
                    if (threatened)
                    {
                        auto tpop = popcount(threatened);
                        logger.log("KEPT_THREAT to {} {} for {}", tpop,
                                ".RCDHMErcdhme"[p + pcorr],
                                (-piece_value[p + pcorr] / KEPT_DIV)
                                * tpop);
                    }
                }
            }
        }
        score += threat_score * threat_w;

        debug (mobility)
        {
            logger.log("Threat only: {}", threat_score * threat_w);
            logger.log("Final mobility and threat: {}", score);
        }

        return cast(int)score;
    }

    int static_trap_eval(Side side, int pop, int fscore)
    {
        active_traps[side] = 0;

        int score = 0;
        if (trap_search.find_captures(pos, side))
        {
            alias victim_per = tunables.VICTIM_PER;
            alias frozen_per = tunables.FROZEN_PER;
            alias multivic_per = tunables.MULTIVIC_PER;
            alias multitrap_per = tunables.MULTITRAP_PER;

            // Each victim once, with its shortest capture and all its traps.
            ulong[16] vic_bit;
            Piece[16] vic_piece;
            int[16] vic_length;
            ulong[16] vic_traps;
            int num_vics = 0;
            for (int i=0; i < trap_search.num_captures; i++)
            {
                ulong vbit = trap_search.captures[i].victim_bit;
                ulong tbit = trap_search.captures[i].trap_bit;
                active_traps[side] |= tbit;
                int v = 0;
                while (v < num_vics && vic_bit[v] != vbit)
                    v++;
                if (v == num_vics)
                {
                    vic_bit[v] = vbit;
                    vic_piece[v] = trap_search.captures[i].victim;
                    vic_length[v] = trap_search.captures[i].length;
                    vic_traps[v] = tbit;
                    num_vics++;
                } else {
                    if (trap_search.captures[i].length < vic_length[v])
                        vic_length[v] = trap_search.captures[i].length;
                    vic_traps[v] |= tbit;
                }
            }

            // The three most valuable victims, the shortest capture first.
            // Ties go to the victim that scores more (frozen, several traps,
            // or a trap no victim before it uses), then to the one with more
            // traps not yet used. Victims still tied then have the same new
            // traps, so the order they are found in can't change the score.
            ulong[3] valuable_vbit;
            Piece[3] valuable_victim;
            int[3] valuable_length;
            ulong[3] valuable_traps;
            ulong picked = 0;
            ulong picked_traps = 0;
            for (int k=0; k < 3; k++)
            {
                int best = -1;
                double best_per = 0;
                for (int v=0; v < num_vics; v++)
                {
                    if (vic_bit[v] & picked)
                        continue;
                    double per = victim_per[k];
                    if (vic_bit[v] & pos.frozen)
                        per += frozen_per;
                    if ((vic_traps[v] & picked_traps) == vic_traps[v])
                        per *= multivic_per;
                    if (popcount(vic_traps[v]) > 1)
                        per *= multitrap_per;
                    if (best == -1 || vic_piece[v] > vic_piece[best]
                            || (vic_piece[v] == vic_piece[best]
                                && (vic_length[v] < vic_length[best]
                                    || (vic_length[v] == vic_length[best]
                                        && (per > best_per
                                            || (per == best_per
                                                && popcount(vic_traps[v] & ~picked_traps)
                                                > popcount(vic_traps[best] & ~picked_traps)))))))
                    {
                        best = v;
                        best_per = per;
                    }
                }
                if (best == -1)
                    break;
                valuable_vbit[k] = vic_bit[best];
                valuable_victim[k] = vic_piece[best];
                valuable_length[k] = vic_length[best];
                valuable_traps[k] = vic_traps[best];
                picked |= vic_bit[best];
                picked_traps |= vic_traps[best];
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
            alias length_per = tunables.LENGTH_PER;
            alias defense_per = tunables.DEFENSE_PER;
            alias max_victim_per = tunables.MAX_VICTIM_PER;
            double defense_mul = (side != pos.side) ? defense_per[pos.stepsLeft] : defense_per[4];
            ulong used_traps = 0;
            ulong future_victims = 0;
            for (int i=0; i < 3; i++)
            {
                if (valuable_victim[i] != 0)
                {
                    double val;
                    if (valuable_length[i])
                    {
                        double per = victim_per[future_victims];
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
                        // Only the side to move's victims get here: its
                        // steps left already cover the capture.
                        val = valuable_value[i] * tunables.NOW_VICTIM_PER;
                    }
                    used_traps |= valuable_traps[i];

                    score = cast(int)(score - (val));
                }
            }

            debug (eval_trap)
            {
                logger.log("trap:\n{}\n{}", "wb"[pos.side^1], pos.to_long_str());
                logger.log("lf {}, lp {}, ip {}", pos.lastfrom, pos.lastpiece, pos.inpush);
                logger.log("score {}, num {}", score, trap_search.num_captures);
                logger.log("mvv {}, svv {}, tvv {}", valuable_victim[0], valuable_victim[1], valuable_victim[2]);
                logger.log("mvl {}, svl {}, tvl {}", valuable_length[0], valuable_length[1], valuable_length[2]);
                for (int i=0; i < trap_search.num_captures; i++)
                {
                    logger.log("v {}, l {}, t {:X}", trap_search.captures[i].victim, trap_search.captures[i].length,
                            trap_search.captures[i].trap_bit);
                }
            }
        } else {
            debug (eval_trap)
            {
                logger.log("no trap:\n{}\n{}", "wb"[pos.side^1], pos.to_long_str());
                logger.log("lf {}, lp {}, ip {}", pos.lastfrom, pos.lastpiece, pos.inpush);
                logger.log("score {}", score);
            }
        }
        trap_search.clear();

        return score;
    }

    double goal_threat()
    {
        // Depends on goal search being done first
        alias GOAL_THREAT = tunables.GOAL_THREAT;
        alias DEFENSE_STEPS = tunables.DEFENSE_STEPS;
        alias DEFENSE_NUM = tunables.DEFENSE_NUM;
        const ulong[] DEFENSE_SECTORS = [0xF8F8F8, 0x1F1F1F];
        const ulong MIDDLE_SECTOR = 0x181818;
        const ulong[] GOAL_RANK = [RANK_8, RANK_1];
        const int[] SIDE_MUL = [1, -1];

        double score = 0;
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
                    // The sectors overlap on the d and e files. The goal
                    // squares are two threats only when no one sector holds
                    // them all, that is when some are on each side of d/e.
                    int[2] sector_defenders;
                    for (int i = 0; i < 2; i++)
                    {
                        ulong sector = DEFENSE_SECTORS[i] << sector_shift;
                        if (goals.goal_squares & sector & GOAL_RANK[s])
                        {
                            sector_defenders[i] = popcount(sector & defenders);
                            if (sector & (safe_traps[s^1] & ~safe_traps[s]))
                                sector_defenders[i] >>= 1;
                            if (goals.goal_squares & sector & ~(MIDDLE_SECTOR << sector_shift))
                                num_threats++;
                        } else {
                            sector_defenders[i] = 8;
                        }
                    }
                    defender_num = sector_defenders[0] < sector_defenders[1] ? sector_defenders[0] : sector_defenders[1];
                } else {
                    ulong sector = 0xFFFFFFUL << sector_shift;
                    defender_num = popcount(defenders & sector);
                    if (sector & (safe_traps[s^1] & ~safe_traps[s]))
                        defender_num >>= 1;
                    num_threats++;
                }
                if (num_threats == 2)
                    dsteps >>= 1;
                score += GOAL_THREAT[extrasteps] * DEFENSE_STEPS[dsteps]
                    * DEFENSE_NUM[defender_num] * SIDE_MUL[s];
                debug (goal_threat) {
                    logger.log("gthreat: sq {:X}", goals.goal_squares);
                    logger.log("gthreat: num {} extra steps {} dsteps {} dnum {}",
                            num_threats, extrasteps, dsteps, defender_num);
                    logger.log("gthreat vals: esteps {} dsteps {} dnum {}",
                            GOAL_THREAT[extrasteps], DEFENSE_STEPS[dsteps],
                            DEFENSE_NUM[defender_num]);
                }
            }
        }
        return score;
    }

    /// Bitmap estimate of each side's goal distance, from bot_Sharp
    /// (Threats::getGoalDistBitmapEst): the steps a rabbit on a square
    /// would need to reach goal, counting own pieces that must step
    /// aside, dominated enemies to push away and squares where it would
    /// freeze, up to 8. Scores each side's nearest rabbit by GOAL_EST.
    ///
    /// The values are for a turn start. Mid-turn, the side to move counts
    /// the steps it has taken as part of the distance (it has that many
    /// fewer this turn), and the other side's values move toward the side
    /// to move's as the steps left to defend run out, reaching them where
    /// the turn would pass.
    int goal_estimate()
    {
        alias GOAL_EST = tunables.GOAL_EST;
        const int[] SIDE_MUL = [1, -1];

        ulong dominated = dominated_pieces();
        int taken = 4 - pos.stepsLeft;
        int score = 0;
        for (Side s = Side.WHITE; s <= Side.BLACK; s++)
        {
            int dist = goal_distance_estimate(s, dominated);
            if (s == pos.side)
                dist += taken;
            int bucket = dist <= 4 ? 0 : (dist <= 6 ? 1 : (dist <= 8 ? 2 : 3));
            if (bucket == 3)
                continue;
            int value = GOAL_EST[bucket];
            if (s != pos.side)
                value += (GOAL_EST[bucket + 3] - value) * pos.stepsLeft / 4;
            score += value * SIDE_MUL[s];
        }
        return score;
    }

    /// Pieces next to a stronger enemy piece.
    private ulong dominated_pieces()
    {
        ulong dominated;
        for (Side s = Side.WHITE; s <= Side.BLACK; s++)
        {
            int my = s == Side.WHITE ? 0 : 6;
            int en = 6 - my;
            ulong stronger; // enemy pieces stronger than piece type t
            for (int t = 6; t >= 1; t--)
            {
                dominated |= pos.bitBoards[my + t] & neighbors_of(stronger);
                stronger |= pos.bitBoards[en + t];
            }
        }
        return dominated;
    }

    private static ulong adj_ns(ulong b)
    {
        return (b << 8) | (b >> 8);
    }

    private static ulong adj_we(ulong b)
    {
        return ((b & NOT_H_FILE) >> 1) | ((b & NOT_A_FILE) << 1);
    }

    /// The nearest rabbit of side pla's estimated distance (see
    /// goal_estimate), 9 when more than 8.
    private int goal_distance_estimate(Side pla, ulong dominated)
    {
        alias adj = neighbors_of;
        Side opp = cast(Side)(pla ^ 1);
        int po = pla == Side.WHITE ? 0 : 6;
        ulong plas = pos.placement[pla];
        ulong opps = pos.placement[opp];
        ulong empty = pos.bitBoards[Piece.EMPTY];
        ulong open = adj(empty);
        ulong open_we = adj_we(empty);
        ulong opp_rab = pos.bitBoards[Piece.WRABBIT + 6 - po];
        ulong dominatey = TRAPS | adj(opps & ~opp_rab);
        ulong freezy = ~adj(plas) & dominatey;
        ulong pushable = opps & dominated & ~dominatey; // dominated, safe to push from
        // squares within two steps of an unfrozen non-rabbit of pla's
        ulong helpers = adj(plas & ~pos.bitBoards[Piece.WRABBIT + po] & ~pos.frozen);
        helpers |= adj(helpers);

        // g[i]: squares a rabbit could goal from in i steps; r[i]: squares
        // reachable in i more steps from the current g.
        ulong[9] g;
        ulong[9] r;
        g[0] = pla == Side.WHITE ? RANK_8 : RANK_1;
        r[1] = adj_ns(g[0] & (empty | (plas & open_we)));
        r[2] = adj_ns(g[0] & plas & open_we & ~dominated);
        r[3] = adj_ns(g[0] & (plas | (pushable & open_we)));
        r[4] = adj_ns(g[0] & opp_rab & helpers & open_we);
        for (int i = 1; i <= 8; i++)
        {
            g[i] = g[i - 1] | (~freezy & r[i]);
            if (i >= 2)
                g[i] |= r[i - 1] & helpers;
            if (i >= 3)
                g[i] |= r[i - 2];
            if (i < 8)
                r[i + 1] |= adj(g[i] & (empty | (plas & open)));
            if (i + 2 <= 8)
                r[i + 2] |= adj(g[i] & plas);
            if (i + 3 <= 8)
                r[i + 3] |= adj(g[i] & opps & dominated & ~dominatey);
            if (i + 4 <= 8)
                r[i + 4] |= adj(g[i] & opp_rab & helpers);
        }

        ulong rabbits = pos.bitBoards[Piece.WRABBIT + po];
        for (int i = 0; i <= 8; i++)
            if (rabbits & g[i])
                return i;
        return 9;
    }

    /// GOAL_FIVE for the side to move at the start of its turn when it
    /// can goal in 5 steps (the other side passing): one step, then a
    /// goal the 4-step tree finds from a fresh turn. Needs goals set for
    /// pos with no goal this turn. Positions whose goal distance estimate
    /// is over 6 are skipped: in positions from games that is 77% of them,
    /// and 0.13% of the 5-step goals.
    int goal_five()
    {
        if (pos.stepsLeft != 4 || goals.shortest[pos.side] != goals.NOT_FOUND
                || goal_distance_estimate(pos.side, dominated_pieces()) > 6)
            return 0;
        if (five_search is null)
            five_search = new GoalSearchDT();
        Side s = pos.side;
        StepList steps = StepList.allocate();
        scope (exit) StepList.free(steps);
        pos.get_steps(steps);
        bool found = false;
        foreach (Step st; steps.getsteps())
        {
            if (st.frombit == INV_STEP || st.push)
                continue;
            Position np = pos.dup;
            np.do_step(st);
            np.do_step(NULL_STEP); // ends the turn
            np.do_step(NULL_STEP); // the other side passes
            five_search.set_start(np);
            five_search.find_goals();
            Position.free(np);
            if (five_search.shortest[s] != five_search.NOT_FOUND)
            {
                found = true;
                break;
            }
        }
        return found ? (s == Side.WHITE ? tunables.GOAL_FIVE : -tunables.GOAL_FIVE) : 0;
    }

    int material_values(int pop)
    {
        int score = fame.score(pop);
        for (Piece piece=Piece.WRABBIT; piece <= Piece.BELEPHANT; piece++)
        {
            int cur_num = pop2count(pop, piece);
            if (cur_num)
            {
                int mpop = count2pop(pop, piece, cur_num-1);
                int mscore = fame.score(mpop);
                piece_value[piece] = score - mscore;
            } else {
                int mpop = count2pop(pop, piece, 1);
                int mscore = fame.score(mpop);
                piece_value[piece] = mscore - score;
            }
            debug (material_value)
            {
                logger.log("Piece {} has value {}",
                        ".RCDHMErcdhme"[piece], piece_value[piece]);
            }
        }
        return score;
    }

    int static_eval(Position pos)
    {
        // check if the score is cached for this position. Either way
        // goals.shortest is left set for pos, which the quiescence search
        // reads next.
        SCNode* sc_entry = sc_cache.get(pos);
        if (sc_entry.zobrist == pos.zobrist)
        {
            goals.shortest[0] = sc_entry.shortest[0];
            goals.shortest[1] = sc_entry.shortest[1];
            return sc_entry.score;
        }

        int score;
        if (pos.is_endstate() && pos.is_goal(cast(Side)(pos.side^1)))
        {
            // the only time static eval should end up called with a endstate
            // is when there is an opposing rabbit on the goal line that might
            // still get pulled back off before the end of the turn
            score = -(WIN_SCORE - pos.stepsLeft);
            goals.shortest[pos.side] = goals.NOT_FOUND;
            goals.shortest[pos.side^1] = 0;
            sc_entry.set(pos.zobrist, score, goals.shortest);
            return score;
        }

        this.pos = pos;
        goals.set_start(pos);
        goals.find_goals();
        if ((goals.shortest[pos.side] != goals.NOT_FOUND)
                && goals.shortest[pos.side] <= pos.stepsLeft)
        {
            score = WIN_SCORE - goals.shortest[pos.side];
            sc_entry.set(pos.zobrist, score, goals.shortest);
            return score;
        }

        int pop = population(pos);
        int fscore = material_values(pop); // first pawn worth ~196
                                     // only a pawn left ~31883
        score = fscore;
        score = cast(int)(score + (static_trap_eval(cast(Side)(pos.side^1), pop, fscore) * static_otrap_w));
        score = cast(int)(score + (static_trap_eval(pos.side, pop, fscore) * static_strap_w));

        score = cast(int)(score + (trap_safety() * tsafety_w));
        score = cast(int)(score + (piece_strength() * pstrength_w));
        score = cast(int)(score + (on_trap() * ontrap_w));
        score += mobility();
        score = cast(int)(score + (rabbit_strength()));
        score = cast(int)(score + (rabbit_wall() * rwall_w));
        score = cast(int)(score + (rabbit_open() * ropen_w));
        score = cast(int)(score + (rabbit_home() * rhome_w));
        score = cast(int)(score + (frozen_pieces() * frozen_w));
        score = cast(int)(score + (map_elephant() * map_e_w));
        score = cast(int)(score + (goal_threat() * goal_w));
        if (goalest_w != 0)
            score = cast(int)(score + (goal_estimate() * goalest_w));
        if (goal5_w != 0)
            score = cast(int)(score + (goal_five() * goal5_w));

        if (pos.side == Side.BLACK)
            score = -score;

        // clamp the evaluation to be less than a win
        score = (score < MAX_EVAL_SCORE) ? ((score > -(MAX_EVAL_SCORE)) ? score : -(MAX_EVAL_SCORE)) : MAX_EVAL_SCORE;

        // Enter the score into the cache
        sc_entry.set(pos.zobrist, score, goals.shortest);
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
            logger.log("Found goal in {} steps", goals.shortest[pos.side]);
            return WIN_SCORE - goals.shortest[pos.side];
        }

        int pop = population(pos);
        int fscore = material_values(pop); // first pawn worth ~196
                                     // only a pawn left ~31883
        logger.log("Fame {}", fscore);
        int score = fscore;
        int pscore = fscore;
        score = cast(int)(score + (static_trap_eval(cast(Side)(pos.side^1), pop, fscore) * static_otrap_w));
        logger.log("static otrap {}", score-pscore);
        pscore = score;
        score = cast(int)(score + (static_trap_eval(pos.side, pop, fscore) * static_strap_w));
        logger.log("static strap {}", score-pscore);
        pscore = score;

        score = cast(int)(score + (trap_safety() * tsafety_w));
        logger.log("trap safety {}", score-pscore);
        pscore = score;
        score = cast(int)(score + (piece_strength() * pstrength_w));
        logger.log("piece strength {}", score-pscore);
        pscore = score;
        score = cast(int)(score + (on_trap() * ontrap_w));
        logger.log("on trap {}", score-pscore);
        pscore = score;
        score += mobility();
        logger.log("mobility {}", score-pscore);
        pscore = score;
        score = cast(int)(score + (rabbit_strength()));
        logger.log("rabbit strength {}", score-pscore);
        pscore = score;
        score = cast(int)(score + (rabbit_wall() * rwall_w));
        logger.log("rabbit wall {}", score-pscore);
        pscore = score;
        score = cast(int)(score + (rabbit_open() * ropen_w));
        logger.log("rabbit open {}", score-pscore);
        pscore = score;
        score = cast(int)(score + (rabbit_home() * rhome_w));
        logger.log("rabbit home {}", score-pscore);
        pscore = score;
        score = cast(int)(score + (frozen_pieces() * frozen_w));
        logger.log("frozen pieces {}", score-pscore);
        pscore = score;
        score = cast(int)(score + (map_elephant() * map_e_w));
        logger.log("map elephant {}", score-pscore);
        pscore = score;
        score = cast(int)(score + (goal_threat() * goal_w));
        logger.log("goal threat {}", score-pscore);
        if (goalest_w != 0)
        {
            pscore = score;
            score = cast(int)(score + (goal_estimate() * goalest_w));
            logger.log("goal estimate {}", score-pscore);
        }
        if (goal5_w != 0)
        {
            pscore = score;
            score = cast(int)(score + (goal_five() * goal5_w));
            logger.log("goal in five {}", score-pscore);
        }

        if (pos.side == Side.BLACK)
            score = -score;

        // clamp the evaluation to be less than a win
        score = (score < MAX_EVAL_SCORE) ? ((score > -(MAX_EVAL_SCORE)) ? score : -(MAX_EVAL_SCORE)) : MAX_EVAL_SCORE;
        logger.log("Final (clamped) score {}", score);
        logger.info("score cr {}", cast(int)(score/1.96));
        return score;
    }
}
