
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
import position;

const char[] BOT_NAME = "OpFor";
const char[] BOT_AUTHOR = "Janzert";

const int START_SEARCH_NODES = 100000;

int trap_safety(Position pos)
{
    const int BOTH_SAFE = 1;
    const int HOME_CONTROL = 5;
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
    const int ON_TRAP[13] = [0, -10, -15, -19, -31, -56, -132, 10, 15, 19, 31, 56, 132];
    const int PINNED[13] = [0, 0, -4, -8, -14, -25, -59, 0, 4, 8, 14, 25, 59];
    const int FRAMER[13] = [0, 0, -1, -2, -4, -8, -19, 0, 1, 2, 4, 8, 19];

    int score = 0;
    ulong occupied_traps = ~pos.bitBoards[Piece.EMPTY] & TRAPS;
    while (occupied_traps)
    {
        ulong tbit = occupied_traps & -occupied_traps;
        occupied_traps ^= tbit;
        bitix tix = bitindex(tbit);
        Piece tpiece = pos.pieces[tix];
        score += ON_TRAP[tpiece];

        Side tside = (tpiece > Piece.WELEPHANT) ? Side.BLACK : Side.WHITE;
        int pieceoffset = (tside == Side.WHITE) ? 6 : -6;
        ulong tneighbors = neighbors_of(tbit);
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
                    if (tpiece + pieceoffset > pos.pieces[eix])
                        epiece = pos.strongest[tside^1][eix];
                    else
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
         2, 3, 3, 5, 5, 3, 3, 2,
         3, 4, 5, 5, 5, 5, 4, 3,
         3, 4, 5, 5, 5, 5, 4, 3,
         2, 3, 3, 5, 5, 3, 3, 2,
         1, 2, 2, 4, 4, 2, 2, 1,
         0, 1, 1, 2, 2, 1, 1, 0];

    int score = 0;
    if (pos.bitBoards[Piece.WELEPHANT])
        score += CENTRAL_MAP[bitindex(pos.bitBoards[Piece.WELEPHANT])];
    if (pos.bitBoards[Piece.BELEPHANT])
        score -= CENTRAL_MAP[bitindex(pos.bitBoards[Piece.BELEPHANT])];

    return score;
}


int frozen_pieces(Position pos)
{
    const int[13] frozen_penalty = [0, -2, -4, -5, -10, -25, 0,
                              2, 4, 5, 10, 25, 0];
    int score = 0;
    for (int p=1; p < 12; p++)
    {
        score += popcount(pos.bitBoards[p] & pos.frozen) * frozen_penalty[p];
    }
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
    const int[8][2] OPEN_FILE = [[2, 2, 2, 3, 5, 10, 20, 0], [0, -20, -10, -5, -3, -2, -2, -2]];
    const int[8][2] OPEN_ADJ = [[2, 2, 3, 20, 30, 40, 60, 0], [0, -60, -40, -30, -20, -3, -2, -2]];

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
    
    int score = 0;
    for (Side side = Side.WHITE; side <= Side.BLACK; side++)
    {
        Piece rpiece = (side == Side.WHITE) ? Piece.WRABBIT : Piece.BRABBIT;
        ulong rabbits = pos.bitBoards[rpiece];
        score += popcount(side_rank[side][0] & rabbits) * 2 * side_mul[side];
        score += popcount(side_rank[side][1] & rabbits) * side_mul[side];
    }

    return score;
}

real rabbit_strength(Position pos, GoalSearch goals, real weak_w, real strong_w)
{
    const static int[][] pieceval = [[0, 0, 45, 60, 150, 200, 300,
          0, -45, -60, -150, -200, -300],
          [0, 0, -45, -60, -150, -200, -300,
          0, 45, 60, 150, 200, 300]];
    const static int[] distval = [100, 100, 100, 90, 70,
          30, 20, 15, 10, 5, 4, 3, 2, 1, 0, 0];
    const static real[][] rankval = [[0, 0, 0, 0.2, 0.5, 1.0, 1.2, 0],
          [0, -1.2, -1.0, -0.5, -0.2, 0, 0, 0]];
    const static real[] goalval = [1.0,
          1.0, 1.0, 1.0, 1.0,
          1.0, 1.0, 0.9, 0.9,
          0.8, 0.8, 0.7, 0.7,
          0.6, 0.6, 0.5, 0.5];
    const static real[] weakgoal = [0,
          0, 0, 0, 0,
          0.1, 0.1, 0.2, 0.2,
          0.4, 0.4, 0.6, 0.6,
          0.8, 0.8, 0.9, 1];
    const static int[][] weakval = [[0, 0, -15, -30, -30, -30, -30, 0], 
         [0, 30, 30, 30, 30, 15, 0, 0]];
    const static int[] rforward = [8, -8];

    int wscore = 0;
    real sscore = 0;
    ulong allpieces = (pos.placement[Side.WHITE] | pos.placement[Side.BLACK])
        & ~pos.bitBoards[Piece.WRABBIT] & ~pos.bitBoards[Piece.BRABBIT]
        & ~pos.frozen;
    Piece[32] pieces;
    bitix[32] pixs;
    int num_pieces;
    while (allpieces)
    {
	ulong pbit = allpieces & -allpieces;
	allpieces ^= pbit;
	bitix pix = bitindex(pbit);

	pieces[num_pieces] = pos.pieces[pix];
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

            int power = 0;
            for (int i=0; i < num_pieces; i++)
            {
                power += pieceval[s][pieces[i]] * distval[taxicab_dist[pixs[i]][rix+rforward[s]]];
            }

            int goalsteps = goals.board_depth[rix];
            goalsteps = (goalsteps < 16) ? goalsteps : 16;

            if (power <= 0)
            {
                wscore += weakval[s][rix/8] * weakgoal[goalsteps];
            } else {
                real rv = rankval[s][rix/8];
                real rval = power * rv * goalval[goalsteps];
                if (rbit & TRAPS)
                    rval /= 2;
                sscore += rval;
            }
        }
    }

    return (wscore * weak_w) + (sscore * strong_w);
}

int piece_strength(Position pos)
{
    const static int[] pieceval = [0, 0, 4, 6, 15, 20, 30,
          0, -4, -6, -15, -20, -30];
    const static int[] distval = [100, 100, 100, 90, 70,
          30, 20, 15, 10, 5, 4, 3, 2, 1, 0, 0];
    
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

            for (int i=0; i < num_stronger; i++)
            {
                power += pieceval[stronger[i]] * distval[taxicab_dist[pix][sixs[i]]];
            }
        }
        score += power * pieceval[p];
    }

    return score;
}


class ScoreSearch : ABSearch
{
    this()
    {
        super();
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
    
    real map_e_w = 10;
    real tsafety_w = 0;
    real ontrap_w = 3;
    real frozen_w = 10;
    real rwall_w = 1;
    real ropen_w = 50;
    real rhome_w = 0;
    real rweak_w = 1;
    real rstrong_w = 0.1;
    real pstrength_w = 0.00001;
    real goal_w = 10;
    real static_trap_w = 1;
    real random_w = 0;
    int max_qdepth = -40;
    int do_qsearch = 1;
    
    this()
    {
        super();
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
            case "eval_random":
                random_w = toReal(value);
                break;
            case "eval_quiesce":
                do_qsearch = toInt(value);
                break;
            case "eval_qdepth":
                max_qdepth = 0 - toInt(value);
                break;
            case "eval_static_trap":
                static_trap_w = toReal(value);
                break;
            default:
                handled = super.set_option(option, value);
        }
        return handled;
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
        int score;
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

        //writefln("%s %d\n%s", "wb"[pos.side], depth, pos.to_long_str());
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

        if (depth < max_qdepth)
            return score;

        if (score >= beta)
            return score;
        if (score > alpha)
        {
            alpha = score;
            sflag = SType.EXACT;
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

    int static_trap_eval(Position pos, Side side, int score)
    {
        if (trap_search.find_captures(pos, side))
        {
            int pop = population(pos);
            
            int[3] valuable_vid;
            Piece[3] valuable_victim;
            int[3] valuable_length;
            for (int i=0; i < trap_search.num_captures; i++)
            {
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

                int vid = bitindex(trap_search.captures[i].victim_bit) | (tid << 8);
                Piece vic = trap_search.captures[i].victim;
                int len = trap_search.captures[i].length;
                if (vid != valuable_vid[0]
                        && (vic > valuable_victim[0]
                            || (vic == valuable_victim[0]
                                && len < valuable_length[0])))
                {
                    int tvid = valuable_vid[0];
                    Piece tvic = valuable_victim[0];
                    int tlen = valuable_length[0];
                    valuable_vid[0] = vid;
                    valuable_victim[0] = vic;
                    valuable_length[0] = len;
                    vid = tvid;
                    vic = tvic;
                    len = tlen;
                } else if (vid == valuable_vid[0])
                {
                    if (valuable_length[0] > len)
                    {
                        valuable_length[0] = len;
                    }
                    vid = 0;
                    vic = Piece.EMPTY;
                    len = 0;
                }
                if (vid != valuable_vid[1]
                        && (vic > valuable_victim[1]
                            || (vic == valuable_victim[1]
                                && len < valuable_length[1])))
                {
                    int tvid = valuable_vid[1];
                    Piece tvic = valuable_victim[1];
                    int tlen = valuable_length[1];
                    valuable_vid[1] = vid;
                    valuable_victim[1] = vic;
                    valuable_length[1] = len;
                    vid = tvid;
                    vic = tvic;
                    len = tlen;
                } else if (vid == valuable_vid[1])
                {
                    if (valuable_length[1] > len)
                    {
                        valuable_length[1] = len;
                    }
                    vid = 0;
                    vic = Piece.EMPTY;
                    len = 0;
                }
                if (vid != valuable_vid[0]
                        && (vic > valuable_victim[0]
                            || (vic == valuable_victim[0]
                                && len < valuable_length[0])))
                {
                    int tvid = valuable_vid[2];
                    Piece tvic = valuable_victim[2];
                    int tlen = valuable_length[2];
                    valuable_vid[2] = vid;
                    valuable_victim[2] = vic;
                    valuable_length[2] = len;
                    vid = tvid;
                    vic = tvic;
                    len = tlen;
                } else if (vid == valuable_vid[2])
                {
                    if (valuable_length[2] > len)
                    {
                        valuable_length[2] = len;
                    }
                    vid = 0;
                    vic = Piece.EMPTY;
                    len = 0;
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
                    && valuable_victim[1] > valuable_victim[2])
            {
                int l = valuable_length[1];
                valuable_length[1] = valuable_length[2];
                valuable_length[2] = l;
            }

            int[3] valuable_value;
            for (int i=0; i < 3; i++)
            {
                if (valuable_length[i] != 0)
                {
                    int vcnt = pop2count(pop, valuable_victim[i]) - 1;
                    int vpop = pop & ~(pop_mask[valuable_victim[i]] << pop_offset[valuable_victim[i]]);
                    vpop |= vcnt << pop_offset[valuable_victim[i]];
                    valuable_value[i] = score - fame.score(vpop);
                }
            }

            const static real[] victim_per = [0.5, 0.7, 0.9];
            const static real[] length_per = [1.0,
                1.0, 1.0, 0.9, 0.9,
                0.6, 0.5, 0.4, 0.3,
                0.1, 0.1, 0.05, 0.05];
            const static real[] steps_per = [1.0, 0.75, 0.56, 0.42, 0.31];
            for (int i=0; i < 3; i++)
            {
                if (valuable_length[i] != 0)
                {
                    int len = (valuable_length[i] < 12) ? valuable_length[i] : 12;
                    int val = cast(int)(((valuable_value[i] * victim_per[i]) * length_per[len]) * steps_per[pos.stepsLeft]);
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

        const int[17] GOAL_THREAT = [30000, 20000, 20000, 15000, 10000,
              8000, 6000, 4000, 2000,
              1000, 500, 200, 50,
              20, 10, 7, 5];

        int score = 0;
        if (goal_searcher.goals_found[pos.side])
        {
            int extrasteps = (goal_searcher.goal_depth[pos.side][0] - pos.stepsLeft)+8;
            extrasteps = (extrasteps < 16) ? extrasteps : 16;
            score += GOAL_THREAT[extrasteps] * goal_w;
        }
        if (goal_searcher.goals_found[pos.side^1])
        {
            int togoal = goal_searcher.goal_depth[pos.side^1][0] + (pos.stepsLeft << 1);
            togoal = (togoal < 16) ? togoal : 16;
            score -= GOAL_THREAT[togoal] * goal_w;
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
        int score = fame.score(pop); // first pawn worth ~196
                                     // only a pawn left ~31883
        score += static_trap_eval(pos, cast(Side)(pos.side^1), score) * static_trap_w;

        score += piece_strength(pos) * pstrength_w;
        score += rabbit_strength(pos, goal_searcher, rweak_w, rstrong_w);
        score += rabbit_wall(pos) * rwall_w;
        score += rabbit_open(pos) * ropen_w;
        // score += rabbit_home(pos) * rhome_w; No improvement
        score += frozen_pieces(pos) * frozen_w;
        score += map_elephant(pos) * map_e_w;
        //score += trap_safety(pos) * tsafety_w; No weight tested showed improvement
        score += on_trap(pos) * ontrap_w;
        if (random_w)
            score += (rand()%100) * random_w;

        if (pos.side == Side.BLACK)
            score = -score;

        score += goal_threat(pos);

        // clamp the evaluation to be less than a win
        score = (score < WIN_SCORE-10) ? ((score > -(WIN_SCORE-10)) ? score : -(WIN_SCORE-10)) : WIN_SCORE-10;
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
    PositionNode next_pos;
    int depth;
    int best_score;
    int best_guess;

    bool in_step;
    int last_score;
    PositionNode last_best;

    int max_depth;

    const static int BOOK_SIZE = 1000000;
    PositionRecord[] opening_book;
    bool position_record = false;

    bool use_mtdf = false;

    this()
    {
        searcher = new FullSearch();
        //searcher = new ScoreSearch();
        in_step = false;
        max_depth = -1;
        searcher.tournament_rules = false;
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
            case "use_mtdf":
                use_mtdf = cast(bool)toInt(value);
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
            }
            next_pos = pos_list;
            best_score = MIN_SCORE;
            best_guess = MIN_SCORE;
            depth = 0;
            searcher.prepare();
            state = EngineState.SEARCHING;
        }
    }

    void search(int num_nodes)
    {
        in_step = true;
        ulong stop_node = searcher.nodes_searched + num_nodes;
        while (searcher.nodes_searched < stop_node)
        {
            Position pos = next_pos.pos;
            searcher.nullmove = pos.dup;
            searcher.nullmove.do_step(NULL_STEP);
            int score;
            if (use_mtdf)
            {
                score = -searcher.mtdf(pos, depth, -best_guess, -best_score);
            } else {
                score = -searcher.alphabeta(pos, depth, MIN_SCORE, -best_score);
            }
            Position.free(searcher.nullmove);
            searcher.nodes_searched++;

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
                    writefln("Saw position in book added %d to %d score.", val, score);
                }
            }

            if (score > best_score)
            {
                best_score = score;
                best_guess = score;
                
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
            }

            if (next_pos.next !is null)
            {
                next_pos = next_pos.next;
            } else {
                depth++;
                last_score = best_score;
                last_best = pos_list;
                best_score = MIN_SCORE;
                next_pos = pos_list;
                in_step = false;
                break;
            }
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
        while (n.zobrist == pos.zobrist 
                && (n.beststep.frombit != 0 || n.beststep.tobit != 0))
        {
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
        next_pos = null;
        pos_list = null;
        last_best = null;
        last_score = MIN_SCORE;
        best_score = MIN_SCORE;
        searcher.cleanup();
    }

}

int main(char[][] args)
{
    char[] ip = "127.0.0.1";
    ushort port = 40007;

    d_time report_interval = 60 * std.date.TicksPerSecond;
    d_time nextreport = 0;
    int report_depth = 0;

    ServerInterface server = new ServerInterface(new SocketServer(ip, port),
            BOT_NAME, BOT_AUTHOR);
    writefln("Connected to server %s:%d", ip, port);
    Engine engine = new Engine();

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
            writefln("Received unknown command: %s", e.command);
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
                    writefln("Exiting by server command.");
                    return 0;
                case ServerCmd.CmdType.NEWGAME:
                    writefln("Starting new game.");
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
                    writefln("Starting search.");
                    writefln("%s\n%s", "wb"[engine.position.side], engine.position.to_long_str);
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
                    writefln("set position\n%s\n%s", 
                            "wb"[engine.position.side], 
                            engine.position.to_long_str());
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.SETOPTION:
                    OptionCmd scmd = cast(OptionCmd)server.current_cmd;
                    switch (scmd.name)
                    {
                        case "depth":
                            if (scmd.value == "infinite")
                            {
                                engine.max_depth = -1;
                                server.info("log Search depth set to infinite");
                            } else {
                                int depth = toInt(scmd.value);
                                engine.max_depth = (depth > 3) ? depth - 4 : 0;
                                server.info(format("log Search depth set to %d", engine.max_depth+4));
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
                        server.info(format("log Sending forced win move in %.2f seconds.", seconds));
                    }
                }
                real average = 0;
                if (search_num)
                {
                    average = (cast(real)search_time / TicksPerSecond) / search_num;
                }
                real max_seconds = cast(real)search_max / TicksPerSecond;
                server.info(format("log Searched %d nodes, %.0f nps, %d tthits.",
                        engine.searcher.nodes_searched, engine.searcher.nodes_searched/seconds, engine.searcher.tthits));
                writefln("Finished search in %.2f seconds, average %.2f, max %.2f.", seconds, average, max_seconds);
                writefln("Sending move %s", engine.bestmove);
                if (!pondering)
                {
                    server.bestmove(engine.bestmove);
                }
                engine.cleanup_search();
                writefln("Positions allocated %d, in reserve %d (%.0fMB).",
                        Position.allocated, Position.reserved, Position.reserve_size);
                writefln("PNodes allocated %d, in reserve %d.", PositionNode.allocated, PositionNode.reserved);
                engine.state = EngineState.IDLE;
                break;
            case EngineState.SEARCHING:
                PositionNode cur_best = engine.pos_list;
                if (engine.searcher.nodes_searched && (length > (TicksPerSecond/2)))
                {
                    int chunk = engine.searcher.nodes_searched / (length / (TicksPerSecond /2));
                    engine.search(chunk);
                } else {
                    engine.search(START_SEARCH_NODES);
                }
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
                        || (tc_permove && (now >= ((tc_max_search * TicksPerSecond) + move_start))))
                    {
                        engine.set_bestmove();
                        engine.state = EngineState.MOVESET;
                    } else if (tc_permove && (now > ((tc_min_search * TicksPerSecond) + move_start)))
                    {
                        server.info("log Min search time reached");
                        d_time decision_length = now - last_decision_change;
                        d_time move_length = now - move_start;
                        d_time time_left = (move_start + (tc_max_search * TicksPerSecond)) - now;
                        if (decision_length < move_length * (1.0/tc_confidence_denom)
                                && decision_length < time_left * (1.0/tc_time_left_denom))
                        {
                            server.info(format("log move_length %d, decision_length %d, time_left %d", 
                                        (move_length / TicksPerSecond),
                                        (decision_length / TicksPerSecond),
                                        (time_left / TicksPerSecond)));
                            real tc_cd = 1.0 / (tc_confidence_denom-1);
                            real tc_tld = 1.0 / (tc_time_left_denom-1);
                            d_time length_cutoff = cast(d_time)((last_decision_change - move_start) * tc_cd) + last_decision_change;
                            d_time reserve_cutoff = cast(d_time)(((move_start + (tc_max_search * TicksPerSecond))
                                        - last_decision_change) * tc_tld) + last_decision_change;
                            d_time end_search = (length_cutoff < reserve_cutoff) ? length_cutoff : reserve_cutoff;
                            end_search += cast(d_time)(0.1 * TicksPerSecond);
                            tc_min_search = (end_search - move_start) / TicksPerSecond;
                            server.info(format("log next min_search set to %d", tc_min_search));
                        } else {
                            server.info(format("log last decision change %d seconds ago", decision_length / TicksPerSecond));
                            engine.set_bestmove();
                            engine.state = EngineState.MOVESET;
                        }
                    }
                }
                if (now > nextreport 
                        || engine.depth > report_depth 
                        || cur_best !is engine.pos_list)
                {
                    int depth = engine.in_step ? engine.depth+4 : engine.depth+3;
                    server.info(format("depth %d", depth));
                    server.info(format("time %d", (now-search_start)/TicksPerSecond));
                    server.info(format("nodes %d", engine.searcher.nodes_searched));
                    if (engine.in_step)
                    {
                        server.info(format("score cr %d", cast(int)(engine.best_score / 1.96)));
                    } else {
                        server.info(format("score cr %d", cast(int)(engine.last_score / 1.96)));
                    }
                    StepList bestline = engine.get_bestline();
                    server.info(format("pv %s", bestline.to_move_str(engine.position)));
                    StepList.free(bestline);
                    check_num = 0;
                    nextreport = now + report_interval;
                    report_depth = engine.depth;
                }
                break;
            default:
                break;
        }
    }
}


