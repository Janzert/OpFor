
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
    const int AWAY_CONTROL = 7;

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
    const int ON_TRAP[13] = [0, -1, -2, -4, -8, -15, -20, 1, 2, 4, 8, 15, 20];
    const int PINNED[13] = [0, -3, -8, -10, -20, -40, -55, 3, 8, 10, 20, 40, 55];
    const int FRAMED[13] = [0, -5, -7, -15, -30, -80, 150, 5, 7, 15, 30, 80, 150];

    int score = 0;
    ulong occupied_traps = pos.placement[Side.WHITE] & TRAPS;
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
            if (!(tneighbors & pos.bitBoards[Piece.EMPTY]))
            {
                ulong eneighbors = tneighbors ^ fneighbors;
                bool framed = true;
                while (eneighbors)
                {
                    ulong ebit = eneighbors & -eneighbors;
                    eneighbors ^= ebit;
                    bitix eix = bitindex(ebit);
                    if (tpiece + pieceoffset > pos.pieces[eix]
                            && (neighbors_of(ebit) & pos.bitBoards[Piece.EMPTY]))
                    {
                        framed = false;
                        break;
                    }
                }
                if (framed)
                    score += FRAMED[tpiece];
            }
        }
    }
    return score;
}

int central_elephant(Position pos)
{
    const int CENTRAL_E_BONUS = 6;
    const ulong emap = 0x0000183C3C180000UL;

    int score = 0;
    if (emap & pos.bitBoards[Piece.WELEPHANT])
        score += CENTRAL_E_BONUS;
    if (emap & pos.bitBoards[Piece.BELEPHANT])
        score -= CENTRAL_E_BONUS;

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
            ulong ladjacent = rbit << 1 & rbit << 9 & rbit >> 7;
            if (ladjacent & rcandd)
            {
                score += BLOCKING_BONUS[s];
            }
            ulong radjacent = rbit >> 1 & rbit >> 9 & rbit << 7;
            if (radjacent & rcandd)
            {
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
                int rank = rix/8;
                score += NORABBIT_FILE[Side.WHITE][rank];
                if (!(pos.placement[Side.BLACK] & mask))
                {
                    score += OPEN_FILE[Side.WHITE][rank];
                }
                ulong adj_mask = 0;
                if (file != 0)
                    adj_mask = H_FILE << (rix+7);
                if (file != 7)
                    adj_mask |= H_FILE << (rix+9);
                adj_mask &= NOT_RANK_8;
                if (!(pos.bitBoards[Piece.BRABBIT] & adj_mask))
                {
                    score += NORABBIT_ADJ[Side.WHITE][rank];
                    if (!(pos.placement[Side.BLACK] & adj_mask))
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
                int rank = rix / 8;
                score += NORABBIT_FILE[Side.BLACK][rank];
                if (!(pos.placement[Side.BLACK] & rmask))
                {
                    score += OPEN_FILE[Side.BLACK][rank];
                }
                ulong adj_mask = 0;
                if (file != 0)
                    adj_mask = A_FILE >> ((63+9) - rix);
                if (file != 7)
                    adj_mask |= A_FILE >> ((63+7) - rix);
                adj_mask &= NOT_RANK_1;
                if (!(pos.bitBoards[Piece.WRABBIT] & adj_mask))
                {
                    score += NORABBIT_ADJ[Side.BLACK][rank];
                    if (!(pos.placement[Side.WHITE] & adj_mask))
                    {
                        score += OPEN_ADJ[Side.BLACK][rank];
                    }
                }
            }
        }
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

class FullSearch : ABSearch
{
    GoalSearch goal_searcher;
    real tsafety_w = 2;
    real centralel_w = 1;
    real frozen_w = 1;
    real ontrap_w = 1;
    real rwall_w = 1;
    real ropen_w = 1;
    real goal_w = 1;
    
    this()
    {
        super();
        goal_searcher = new GoalSearch(14);
    }
    
    bool set_option(char[] option, char[] value)
    {
        bool handled = false;
        switch (option)
        {
            case "eval_tsafety":
                tsafety_w = toReal(value);
                handled = true;
                break;
            case "eval_centralel":
                centralel_w = toReal(value);
                handled = true;
                break;
            case "eval_frozen":
                frozen_w = toReal(value);
                handled = true;
                break;
            case "eval_ontrap":
                ontrap_w = toReal(value);
                handled = true;
                break;
            case "eval_rwall":
                rwall_w = toReal(value);
                handled = true;
                break;
            case "eval_ropen":
                ropen_w = toReal(value);
                handled = true;
                break;
            case "eval_goal":
                goal_w = toReal(value);
                handled = true;
                break;
            default:
                handled = super.set_option(option, value);
        }
        return handled;
    }

    int eval(Position pos)
    {
        int score = cast(int)fastFAME(pos, 0.1716); // first pawn worth ~196
                                                    // only a pawn left ~31883
        score += trap_safety(pos) * tsafety_w;
        score += central_elephant(pos) * centralel_w;
        score += frozen_pieces(pos) * frozen_w;
        score += on_trap(pos) * ontrap_w;
        score += rabbit_wall(pos) * rwall_w;
        score += rabbit_open(pos) * ropen_w;

        if (pos.side == Side.BLACK)
            score = -score;

        const int[17] GOAL_THREAT = [30000, 20000, 20000, 15000, 10000,
              8000, 6000, 4000, 2000,
              1000, 500, 200, 50,
              20, 10, 7, 5];
        goal_searcher.set_start(pos);
        goal_searcher.find_goals();
        if (goal_searcher.goals_found[pos.side]
                && goal_searcher.goal_depth[pos.side][0] <= pos.stepsLeft)
        {
                // score = (WIN_SCORE-10) - goal_searcher.goal_depth[pos.side][0];
                score = WIN_SCORE;
        } else { 
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
            // clamp the evaluation to be less than a win
            score = (score < WIN_SCORE-10) ? ((score > -(WIN_SCORE-10)) ? score : -(WIN_SCORE-10)) : WIN_SCORE-10;
        }

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

    bool in_step;
    int last_score;
    PositionNode last_best;

    int max_depth;

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
        return searcher.set_option(option, value);
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
            int score = -searcher.alphabeta(pos, depth, MIN_SCORE, -best_score);
            Position.free(searcher.nullmove);
            searcher.nodes_searched++;

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
                    engine.new_game();
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.GO:
                    GoCmd gcmd = cast(GoCmd)server.current_cmd;
                    if (gcmd.option == GoCmd.Option.PONDER)
                    {
                        server.clear_cmd();
                        break;
                    }
                    writefln("Starting search.");
                    search_start = getUTCtime();
                    last_decision_change = search_start;
                    engine.start_search();
                    nextreport = getUTCtime() + report_interval;
                    report_depth = 0;
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
                server.bestmove(engine.bestmove);
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
                        end_search += cast(d_time)(0.5 * TicksPerSecond);
                        tc_min_search = (end_search - move_start) / TicksPerSecond;
                        server.info(format("log next min_search set to %d", tc_min_search));
                    } else {
                        server.info(format("log last decision change %d seconds ago", decision_length / TicksPerSecond));
                        engine.set_bestmove();
                        engine.state = EngineState.MOVESET;
                    }
                }
                if (now > nextreport 
                        || engine.depth > report_depth 
                        || cur_best !is engine.pos_list)
                {
                    int depth = engine.in_step ? engine.depth+4 : engine.depth+3;
                    server.info(format("depth %d", depth));
                    server.info(format("time %d", length/TicksPerSecond));
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

