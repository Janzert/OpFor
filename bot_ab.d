
import std.c.string;
import std.date;
import std.math;
import std.random;
import std.stdio;
import std.string;

import alphabeta;
import aeibot;
import goalsearch;
import position;

const char[] BOT_NAME = "AB";
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
    this (TransTable tt)
    {
        super(tt);
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
    
    this (TransTable tt)
    {
        super(tt);
        goal_searcher = new GoalSearch(16);
    }
    
    int eval(Position pos)
    {
        int score = cast(int)fastFAME(pos, 0.1716); // first pawn worth ~196
                                                    // only a pawn left ~31883
        score += trap_safety(pos) << 2;
        score += central_elephant(pos);
        score += frozen_pieces(pos);
        score += on_trap(pos);
        score += rabbit_wall(pos);
        score += rabbit_open(pos);

        if (pos.side == Side.BLACK)
            score = -score;

        const int[17] GOAL_THREAT = [30000, 8000, 4000, 2000, 1000,
              300, 250, 200, 150,
              75, 50, 40, 35,
              20, 10, 7, 5];
        goal_searcher.set_start(pos);
        goal_searcher.find_goals();
        if (goal_searcher.goals_found[pos.side]
                && goal_searcher.goal_depth[pos.side][0] <= pos.stepsLeft)
        {
                score = (WIN_SCORE-10) - goal_searcher.goal_depth[pos.side][0];
        } else { 
            if (goal_searcher.goals_found[pos.side])
            {
                score += GOAL_THREAT[goal_searcher.goal_depth[pos.side][0] - pos.stepsLeft];
            }
            if (goal_searcher.goals_found[pos.side^1])
            {
                score -= GOAL_THREAT[goal_searcher.goal_depth[pos.side^1][0]];
            }
        }

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

    int max_depth;

    this()
    {
        searcher = new FullSearch(new TransTable(500));
        //searcher = new ScoreSearch(new TransTable(150));
        max_depth = 2;
    }

    void start_search()
    {
        if (ply == 1) // white setup move
        {
            bestmove = "Ra1 Rb1 Rc1 Rd1 Re1 Rf1 Rg1 Rh1 Ha2 Db2 Cc2 Md2 Ee2 Cf2 Dg2 Hh2";
            state = EngineState.MOVESET;
        } else if (ply == 2)
        {
            if (position.pieces[11] == Piece.WELEPHANT)
            {
                bestmove = "ra8 rb8 rc8 rd8 re8 rf8 rg8 rh8 ha7 db7 cc7 ed7 me7 cf7 dg7 hh7";
            } else {
                bestmove = "ra8 rb8 rc8 rd8 re8 rf8 rg8 rh8 ha7 db7 cc7 md7 ee7 cf7 dg7 hh7";
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
                if ((max_depth != -1) && (depth > max_depth))
                {
                    break;
                }
                best_score = MIN_SCORE;
                next_pos = pos_list;
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
        searcher.cleanup();
    }

}

int main(char[][] args)
{
    char[] ip = "127.0.0.1";
    ushort port = 40007;

    d_time report_interval = 30 * std.date.TicksPerSecond;
    d_time nextreport = 0;
    int report_depth = 0;

    ServerInterface server = new ServerInterface(new SocketServer(ip, port),
            BOT_NAME, BOT_AUTHOR);
    writefln("Connected to server %s:%d", ip, port);
    Engine engine = new Engine();

    d_time search_time = 0;
    d_time search_max = 0;
    int search_num = 0;
    d_time search_start;

    d_time win_search_time = 0;
    int win_search_num = 0;
    int check_num = 0;
    while (true)
    {
        if (engine.state == EngineState.IDLE)
        {
            server.check(10);
        } else {
            server.check();
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
                    if (engine.position !is null)
                    {
                        writefln(engine.position.to_long_str());
                    }
                    writefln("Starting new game.");
                    engine.new_game();
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.GO:
                    writefln("Starting search.");
                    GoCmd gcmd = cast(GoCmd)server.current_cmd;
                    search_start = getUTCtime();
                    engine.start_search();
                    if (gcmd.option == GoCmd.Option.INFINITE)
                    {
                        engine.max_depth = -1;
                        writefln("Starting infinite analyses.");
                    }
                    nextreport = getUTCtime() + report_interval;
                    report_depth = 0;
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.MAKEMOVE:
                    MoveCmd mcmd = cast(MoveCmd)server.current_cmd;
                    engine.make_move(mcmd.move);
                    writefln("received move %s\n%s", mcmd.move, engine.position.to_long_str());
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
                        win_search_time += length;
                        win_search_num += 1;
                        real avg_wsearch = (cast(real)win_search_time / TicksPerSecond) / win_search_num;
                        writefln("Sending forced win move %.2f average.", avg_wsearch);
                    }
                }
                real average = 0;
                if (search_num)
                {
                    average = (cast(real)search_time / TicksPerSecond) / search_num;
                }
                real max_seconds = cast(real)search_max / TicksPerSecond;
                writefln("Finished search in %.2f seconds, average %.2f, max %.2f.", seconds, average, max_seconds);
                writefln("Searched %d nodes, %.0f nps, %d tthits.",
                        engine.searcher.nodes_searched, engine.searcher.nodes_searched/seconds, engine.searcher.tthits);
                writefln("Current score %.2f", engine.best_score / 196.0);
                writefln("Sending move %s", engine.bestmove);
                server.bestmove(engine.bestmove);
                engine.cleanup_search();
                writefln("Positions allocated %d, in reserve %d (%.0fMB).",
                        Position.allocated, Position.reserved, Position.reserve_size);
                writefln("PNodes allocated %d, in reserve %d.", PositionNode.allocated, PositionNode.reserved);
                engine.state = EngineState.IDLE;
                break;
            case EngineState.SEARCHING:
                if (engine.searcher.nodes_searched && (length > (TicksPerSecond/2)))
                {
                    int chunk = engine.searcher.nodes_searched / (length / (TicksPerSecond /2));
                    engine.search(chunk);
                } else {
                    engine.search(START_SEARCH_NODES);
                }
                check_num += 1;
                if (((engine.max_depth != -1) && (engine.depth > engine.max_depth))
                    || (engine.best_score >= WIN_SCORE))
                {
                    engine.set_bestmove();
                    engine.state = EngineState.MOVESET;
                }
                d_time now = getUTCtime();
                if (now > nextreport || engine.depth > report_depth)
                {
                    server.info(format("depth %d", engine.depth+4));
                    server.info(format("time %d", length/TicksPerSecond));
                    server.info(format("nodes %d", engine.searcher.nodes_searched));
                    server.info(format("score cr %d", cast(int)(engine.best_score / 1.96)));
                    StepList bestline = engine.get_bestline();
                    server.info(format("pv %s", bestline.to_move_str(engine.position)));
                    StepList.free(bestline);
                    server.info(format("number checks %d", check_num));
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

