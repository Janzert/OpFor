
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
import staticeval;

const char[] BOT_NAME = "OpFor";
const char[] BOT_AUTHOR = "Janzert";

const int START_SEARCH_NODES = 30000;

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
    StaticEval evaluator;

    ulong nodes_quiesced = 0;
    
    int max_qdepth = -16;
    int do_qsearch = 1;

    int qdepth;
    
    this(Logger l)
    {
        super(l);
        goal_searcher = new GoalSearch();
        evaluator = new StaticEval(l, goal_searcher, trap_search);
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
            case "eval_quiesce":
                do_qsearch = toInt(value);
                break;
            case "eval_qdepth":
                max_qdepth = 0 - toInt(value);
                qdepth = max_qdepth;
                break;
            default:
                handled = evaluator.set_option(option, value);
                if (!handled)
                    handled = super.set_option(option, value);
        }
        return handled;
    }

    void set_depth(int depth)
    {
        super.set_depth(depth);
    }

    int eval(Position pos, int alpha, int beta)
    {
        switch (do_qsearch)
        {
            case 0:
                return evaluator.static_eval(pos);
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
            score = evaluator.static_eval(pos);

            debug (eval_bias)
            {
                Position reversed = pos.reverse();
                int rscore = evaluator.static_eval(reversed);
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
                        *step = trap_search.captures[six].first_step;
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
            uint undo = pos.do_step(steps.steps[six]);

            if (pos == nullmove)
            {
                cal = -(WIN_SCORE+1);   // Make this worse than a normal
                                        // loss since it's actually an illegal move
            } else if (pos.stepsLeft == 4)
            {
                Position mynull = nullmove;
                nullmove = pos.dup;
                nullmove.do_step(NULL_STEP);

                cal = -quiesce(pos, depth-1, -beta, -alpha);

                Position.free(nullmove);
                nullmove = mynull;
            } else {
                cal = quiesce(pos, depth-1, alpha, beta);
            }

            pos.undo_step(undo);

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

    int logged_eval(Position pos)
    {
        return evaluator.logged_eval(pos);
    }

    void report()
    {
        super.report();
        if (do_qsearch)
            logger.info("qnodes %d", nodes_quiesced);
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
    int last_depth;

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
    const static int[] reduction_margins = [150, 350, 1000, 2600];

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
        searcher.check_nodes = stop_nodes;
        while (searcher.nodes_searched < stop_nodes)
        {
            Position pos = next_pos.pos;
            searcher.nullmove = pos.dup;
            searcher.nullmove.do_step(NULL_STEP);
            int score;
            int searched_depth;
            if (root_lmr && depth > 2
                    && checked_moves > num_best)
            {
                int firstdepth = depth - 1;
                if ((firstdepth > 2) && (next_pos.move.numsteps < 4))
                    firstdepth--;
                if ((firstdepth > 3) && (next_pos.move.steps[next_pos.move.numsteps-1] == NULL_STEP))
                    firstdepth--;
                uint margin_num = 0;
                while ((firstdepth > 2+margin_num) && (margin_num < reduction_margins.length)
                        && (next_pos.last_score < (best_score - reduction_margins[margin_num])))
                {
                    firstdepth--;
                    margin_num++;
                }
                if (firstdepth > next_pos.last_depth)
                {
                    score = -searcher.alphabeta(pos, firstdepth, -(best_score+1), -best_score);
                    searched_depth = firstdepth;
                } else {
                    score = next_pos.last_score;
                    searched_depth = next_pos.last_depth;
                }
            } else {
                score = best_score + 1;
                searched_depth = depth - 1;
            }

            while (searched_depth < depth
                    && score > best_score
                    && score != -ABORT_SCORE)
            {
                score = -searcher.alphabeta(pos, ++searched_depth, MIN_SCORE, -best_score);
            }
            if (score != -ABORT_SCORE)
            {
                next_pos.last_score = score;
                next_pos.last_depth = searched_depth;
            }
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
            *next_step = n.beststep;
            pos.do_step(n.beststep);
            n = searcher.ttable.get(pos);
        }

        Position.free(pos);
        return bestline;
    }

    void report()
    {
        searcher.report();
        if (in_step)
        {
            logger.info("score cr %d", cast(int)(best_score / 1.96));
        } else {
            logger.info("score cr %d", cast(int)(last_score / 1.96));
        }
        StepList bestline = get_bestline();
        logger.info("pv %s", bestline.to_move_str(position));
        StepList.free(bestline);
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
    int tc_safety_margin = 11;  // safety margin in seconds to end the search
    real tc_min_search_per = 0.6;  // minimum percentage of permove time to search
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

                        if (pondering)
                        {
                            int otherreserve = (myside == Side.WHITE) ? tc_breserve : tc_wreserve;
                            int myrealtime = otherreserve + tc_permove;
                            if (myrealtime < 35)
                            {
                                pondering = false;
                                engine.cleanup_search();
                                engine.state = EngineState.IDLE;
                                logger.log("Stopping ponder because of low time for next move.");
                            }
                        }
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
                    if (chkcmd.current)
                    {
                        engine.searcher.logged_eval(engine.position);
                    } else {
                        Position pos = parse_short_str(chkcmd.side, 4, chkcmd.pos_str);
                        engine.searcher.logged_eval(pos);
                        Position.free(pos);
                    }
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
                        engine.report();
                        check_num = 0;
                        nextreport = now + report_interval;
                        report_depth = engine.depth;
                    }
                } else { // pondering
                    if (now > (tc_permove * TicksPerSecond) + search_start)
                    {
                        engine.cleanup_search();
                        engine.state = EngineState.IDLE;
                    }
                }
                break;
            default:
                break;
        }
    }
}


