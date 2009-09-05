
import std.conv;
import std.date;
import std.math;
import std.random;
import std.stdio;
import std.string;

import tango.core.Memory;
// Lifted from tango trunk, should be included in some release after 0.99.7
import Arguments;

import alphabeta;
import aeibot;
import goalsearch;
import logging;
import position;
import setupboard;
import staticeval;

const char[] BOT_NAME = "OpFor";
const char[] BOT_AUTHOR = "Janzert";

const int START_SEARCH_NODES = 30000;

struct PositionRecord
{
    ulong position_key;
    int total_seen;
    int gold_wins;
}

class FullSearch : ABSearch
{
    GoalSearchDT goal_searcher;
    StaticEval evaluator;

    ulong nodes_quiesced = 0;

    int max_qdepth = -16;
    int do_qsearch = 1;

    int qdepth;

    this(Logger l)
    {
        super(l);
        goal_searcher = new GoalSearchDT();
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

    int static_eval(Position pos)
    {
        return evaluator.static_eval(pos);
    }

    int quiesce(Position pos, int depth, int alpha, int beta)
    {
        int score = MIN_SCORE;
        if (pos.is_endstate() && (!pos.is_goal(cast(Side)(pos.side^1)) || pos.stepsLeft < 2))
        {
            score = pos.endscore() * WIN_SCORE;
            if (pos.side == Side.BLACK)
            {
                score = -score;
            }
            return score;
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
                    fwritefln(stderr, "%s\n%s", "wb"[pos.side], pos.to_long_str());
                    fwritefln(stderr, "reversed:\n%s\n%s", "wb"[reversed.side], reversed.to_long_str());
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
                if (trap_search.captures[six].length <= pos.stepsLeft + 2)
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
                    if (!duplicate && (pos.stepsLeft > 1
                                || !trap_search.captures[six].first_step.push))
                    {
                        Step* step = steps.newstep();
                        *step = trap_search.captures[six].first_step;
                    }
                }
            }
            if (trap_search.find_captures(pos, cast(Side)(pos.side^1)))
            {
                StepList esteps = StepList.allocate();
                trap_search.evasion_steps(esteps);
                for (int eix=0; eix < esteps.numsteps; eix++)
                {
                    bool duplicate = false;
                    for (int i=0; i < steps.numsteps; i++)
                    {
                        if (esteps.steps[eix] == steps.steps[i])
                        {
                            duplicate = true;
                            break;
                        }
                    }
                    if (!duplicate)
                    {
                        Step* step = steps.newstep();
                        *step = esteps.steps[eix];
                    }
                }
                StepList.free(esteps);
            }
            trap_search.clear();
            debug (check_qsteps)
            {
                StepList rsteps = StepList.allocate();
                pos.get_steps(rsteps);
                for (int six=0; six < steps.numsteps; six++)
                {
                    bool invalid = true;
                    for (int rix=0; rix < rsteps.numsteps; rix++)
                    {
                        if (steps.steps[six].frombit == rsteps.steps[rix].frombit
                                && steps.steps[six].tobit == rsteps.steps[rix].tobit)
                        {
                            invalid = false;
                            break;
                        }
                    }
                    if (invalid)
                    {
                        writefln("%s\n%s", "wb"[pos.side], pos.to_long_str());
                        for (int rix=0; rix < rsteps.numsteps; rix++)
                            writef("%s ", rsteps.steps[rix].toString(true));
                        writefln();
                        throw new Exception(format("Bad step found in qsearch %s",
                                    steps.steps[six].toString(true)));
                    }
                }
                StepList.free(rsteps);
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

            if (cal == ABORT_SCORE
                    || cal == -ABORT_SCORE)
            {
                score = ABORT_SCORE;
                break;
            }

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
        StepList.free(steps);

        if (score != ABORT_SCORE)
            node.set(pos, depth, score, sflag, bstep);

        if (nodes_searched > check_nodes)
        {
            if (should_abort())
            {
                return ABORT_SCORE;
            }
            check_nodes += check_interval;
        }

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
        if (n.pos !is null)
        {
            Position.free(n.pos);
            n.pos = null;
        }
        if (n.move !is null)
        {
            StepList.free(n.move);
            n.move = null;
        }
        n.prev = null;
        n.next = cache_head;
        cache_head = n;
        reserved++;
    }
}

class Engine : AEIEngine
{
    SetupGenerator board_setup;
    ABSearch searcher;
    PositionNode pos_list;
    PositionNode loss_list;
    PositionNode next_pos;
    int num_moves;
    int checked_moves;
    int num_best;
    int num_losing;
    int losing_score;

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
    const static int[] reduction_margins = [150, 350, 1000, 2600, 6000, 15000, 30000];

    this(Logger l)
    {
        super(l);
        board_setup = new SetupGenerator();
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
            case "setup_rabbits":
                switch (toupper(value))
                {
                    case "ANY":
                        board_setup.rabbit_style = SetupGenerator.RabbitSetup.ANY;
                        break;
                    case "STANDARD":
                        board_setup.rabbit_style = SetupGenerator.RabbitSetup.STANDARD;
                        break;
                    case "99OF9":
                        board_setup.rabbit_style = SetupGenerator.RabbitSetup.NINETY_NINE;
                        break;
                    case "FRITZ":
                        board_setup.rabbit_style = SetupGenerator.RabbitSetup.FRITZ;
                        break;
                }
                break;
            case "setup_random_minor":
                board_setup.random_minor = cast(bool)toInt(value);
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
        if (ply < 3)
        {
            Position pos = position.dup;
            board_setup.setup_board(pos.side, pos);
            bestmove = pos.to_placing_move(pos.side);
            Position.free(pos);
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
            num_losing = 0;
            losing_score = -MIN_WIN_SCORE;
            searcher.set_depth(4);
            searcher.prepare();
            state = EngineState.SEARCHING;
        }
    }

    void search(uint check_nodes, bool delegate() should_abort)
    {
        in_step = true;
        d_time start_time = getUTCtime();
        searcher.check_interval = check_nodes;
        ulong stop_nodes = searcher.nodes_searched + check_nodes;
        searcher.check_nodes = stop_nodes;
        searcher.should_abort = should_abort;
        while (searcher.nodes_searched < stop_nodes)
        {
            Position pos = next_pos.pos;
            searcher.nullmove = pos.dup;
            searcher.nullmove.do_step(NULL_STEP);
            int score;
            int search_depth;
            if (root_lmr && depth > 2
                    && checked_moves > num_best)
            {
                search_depth = depth - 1;
                if ((search_depth > 2) && (next_pos.move.numsteps < 4))
                    search_depth--;
                if ((search_depth > 3) && (next_pos.move.steps[next_pos.move.numsteps-1] == NULL_STEP))
                    search_depth--;
                uint margin_num = 0;
                while ((search_depth > 2+margin_num) && (margin_num < reduction_margins.length)
                        && (next_pos.last_score < (best_score - reduction_margins[margin_num])))
                {
                    search_depth--;
                    margin_num++;
                }
                if (search_depth > next_pos.last_depth)
                {
                    ulong sd = next_pos.last_depth;
                    while (sd < search_depth)
                        score = -searcher.alphabeta(pos, ++sd, -(best_score+1), -best_score, 0);
                } else {
                    score = next_pos.last_score;
                    search_depth = next_pos.last_depth;
                }
            } else {
                score = -searcher.alphabeta(pos, depth, MIN_SCORE, -best_score, 0);
                search_depth = depth;
            }

            while (search_depth < depth
                    && score > best_score)
            {
                score = -searcher.alphabeta(pos, ++search_depth, MIN_SCORE, -best_score, 0);
            }
            if (score != -ABORT_SCORE && score > best_score)
                score = -searcher.alphabeta(pos, depth, MIN_SCORE, MAX_SCORE, 0);
            if (score != -ABORT_SCORE)
            {
                next_pos.last_score = score;
                next_pos.last_depth = search_depth;
            }
            Position.free(searcher.nullmove);
            searcher.nodes_searched++;
            checked_moves++;

            if (score == -ABORT_SCORE)
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

            if (score <= losing_score
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
                num_losing += 1;

                if (next_pos is pos_list
                        && next_pos.next is null
                        && next_pos.last_score <= losing_score
                        && losing_score > -WIN_SCORE)
                {
                    logger.info("msg All moves lose, searching for longest loss");
                    num_losing = 0;
                    losing_score = -WIN_SCORE;
                    next_pos.next = loss_list;
                    if (loss_list !is null)
                        loss_list.prev = next_pos;
                    loss_list = null;
                }
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
        if (num_losing)
            logger.info("losing_moves %d", num_losing);
        if (in_step)
        {
            logger.info("depth_searched %d", checked_moves);
            logger.info("score %d", cast(int)(best_score / 1.96));
        } else {
            logger.info("score %d", cast(int)(last_score / 1.96));
        }
        StepList bestline = get_bestline();
        logger.info("pv %s", bestline.to_move_str(position));
        StepList.free(bestline);
    }

    void cleanup_search()
    {
        while (pos_list !is null)
        {
            PositionNode n = pos_list;
            pos_list = n.next;
            PositionNode.free(n);
        }
        while (loss_list !is null)
        {
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
    bool use_stdio = true;

    Arguments arguments = new Arguments();
    arguments.define("server").aliases(["s"]).parameters(1);
    arguments.define("port").aliases(["p"]).parameters(1);
    arguments.define("stdio").conflicts(["socket"]);
    arguments.define("socket").conflicts(["stdio"]);

    if (args.length > 1)
    {
        arguments.parse(args[1..$]);

        if (arguments.contains("server"))
        {
            use_stdio = false;
            ip = arguments["server"];
        }
        if (arguments.contains("port"))
        {
            use_stdio = false;
            port = toUshort(arguments["port"]);
        }
        if (arguments.contains("socket"))
        {
            use_stdio = false;
        }
        if (arguments.contains("stdio"))
        {
            use_stdio = true;
        }
    }

    d_time report_interval = 60 * std.date.TicksPerSecond;
    d_time nextreport = 0;
    int report_depth = 0;

    Logger logger = new Logger();
    ServerInterface server;
    if (use_stdio)
    {
        server = new ServerInterface(new StdioServer(),
               BOT_NAME, BOT_AUTHOR);
    } else {
        try
        {
            server = new ServerInterface(new SocketServer(ip, port),
                BOT_NAME, BOT_AUTHOR);
        } catch (ConnectException e)
        {
            fwritefln(stderr, "Error connecting to server: %s", e.msg);
            fwritefln(stderr, "Tried to connect to %s:%d", ip, port);
            return 1;
        }
    }
    logger.register(server);
    Engine engine = new Engine(logger);

    class AbortChecker
    {
        d_time abort_time;
        ServerInterface server;
        this(ServerInterface s)
        {
            server = s;
        }

        bool should_abort()
        {
            if (abort_time && getUTCtime() > abort_time)
                return true;
            return server.should_abort();
        }
    }
    AbortChecker abort_checker = new AbortChecker(server);

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

    int tc_target_length = 0; // used to set different thinking times than the game timecontrol
    int tc_max_length = 0;

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
            if (engine.state == EngineState.IDLE
                    || engine.state == EngineState.UNINITIALIZED)
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
                    server.shutdown();
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
                    debug (gc_time)
                    {
                        if (gcmd.option == GoCmd.Option.PONDER)
                        {
                            d_time start_collect = getUTCtime();
                            GC.collect();
                            d_time clength = getUTCtime() - start_collect;
                            logger.log("Garbage collection took %d seconds", clength / TicksPerSecond);
                        }
                    }
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
                    if (tc_permove && engine.max_depth == -1)
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
                        logger.log("Stopping engine for incoming move.");
                    }
                    engine.make_move(mcmd.move);
                    server.clear_cmd();
                    logger.log("made move %s", mcmd.move);
                    break;
                case ServerCmd.CmdType.SETPOSITION:
                    PositionCmd pcmd = cast(PositionCmd)server.current_cmd;
                    engine.set_position(pcmd.side, pcmd.pos_str);
                    logger.console("set position\n%s\n%s",
                            "gs"[engine.position.side],
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
                                logger.log("Search depth set to infinite");
                            } else {
                                int depth = toInt(scmd.value);
                                engine.max_depth = (depth > 3) ? depth - 4 : 0;
                                logger.log("Search depth set to %d", engine.max_depth+4);
                            }
                            break;
                        case "tcmove":
                            tc_permove = toInt(scmd.value);
                            if (tc_permove < 600)
                            {
                                GC.disable();
                            } else {
                                GC.enable();
                            }
                            break;
                        case "tcmax":
                            tc_maxreserve = toInt(scmd.value);
                            break;
                        case "tcturntime":
                            tc_maxmove = toInt(scmd.value);
                            break;
                        case "greserve":
                            tc_wreserve = toInt(scmd.value);
                            break;
                        case "sreserve":
                            tc_breserve = toInt(scmd.value);
                            break;
                        case "lastmoveused":
                            tc_lastmove = toInt(scmd.value);
                            break;
                        case "moveused":
                            move_start = getUTCtime() - (cast(d_time)(toInt(scmd.value)) * TicksPerSecond);
                            break;
                        case "target_min_time":
                            tc_target_length = toInt(scmd.value);
                            break;
                        case "target_max_time":
                            tc_max_length = toInt(scmd.value);
                            break;
                        case "log_console":
                            logger.to_console = cast(bool)toInt(scmd.value);
                            break;
                        case "run_gc":
                            d_time start_collect = getUTCtime();
                            GC.collect();
                            d_time clength = getUTCtime() - start_collect;
                            logger.log("Garbage collection took %d seconds", clength / TicksPerSecond);
                            break;
                        case "check_eval":
                            engine.searcher.logged_eval(engine.position);
                            break;
                        default:
                            if (!engine.set_option(scmd.name, scmd.value)
                                    && !server.is_standard_option(scmd.name))
                            {
                                logger.warn("Unrecognized option received: %s\n", scmd.name);
                            }
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
                        auto score = engine.best_score;
                        if (!engine.in_step)
                            score = engine.last_score;
                        if (score <= -MIN_WIN_SCORE)
                        {
                            logger.log("Sending move with forced loss, after %.2f seconds.", seconds);
                        } else {
                            logger.log("Sending forced move, after %.2f seconds.", seconds);
                        }
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
                if (PositionNode.allocated != PositionNode.reserved)
                {
                    logger.warn("PNodes allocated %d != in reserve %d.", PositionNode.allocated, PositionNode.reserved);
                }
                if (StepList.allocated != StepList.reserved)
                {
                    logger.warn("StepList allocated %d != in reserve %d", StepList.allocated, StepList.reserved);
                }
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
                if (tc_max_search && !pondering)
                {
                    d_time abort_time = ((tc_min_search + 20) * TicksPerSecond) + move_start;
                    d_time max_time_limit = (tc_max_search * TicksPerSecond) + move_start;
                    if (abort_time > max_time_limit)
                        abort_time = max_time_limit;
                    if (tc_max_length)
                    {
                        d_time length_abort = (tc_max_length * TicksPerSecond) + search_start;
                        if (abort_time > length_abort)
                            abort_time = length_abort;
                    }
                    abort_checker.abort_time = abort_time;
                } else {
                    abort_checker.abort_time = 0;
                }
                engine.search(check_nodes, &abort_checker.should_abort);
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
                        || (tc_permove && (now >= ((tc_max_search * TicksPerSecond) + move_start)))
                        || (tc_max_length && (now >= ((tc_max_length * TicksPerSecond) + search_start))))
                    {
                        engine.set_bestmove();
                        engine.state = EngineState.MOVESET;
                    } else if (tc_target_length && (now > ((tc_target_length * TicksPerSecond) + search_start)))
                    {
                        logger.log("Target search time reached");
                        d_time decision_length = now - last_decision_change;
                        d_time think_time = now - search_start;
                        d_time time_left = (move_start + (tc_max_search * TicksPerSecond)) - now;
                        d_time search_left = (search_start + (tc_max_length * TicksPerSecond)) - now;
                        if (time_left < search_left)
                            search_left = time_left;
                        logger.log("search_length %d, decision_length %d, search_left %d", 
                                   (think_time / TicksPerSecond),
                                   (decision_length / TicksPerSecond),
                                   (search_left / TicksPerSecond));
                        if (decision_length < think_time * (1.0/tc_confidence_denom)
                                && decision_length < search_left * (1.0/tc_time_left_denom))
                        {
                            real tc_cd = 1.0 / (tc_confidence_denom-1);
                            real tc_tld = 1.0 / (tc_time_left_denom-1);
                            d_time length_cutoff = cast(d_time)((last_decision_change - search_start) * tc_cd) + last_decision_change;
                            d_time reserve_cutoff = cast(d_time)(((search_start + (tc_max_length * TicksPerSecond))
                                        - last_decision_change) * tc_tld) + last_decision_change;
                            d_time end_search = (length_cutoff < reserve_cutoff) ? length_cutoff : reserve_cutoff;
                            end_search += cast(d_time)(0.1 * TicksPerSecond);
                            tc_target_length = (end_search - search_start) / TicksPerSecond;
                            logger.log("next target time set to %d", tc_target_length);
                        } else {
                            engine.set_bestmove();
                            engine.state = EngineState.MOVESET;
                        }
                    } else if (tc_permove && (now > ((tc_min_search * TicksPerSecond) + move_start)))
                    {
                        logger.log("Min search time reached");
                        d_time decision_length = now - last_decision_change;
                        d_time move_length = now - move_start;
                        d_time time_left = (move_start + (tc_max_search * TicksPerSecond)) - now;
                        logger.log("move_length %d, decision_length %d, time_left %d", 
                                    (move_length / TicksPerSecond),
                                    (decision_length / TicksPerSecond),
                                    (time_left / TicksPerSecond));
                        if (decision_length < move_length * (1.0/tc_confidence_denom)
                                && decision_length < time_left * (1.0/tc_time_left_denom))
                        {
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
                } 
                break;
            default:
                break;
        }
    }
}


