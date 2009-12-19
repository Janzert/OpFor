
// Give traceback when an exception is thrown
// does not work in release mode
// does not work if placed in a debug section
version (trace_exceptions)
{
import tango.core.tools.TraceExceptions;
}

import tango.core.Memory;
import tango.core.Atomic;
import tango.core.Thread;
import tango.core.sync.Condition;
import tango.core.sync.Mutex;
import tango.core.sync.ReadWriteMutex;
import tango.io.Stdout;
import tango.text.Ascii;
import tango.text.convert.Float;
import tango.text.convert.Integer;
import tango.time.Clock;
import tango.time.StopWatch;
import tango.time.Time;
import tango.util.Convert;
// Lifted from tango trunk, should be included in some release after 0.99.7
import Arguments;

import alphabeta;
import aeibot;
import logging;
import position;
import setupboard;
import utility;

const char[] BOT_NAME = "OpFor";
const char[] BOT_AUTHOR = "Janzert";

const int START_SEARCH_NODES = 30000;

struct PositionRecord
{
    ulong position_key;
    int total_seen;
    int gold_wins;
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
    int last_score = 0;
    int last_depth = 0;
    int last_nodes = 0;
    bool in_best = false;

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
        n.last_score = 0;
        n.last_depth = 0;
        n.last_nodes = 0;
        n.in_best = false;
        n.prev = null;
        n.next = cache_head;
        cache_head = n;
        reserved++;
    }
}

class Engine : AEIEngine
{
    PositionNode pos_list;
    bool in_step;
    int last_score;
    int depth;

    this(Logger l)
    {
        super(l);
    }

    int cur_score() { return 0; }

    void logged_eval(Position pos) { }

    void report() { }

    bool set_option(char[] name, char[] value) { return false; }

    void shutdown() { }
}

class SearcherMsg
{
    SearchThread sender;

    this (SearchThread s)
    {
        sender = s;
    }
}

class ResultSMessage : SearcherMsg
{
    private
    {
    static Mutex cache_lock;
    static ResultSMessage[] msg_store;
    static uint num_msgs;
    }

    static this()
    {
        cache_lock = new Mutex();
    }

    static ResultSMessage allocate(SearchThread t, PositionNode s)
    {
        synchronized (cache_lock)
        {
            if (num_msgs)
            {
                ResultSMessage msg = msg_store[--num_msgs];
                msg.sender = t;
                msg.search = s;
                return msg;
            }
        }

        return new ResultSMessage(t, s);
    }

    static void free(ResultSMessage m)
    {
        synchronized (cache_lock)
        {
            if (num_msgs == msg_store.length)
                msg_store.length = (msg_store.length * 2) + 1;
            msg_store[num_msgs++] = m;
        }
    }

    PositionNode search;

    this(SearchThread t, PositionNode s)
    {
        super(t);
        search = s;
    }

}

class SearchThread : Thread
{
    bool shutdown = false;
    bool abort_search = false;

    private {
    Mutex search_lock;
    ABQSearch searcher;
    ThreadEngine control;
    int depth;

    Mutex search_check_lock;
    Atomic!(bool) searching;

    bool root_lmr = true;
    const static int[] reduction_margins = [150, 350, 1000, 2600, 6000, 15000, 30000];
    }

    this(ThreadEngine ctl)
    {
        super(&run);
        control = ctl;
        search_lock = new Mutex();
        searching.store(false);
        searcher = new ABQSearch(ctl.logger, ctl.ttable);
        class ACheck
        {
            SearchThread ctl;

            this(SearchThread t)
            {
                ctl = t;
            }

            bool sa()
            {
                return ctl.abort_search;
            }
        }
        auto chk = new ACheck(this);
        searcher.should_abort = &chk.sa;
    }

    void cleanup_search()
    {
        synchronized (search_lock)
        {
            searcher.cleanup();
        }
    }

    bool is_searching()
    {
        return searching.load();
    }

    bool set_option(char[] name, char[] value)
    {
        synchronized (search_lock)
        {
            return searcher.set_option(name, value);
        }
    }

    void set_depth(int d)
    {
        synchronized (search_lock)
        {
            depth = d;
            searcher.set_depth(d);
        }
    }

    void prepare_search()
    {
        synchronized (search_lock)
        {
            searcher.prepare();
        }
    }

    private void search_pos(PositionNode search)
    {
        ulong pos_nodes;
        int score;
        int search_depth;
        synchronized (search_lock)
        {
            // FIXME: check_nodes should be based on 1 second
            ulong check_nodes = 100000;
            searcher.check_interval = check_nodes;
            ulong next_check = searcher.nodes_searched + check_nodes;
            searcher.check_nodes = next_check;

            ulong start_nodes = searcher.nodes_searched;
            int cur_score = control.cur_score();
            Position pos = search.pos;
            searcher.nullmove = pos.dup;
            searcher.nullmove.do_step(NULL_STEP);
            if (root_lmr && depth > 2
                && !search.in_best)
            {
                search_depth = depth - 1;
                if ((search_depth > 2) && (search.move.numsteps < 4))
                    search_depth--;
                if ((search_depth > 3)
                        && (search.move.steps[search.move.numsteps-1]
                            == NULL_STEP))
                    search_depth--;
                uint margin_num = 0;
                while ((search_depth > 2+margin_num)
                        && (margin_num < reduction_margins.length)
                        && (search.last_score < (cur_score
                                - reduction_margins[margin_num])))
                {
                    search_depth--;
                    margin_num++;
                }
                if (search_depth > search.last_depth)
                {
                    ulong sd = search.last_depth;
                    while (sd < search_depth && score != -ABORT_SCORE)
                        score = -searcher.alphabeta(pos, ++sd,
                                -(cur_score+1), -cur_score, 0);
                } else {
                    score = search.last_score;
                    search_depth = search.last_depth;
                }
            } else {
                score = -searcher.alphabeta(pos, depth, MIN_SCORE,
                        -cur_score, 0);
                search_depth = depth;
            }

            while (search_depth < depth && score > cur_score)
            {
                score = -searcher.alphabeta(pos, ++search_depth, MIN_SCORE,
                        -cur_score, 0);
            }
            Position.free(searcher.nullmove);
            searcher.nodes_searched++;
            pos_nodes = searcher.nodes_searched - start_nodes;
        }

        if (score != -ABORT_SCORE)
        {
            int best_score;
            do
            {
                best_score = control.best_score.load();
                if (best_score >= score)
                    break;
            } while (!control.best_score.storeIf(score, best_score))
            synchronized (control.pn_lock)
            {
                search.last_score = score;
                search.last_depth = search_depth;
                search.last_nodes = pos_nodes;
            }
            control.msg_q.set(ResultSMessage.allocate(this, search));
        }
    }

    void run()
    {
        try
        {
            while (!shutdown)
            {
                if (control.run_search.load())
                {
                    searching.store(true);
                    PositionNode search = control.pos_q.get();
                    while (search !is null)
                    {
                        search_pos(search);
                        search = control.pos_q.get();
                    }
                    searching.store(false);
                } else {
                    synchronized (control.search_wait_lock)
                    {
                        control.search_wait.wait(0.1);
                    }
                }
            }
        } catch (Exception err)
        {
            control.logger.warn("Caught error in search thread");
            char[] exception_msg = "".dup;
            void excwriter(char[] str)
            {
                exception_msg ~= str;
            }
            err.writeOut(&excwriter);
            control.logger.console(exception_msg);
        }
    }
}

class ThreadEngine : Engine
{
    TransTable ttable;
    Logger logger;
    Queue!(SearcherMsg) msg_q;
    Queue!(PositionNode) pos_q;
    Atomic!(bool) run_search;
    Condition search_wait;
    Mutex search_wait_lock;

    private {
    SetupGenerator board_setup;
    SearchThread[] threads;

    Atomic!(int) best_score;
    int update_score;
    Mutex pn_lock;
    PositionNode last_best;
    PositionNode loss_list;
    int num_moves;
    int checked_moves;
    int to_check;
    int num_losing;
    int losing_score;
    ulong nodes_searched;

    StopWatch search_timer;

    bool log_tt_stats = false;
    }

    this(Logger l)
    {
        super(l);
        logger = l;
        board_setup = new SetupGenerator();
        ttable = new TransTable(l, 10);
        pn_lock = new Mutex();
        pos_q = new Queue!(PositionNode)();
        msg_q = new Queue!(SearcherMsg)();
        search_wait_lock = new Mutex();
        search_wait = new Condition(search_wait_lock);
        run_search.store(false);
        set_num_threads(1);
    }

    void set_num_threads(uint thread_num)
    {
        if (thread_num > threads.length)
        {
            auto cur_num = threads.length;
            threads.length = thread_num;
            for (int t=cur_num; t < thread_num; t++)
            {
                threads[t] = new SearchThread(this);
                threads[t].start();
            }
        }
        else if (thread_num < threads.length)
        {
            for (int t=threads.length-1; t >= thread_num; t--)
            {
                threads[t].shutdown = true;
            }
            threads.length = thread_num;
        }
    }

    bool set_option(char[] name, char[] value)
    {
        bool handled = true;
        switch(name)
        {
            case "threads":
                set_num_threads(to!(uint)(value));
                break;
            case "hash":
                if (state != EngineState.SEARCHING)
                {
                    ttable.set_size(to!(int)(value));
                } else {
                    logger.warn("Cannot change transposition table size while searching.");
                }
                break;
            case "log_tt_stats":
                log_tt_stats = to!(bool)(value);
                break;
            case "setup_rabbits":
                switch (toUpper(value))
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
                    default:
                        logger.warn("Unrecognized rabbit setup requested '{}'",
                                value);
                }
                break;
            case "setup_random_minor":
                board_setup.random_minor = cast(bool)toInt(value);
                break;
            case "history":
                StepSorter.use_history = to!(bool)(value);
                break;
            case "capture_sort":
                StepSorter.capture_first = to!(bool)(value);
                break;
            case "use_killers":
                StepSorter.use_killers = to!(bool)(value);
                break;
            case "prune_unrelated":
                StepSorter.prune_unrelated = to!(bool)(value);
                break;
            default:
                if (state != EngineState.SEARCHING)
                {
                    foreach (thread; threads)
                    {
                        handled = handled && thread.set_option(name, value);
                    }
                } else {
                    logger.warn("Currently searching did not try to set option {} on search threads.");
                    handled = false;
                }
        }
        return handled;
    }

    void cleanup_search()
    {
        stop_search();
        foreach(thread; threads)
        {
            thread.cleanup_search();
        }
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
        pos_list = null;
        last_best = null;
        num_moves = 0;
        nodes_searched = 0;
        last_score = MIN_SCORE;
        update_score = MIN_SCORE;
        best_score.store(MIN_SCORE);
        state = EngineState.IDLE;
    }

    int cur_score()
    {
        return best_score.load();
    }

    void logged_eval(Position pos)
    {
        if (run_search.load())
        {
            logger.warn("Cannot do a logged eval while searching.");
            return;
        }
        threads[0].searcher.logged_eval(pos);
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
            best_score.store(MIN_SCORE);
            depth = 0;
            checked_moves = 0;
            num_losing = 0;
            losing_score = -MIN_WIN_SCORE;
            foreach (thread; threads)
            {
                thread.set_depth(0);
                thread.prepare_search();
            }
            state = EngineState.SEARCHING;
            PositionNode next_pos = pos_list;
            to_check = 0;
            while (next_pos !is null)
            {
                pos_q.set(next_pos);
                next_pos = next_pos.next;
                ++to_check;
            }
            run_search.store(true);
            search_wait.notifyAll();
        }
    }

    private void stop_search()
    {
        if (run_search.load())
        {
            run_search.store(false);
            pos_q.clear();
            foreach(thread; threads)
            {
                thread.abort_search = true;
            }
            bool still_searching = true;
            while (still_searching)
            {
                still_searching = false;
                foreach(thread; threads)
                {
                    if (thread.is_searching())
                    {
                        still_searching = true;
                        Thread.sleep(0.2);
                    }
                }
            }
            foreach(thread; threads)
            {
                thread.abort_search = false;
            }
        }
    }

    void search(double check_time, bool delegate() should_abort)
    {
        in_step = true;
        search_timer.start();
        uint check_usecs = cast(uint)(check_time * 1000000);
        while (search_timer.microsec() < check_usecs && in_step && best_score.load() < WIN_SCORE)
        {
            bool depth_finished = false;
            SearcherMsg msg;
            do {
                auto time = cast(double)(search_timer.microsec()) / 1000000;
                time = time < 1 ? 1 - time : 0;
                msg = msg_q.get(time);
                if (auto result = cast(ResultSMessage)msg)
                {
                    update_pos(result.search);
                    ResultSMessage.free(result);
                    if (checked_moves >= to_check)
                    {
                        depth_finished = true;
                        break;
                    }
                }
                else if (msg !is null)
                {
                    logger.warn("Got unknown message from search thread.");
                    assert(false, "Bad search thread message");
                }
            } while (msg !is null);

            if (depth_finished)
            {
                run_search.store(false);
                depth++;
                checked_moves = 0;
                foreach (thread; threads)
                {
                    thread.set_depth(depth);
                }
                last_score = best_score.load();
                last_best = pos_list;
                update_score = MIN_SCORE;
                best_score.store(MIN_SCORE);
                PositionNode next_pos = pos_list;
                to_check = 0;
                while (next_pos !is null)
                {
                    pos_q.set(next_pos);
                    next_pos = next_pos.next;
                    ++to_check;
                }
                run_search.store(true);
                search_wait.notifyAll();
                in_step = false;
            }
        }
    }

    void set_bestmove()
    {
        bestmove = pos_list.move.to_move_str(position);
        stop_search();
        state = EngineState.MOVESET;
    }

    void shutdown()
    {
        foreach (thread; threads)
        {
            thread.shutdown = true;
        }
        search_wait.notifyAll();
    }

    private void update_pos(PositionNode result)
    {
        auto score = result.last_score;
        if (score > update_score)
        {
            update_score = score;
            if (result !is pos_list)
            {
                result.in_best = true;

                synchronized (pn_lock)
                {
                    if (result.next !is null)
                        result.next.prev = result.prev;
                    result.prev.next = result.next;
                    result.next = pos_list;
                    result.prev = null;
                    pos_list.prev = result;
                    pos_list = result;
                }
            }
        }
        if (score <= losing_score
                && result !is pos_list)
        {
            synchronized (pn_lock)
            {
                auto next_pos = result.next;
                if (result.next !is null)
                    result.next.prev = result.prev;

                result.prev.next = result.next;

                result.prev = null;
                result.next = loss_list;
                if (loss_list !is null)
                    loss_list.prev = result;
                loss_list = result;
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
        }
        nodes_searched += result.last_nodes;
        checked_moves += 1;
    }

    StepList get_bestline()
    {
        StepList bestline = pos_list.move.dup;
        Position pos = pos_list.pos.dup;
        TTNode* n = ttable.get(pos);
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
            n = ttable.get(pos);
        }

        Position.free(pos);
        return bestline;
    }

    void report()
    {
        logger.info("nodes {}", nodes_searched);
        if (num_losing)
            logger.info("losing_moves {}", num_losing);
        if (in_step)
        {
            logger.info("depth_searched {}", checked_moves);
            logger.info("to_search {}", to_check - checked_moves);
            logger.info("score {}", cast(int)(best_score.load() / 1.96));
        } else {
            logger.info("score {}", cast(int)(last_score / 1.96));
        }
        StepList bestline = get_bestline();
        logger.info("pv {}", bestline.to_move_str(position));
        StepList.free(bestline);
        if (log_tt_stats)
        {
            logger.info("TT hits {} misses {} collisions {}",
                ttable.hits, ttable.miss, ttable.collisions);
        }
    }
}

class SeqEngine : Engine
{
    TransTable ttable;
    SetupGenerator board_setup;
    ABQSearch searcher;
    PositionNode loss_list;
    PositionNode next_pos;
    int num_moves;
    int checked_moves;
    int num_losing;
    int losing_score;

    bool log_tt_stats = false;

    int best_score;

    PositionNode last_best;

    const static int BOOK_SIZE = 1000000;
    PositionRecord[] opening_book;
    bool position_record = false;

    const static uint MAX_ABORT_REPORTS = 4;
    uint aborts_reported = 0;

    bool root_lmr = true;
    const static int[] reduction_margins = [150, 350, 1000, 2600, 6000, 15000, 30000];

    StopWatch search_length;

    this(Logger l)
    {
        super(l);
        board_setup = new SetupGenerator();
        ttable = new TransTable(l, 10);
        searcher = new ABQSearch(l, ttable);
        in_step = false;
    }

    bool set_option(char[] option, char[] value)
    {
        bool handled = true;
        switch (option)
        {
            case "hash":
                ttable.set_size(to!(int)(value));
                break;
            case "log_tt_stats":
                log_tt_stats = to!(bool)(value);
                break;
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
                switch (toUpper(value))
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
                    default:
                        logger.warn("Unrecognized rabbit setup requested '{}'",
                                value);
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

    int cur_score()
    {
        return best_score;
    }

    void logged_eval(Position pos)
    {
        searcher.logged_eval(pos);
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
            num_losing = 0;
            losing_score = -MIN_WIN_SCORE;
            searcher.set_depth(4); // FIXME: Should be same as depth, i.e. 0
            searcher.prepare();
            state = EngineState.SEARCHING;
            search_length.start();
        }
    }

    void search(double check_time, bool delegate() should_abort)
    {
        in_step = true;
        uint check_nodes;
        if (searcher.nodes_searched
                && (search_length.microsec > 2000000))
        {
            check_nodes = cast(uint)(searcher.nodes_searched
                    / (cast(double)(search_length.microsec) / 1000000));
        } else {
            check_nodes = START_SEARCH_NODES;
        }
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
                    && !next_pos.in_best)
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
                    while (sd < search_depth && score != -ABORT_SCORE)
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
                    logger.console("Saw position in book added {} to {} score.", val, score);
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
                    next_pos.in_best = true;
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
        search_length.stop();
        state = EngineState.MOVESET;
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
            logger.info("losing_moves {}", num_losing);
        if (in_step)
        {
            logger.info("depth_searched {}", checked_moves);
            logger.info("score {}", cast(int)(best_score / 1.96));
        } else {
            logger.info("score {}", cast(int)(last_score / 1.96));
        }
        StepList bestline = get_bestline();
        logger.info("pv {}", bestline.to_move_str(position));
        StepList.free(bestline);
        if (log_tt_stats)
        {
            logger.info("TT hits {} misses {} collisions {}",
                ttable.hits, ttable.miss, ttable.collisions);
        }
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
        state = EngineState.IDLE;
    }
}


int main(char[][] args)
{
    char[] ip = "127.0.0.1";
    ushort port = 40015;
    bool use_stdio = true;

    Logger logger = new Logger();
    Engine engine;

    Arguments arguments = new Arguments();
    arguments.define("server").aliases(["s"]).parameters(1);
    arguments.define("port").aliases(["p"]).parameters(1);
    arguments.define("stdio").conflicts(["socket"]);
    arguments.define("socket").conflicts(["stdio"]);
    arguments.define("seq").conflicts(["threads"]);
    arguments.define("threads").conflicts(["seq"]);

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
            port = toInt(arguments["port"]);
        }
        if (arguments.contains("socket"))
        {
            use_stdio = false;
        }
        if (arguments.contains("stdio"))
        {
            use_stdio = true;
        }
        if (arguments.contains("seq"))
        {
            engine = new SeqEngine(logger);
        }
        if (arguments.contains("threads"))
        {
            engine = new ThreadEngine(logger);
        }
    }
    if (engine is null)
        engine = new ThreadEngine(logger);

    int max_depth = -1;

    TimeSpan report_interval = TimeSpan.fromMinutes(1);
    Time nextreport = Time.min;
    int report_depth = 0;

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
            Stderr.formatln("Error connecting to server: {}", e.msg);
            Stderr.formatln("Tried to connect to {}:{}", ip, port);
            return 1;
        }
    }
    logger.register(server);

    class AbortChecker
    {
        Time abort_time;
        ServerInterface server;
        this(ServerInterface s)
        {
            server = s;
            abort_time = Time.max;
        }

        bool should_abort()
        {
            if (Clock.now() > abort_time)
                return true;
            return server.should_abort();
        }
    }
    AbortChecker abort_checker = new AbortChecker(server);

    TimeSpan tc_permove = TimeSpan.zero; // time given per move
    TimeSpan tc_maxreserve = TimeSpan.zero; // maximum reserve size
    TimeSpan tc_maxmove = TimeSpan.zero; // maximum time for a move
    TimeSpan tc_wreserve = TimeSpan.zero; // white's reserve time
    TimeSpan tc_breserve = TimeSpan.zero; // black's reserve time
    TimeSpan tc_lastmove = TimeSpan.zero; // time used for opponents last move
    TimeSpan tc_safety_margin = TimeSpan.fromSeconds(11); // safety margin in seconds to end the search
    real tc_min_search_per = 0.6;  // minimum percentage of permove time to search
    real tc_confidence_denom = 3;
    real tc_time_left_denom = 3;

    // used to set different thinking times than the game timecontrol
    TimeSpan tc_target_length = TimeSpan.fromSeconds(0);
    TimeSpan tc_max_length =  TimeSpan.fromSeconds(0);

    TimeSpan search_time = TimeSpan.fromSeconds(0);
    TimeSpan search_max = TimeSpan.fromSeconds(0);
    int search_num = 0;
    Time search_start;
    Time move_start;

    TimeSpan tc_min_search;
    TimeSpan tc_max_search;
    Time last_decision_change;

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
            logger.warn("Received unknown command: '{}'", e.command);
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
                    engine.shutdown();
                    server.shutdown();
                    return 0;
                case ServerCmd.CmdType.NEWGAME:
                    logger.log("Starting new game.");
                    if (engine.state != EngineState.IDLE)
                    {
                        engine.cleanup_search();
                    }
                    engine.new_game();
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.GO:
                    GoCmd gcmd = cast(GoCmd)server.current_cmd;
                    if (engine.state != EngineState.IDLE)
                    {
                        engine.cleanup_search();
                    }
                    logger.log("Starting search");
                    logger.console("{}\n{}", "wb"[engine.position.side], engine.position.to_long_str);
                    search_start = Clock.now();
                    debug (gc_time)
                    {
                        if (gcmd.option == GoCmd.Option.PONDER)
                        {
                            auto start_collect = Clock.now();
                            GC.collect();
                            auto clength = Clock.now() - start_collect;
                            logger.log("Garbage collection took {} seconds", clength.interval);
                        }
                    }
                    engine.start_search();
                    last_decision_change = search_start;
                    nextreport = Clock.now() + report_interval;
                    report_depth = 0;
                    if (gcmd.option == GoCmd.Option.PONDER)
                    {
                        pondering = true;
                    } else {
                        pondering = false;
                    }
                    if (tc_permove.interval && max_depth == -1)
                    {
                        Side myside = engine.position.side;
                        TimeSpan myreserve = (myside == Side.WHITE) ? tc_wreserve : tc_breserve;
                        TimeSpan max_reserve = tc_maxmove - tc_permove;
                        if (tc_maxreserve > max_reserve)
                            max_reserve = tc_maxreserve;
                        // if reserve is unlimited target it to 4 * move time
                        if (max_reserve == TimeSpan.zero)
                            max_reserve = tc_permove * 4;
                        real reserve_fill = myreserve.interval / max_reserve.interval;
                        reserve_fill = reserve_fill > 1.0 ? 1.0 : reserve_fill;
                        tc_min_search = TimeSpan(cast(long)(tc_permove.ticks
                                * tc_min_search_per));
                        tc_min_search += TimeSpan(cast(long)((tc_permove.ticks
                                    * (1-tc_min_search_per)) * reserve_fill));

                        tc_max_search = tc_permove + myreserve;
                        if (tc_maxmove != TimeSpan.zero
                                && (tc_max_search > tc_maxmove))
                        {
                            tc_max_search = tc_maxmove;
                        }
                        tc_max_search -= tc_safety_margin;
                        if (tc_max_search < TimeSpan.zero)
                            tc_max_search = TimeSpan.zero;

                        if (pondering)
                        {
                            TimeSpan otherreserve = (myside == Side.WHITE)
                                ? tc_breserve : tc_wreserve;
                            TimeSpan myrealtime = otherreserve + tc_permove;
                            if (myrealtime.seconds < 35)
                            {
                                pondering = false;
                                engine.cleanup_search();
                                logger.log("Stopping ponder because of low time for next move.");
                            }
                        }
                        logger.log("Min search: {} Max: {}",
                                tc_min_search.interval, tc_max_search.interval);
                    } else {
                        tc_min_search = TimeSpan.zero;
                        tc_max_search = TimeSpan.zero;
                    }
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.STOP:
                    if (engine.state == EngineState.SEARCHING)
                    {
                        engine.set_bestmove();
                    }
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.MAKEMOVE:
                    MoveCmd mcmd = cast(MoveCmd)server.current_cmd;
                    if (engine.state != EngineState.IDLE)
                    {
                        engine.cleanup_search();
                        logger.log("Stopping engine for incoming move.");
                    }
                    engine.make_move(mcmd.move);
                    server.clear_cmd();
                    logger.log("made move {}", mcmd.move);
                    break;
                case ServerCmd.CmdType.SETPOSITION:
                    PositionCmd pcmd = cast(PositionCmd)server.current_cmd;
                    engine.set_position(pcmd.side, pcmd.pos_str);
                    logger.console("set position\n{}\n{}",
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
                                max_depth = -1;
                                logger.log("Search depth set to infinite");
                            } else {
                                int depth = toInt(scmd.value);
                                max_depth = (depth > 3) ? depth - 4 : 0;
                                logger.log("Search depth set to {}",
                                        max_depth+4);
                            }
                            break;
                        case "tcmove":
                            tc_permove = TimeSpan.fromInterval(
                                    toFloat(scmd.value));
                            if (tc_permove.minutes < 10)
                            {
                                GC.disable();
                            } else {
                                GC.enable();
                            }
                            break;
                        case "tcmax":
                            tc_maxreserve = TimeSpan.fromInterval(
                                    toFloat(scmd.value));
                            break;
                        case "tcturntime":
                            tc_maxmove = TimeSpan.fromInterval(
                                toFloat(scmd.value));
                            break;
                        case "greserve":
                            tc_wreserve = TimeSpan.fromInterval(
                                toFloat(scmd.value));
                            break;
                        case "sreserve":
                            tc_breserve = TimeSpan.fromInterval(
                                    toFloat(scmd.value));
                            break;
                        case "lastmoveused":
                            tc_lastmove = TimeSpan.fromInterval(
                                    toFloat(scmd.value));
                            break;
                        case "moveused":
                            auto used = TimeSpan.fromInterval(
                                    toFloat(scmd.value));
                            move_start = Clock.now() - used;
                            break;
                        case "target_min_time":
                            tc_target_length = TimeSpan.fromInterval(
                                    toFloat(scmd.value));
                            break;
                        case "target_max_time":
                            tc_max_length = TimeSpan.fromInterval(
                                    toFloat(scmd.value));
                            break;
                        case "log_console":
                            logger.to_console = to!(bool)(scmd.value);
                            break;
                        case "run_gc":
                            auto collect_timer = new StopWatch();
                            collect_timer.start();
                            GC.collect();
                            auto collect_time = collect_timer.stop();
                            logger.log("Garbage collection took {} seconds",
                                    collect_time);
                            break;
                        case "check_eval":
                            engine.logged_eval(engine.position);
                            break;
                        default:
                            if (!engine.set_option(scmd.name, scmd.value)
                                    && !server.is_standard_option(scmd.name))
                            {
                                logger.warn("Unrecognized option received: {}\n", scmd.name);
                            }
                            break;
                    }
                    server.clear_cmd();
                    break;
                default:
                    throw new Exception("Unhandled server command in main loop.");
            }
        }

        TimeSpan search_length = Clock.now() - search_start;
        switch (engine.state)
        {
            case EngineState.MOVESET:
                if (search_length > search_max)
                {
                    search_max = search_length;
                }
                auto seconds = search_length.interval();
                if (engine.ply > 2)
                {
                    search_time += search_length;
                    search_num += 1;
                    if (engine.cur_score >= WIN_SCORE)
                    {
                        logger.log("Sending forced win move in {} seconds.",
                                seconds);
                    } else if (engine.pos_list.next is null)
                    {
                        auto score = engine.cur_score;
                        if (!engine.in_step)
                            score = engine.last_score;
                        if (score <= -MIN_WIN_SCORE)
                        {
                            logger.log("Sending move with forced loss, after {} seconds.", seconds);
                        } else {
                            logger.log("Sending forced move, after {} seconds.", seconds);
                        }
                    }
                }
                double average = 0;
                if (search_num)
                {
                    average = search_time.interval() / search_num;
                }
                double max_seconds = search_max.interval();
                /*
                logger.log("Searched {} nodes, {:d} nps, {} tthits.",
                        engine.searcher.nodes_searched,
                        engine.searcher.nodes_searched/seconds,
                        engine.searcher.tthits);
                */
                logger.log("Finished search in {} seconds, average {}, max {}.",
                        seconds, average, max_seconds);
                logger.console("Sending move {}", engine.bestmove);
                if (!pondering)
                {
                    server.bestmove(engine.bestmove);
                }
                engine.cleanup_search();
                logger.log("Positions allocated {}, in reserve {}({}MB).",
                        Position.allocated, Position.reserved, Position.reserve_size);
                if (PositionNode.allocated != PositionNode.reserved)
                {
                    logger.warn("PNodes allocated {} != in reserve {}.",
                            PositionNode.allocated, PositionNode.reserved);
                }
                if (StepList.allocated != StepList.reserved)
                {
                    logger.log("StepList allocated {}, in reserve {}",
                            StepList.allocated, StepList.reserved);
                }
                break;
            case EngineState.SEARCHING:
                PositionNode cur_best = engine.pos_list;
                Time now = Clock.now();
                double check_time = 1.0;
                if (tc_max_search != TimeSpan.zero && !pondering)
                {
                    Time abort_time = move_start + tc_max_search;
                    if (tc_max_length != TimeSpan.zero)
                    {
                        Time length_abort = search_start + tc_max_length;
                        if (abort_time > length_abort)
                            abort_time = length_abort;
                    }
                    abort_checker.abort_time = abort_time;
                    auto abort_length = abort_time - now;
                    if (abort_length.interval < 1.0)
                    {
                        check_time = abort_length.interval;
                        check_time = check_time > 0 ? check_time : 0;
                    }
                } else {
                    abort_checker.abort_time = Time.max;
                }
                engine.search(check_time, &abort_checker.should_abort);
                check_num += 1;
                if (cur_best != engine.pos_list)
                {
                    last_decision_change = now;
                }
                if (!pondering)
                {
                    if (((max_depth != -1) && (engine.depth > max_depth))
                        || (engine.cur_score >= WIN_SCORE)
                        || (engine.pos_list.next is null)
                        || (tc_permove != TimeSpan.zero
                            && (now >= (move_start + tc_max_search)))
                        || (tc_max_length != TimeSpan.zero
                            && (now >= (search_start + tc_max_length))))
                    {
                        engine.set_bestmove();
                    } else if (tc_target_length != TimeSpan.zero
                            && (now > (search_start + tc_target_length)))
                    {
                        logger.log("Target search time reached");
                        auto decision_length = (now - last_decision_change).interval;
                        auto think_time = (now - search_start).interval;
                        auto time_left = ((move_start + tc_max_search)
                                - now).interval;
                        auto search_left = ((search_start + tc_max_length)
                            - now).interval;
                        if (time_left < search_left)
                            search_left = time_left;
                        logger.log("search_length {}, decision_length {}, search_left {}",
                                   think_time, decision_length, search_left);
                        if (decision_length < (think_time
                                    * (1.0/tc_confidence_denom))
                                && decision_length < (search_left
                                    * (1.0/tc_time_left_denom)))
                        {
                            auto tc_cd = 1.0 / (tc_confidence_denom-1);
                            auto tc_tld = 1.0 / (tc_time_left_denom-1);
                            auto length_cutoff = last_decision_change
                                + TimeSpan.fromInterval((last_decision_change
                                            - search_start).interval * tc_cd);
                            auto reserve_cutoff = last_decision_change
                                + TimeSpan.fromInterval(((search_start
                                                + tc_max_length)
                                            - last_decision_change).interval
                                        * tc_tld);
                            auto end_search = (length_cutoff < reserve_cutoff) ? length_cutoff : reserve_cutoff;
                            end_search += TimeSpan.fromInterval(0.1);
                            tc_target_length = (end_search - search_start);
                            logger.log("next target time set to {}",
                                    tc_target_length.interval);
                        } else {
                            engine.set_bestmove();
                        }
                    } else if (tc_permove != TimeSpan.zero
                            && (now > (move_start + tc_min_search)))
                    {
                        logger.log("Min search time reached");
                        auto decision_length = (now - last_decision_change).interval;
                        auto move_length = (now - move_start).interval;
                        auto time_left = ((move_start + tc_max_search)
                                - now).interval;
                        logger.log("move_length {}, decision_length {}, time_left {}",
                                    move_length, decision_length, time_left);
                        if (decision_length < move_length
                                * (1.0/tc_confidence_denom)
                                && decision_length < time_left
                                * (1.0/tc_time_left_denom))
                        {
                            real tc_cd = 1.0 / (tc_confidence_denom-1);
                            real tc_tld = 1.0 / (tc_time_left_denom-1);
                            auto length_cutoff = last_decision_change
                                + TimeSpan.fromInterval((last_decision_change
                                            - move_start).interval * tc_cd);
                            auto reserve_cutoff = last_decision_change
                                + TimeSpan.fromInterval(((move_start
                                                + tc_max_search)
                                        - last_decision_change).interval
                                        * tc_tld);
                            auto end_search = (length_cutoff < reserve_cutoff) ? length_cutoff : reserve_cutoff;
                            end_search += TimeSpan.fromInterval(0.1);
                            tc_min_search = end_search - move_start;
                            logger.log("next min_search set to {}",
                                    tc_min_search.interval);
                        } else {
                            engine.set_bestmove();
                        }
                    }
                    if (now > nextreport
                            || engine.depth > report_depth
                            || cur_best !is engine.pos_list)
                    {
                        if (engine.in_step)
                        {
                            logger.info("depth {}+", engine.depth+3);
                        } else {
                            logger.info("depth {}", engine.depth+3);
                        }
                        logger.info("time {:f0}", (now-search_start).interval);
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


