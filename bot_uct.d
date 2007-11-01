
import std.date;
import std.math;
import std.stdio;
import std.string;

import position;
import aeibot;

const char[] BOT_NAME = "UCT";
const char[] BOT_AUTHOR = "Janzert";

class SearchStore
{
    int min_trials;
    SearchNode[ulong] store;

    this()
    {
        min_trials = 1;
    }

    SearchNode get_node(Position pos)
    {
        SearchNode n;
        if (pos.zobrist in store)
        {
            n = store[pos.zobrist];
        } else {
            n = new SearchNode(pos);
            store[pos.zobrist] = n;
        }
        return n;
    }

    void clear()
    {
        foreach (SearchNode n; store)
        {
            ulong key = n.zobrist;
            store.remove(key);
            delete n;
        }
    }
}

class SearchNode
{
    ulong zobrist;
    Side side;
    real wins;
    int trials;

    this(Position p)
    {
        side = p.side;
        zobrist = p.zobrist;
        wins = 0;
        trials = 0;
    }
}

class Engine : AEIEngine
{
    int total_trials;
    int max_playout_len;
    SearchStore search_store;

    real initial_ucb;

    private SearchNode[] search_path;

    this(int plen)
    {
        super();
        search_store = new SearchStore();
        initial_ucb = 1.5;
        max_playout_len = plen;
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
            total_trials = 0;
            search_store.clear();
            state = EngineState.SEARCHING;
        }
    }

    void search()
    {
        Position cur_pos = position.dup;
        StepList cur_steps = StepList.allocate();
        SearchNode cur_node = search_store.get_node(cur_pos);
        search_path ~= cur_node;
        real best_ucb;
        while (cur_node.trials > search_store.min_trials && !cur_pos.is_endstate())
        {
            SearchNode[] child_nodes;
            cur_pos.get_steps(cur_steps);
            if (cur_steps.numsteps == 0)
            {
                best_ucb = 0;
                break;
            }

            int parent_trials = 0;
            for (int index=0; index < cur_steps.numsteps; index++)
            {
                Position cpos = cur_pos.dup;
                cpos.do_step(cur_steps.steps[index]);
                SearchNode cnode = search_store.get_node(cpos);
                parent_trials += cnode.trials;
                child_nodes ~= cnode;
                Position.free(cpos);
            }

            real ln_ptrials = log(parent_trials);
            SearchNode best_child = null;
            int best_ix;
            for (int index=0; index < child_nodes.length; index++)
            {
                SearchNode child = child_nodes[index];
                real ucb;

                // XXX: This stops loops in the search and repeated positions but isn't correct
                int repeats = 0;
                for (int i=0; i < search_path.length; i++)
                {
                    if (child.zobrist == search_path[i].zobrist)
                    {
                        repeats += 1;
                    }
                }

                for (int i=0; i < past.length; i++)
                {
                    if (child.zobrist == past[i].zobrist)
                    {
                        repeats += 1;
                    }
                }

                if (repeats > 2)
                {
                    ucb = -1;
                } else if (child.trials == 0)
                {
                    ucb = initial_ucb;
                } else {
                    real winrate = cast(real)child.wins / child.trials;
                    if (child.side != cur_pos.side)
                    {
                        winrate = 1 - winrate;
                    }
                    ucb = winrate + sqrt(ln_ptrials / (5*child.trials));
                }

                if (best_child is null || best_ucb < ucb)
                {
                    best_child = child;
                    best_ucb = ucb;
                    best_ix = index;
                }
            }

            if (best_child is null) // immobilized
                break;
            
            cur_pos.do_step(cur_steps.steps[best_ix]);
            cur_node = best_child;
            search_path ~= cur_node;
            cur_steps.clear();
        }

        real white_value;
        if (best_ucb == -1)
        {
            white_value = cur_pos.side ^ 1;
            search_path = search_path[0..length-1];
        } else {
            PlayoutResult result = playout_steps(cur_pos, max_playout_len);
            if (result.endscore != 0)
            {
                white_value = (result.endscore == 1) ? 1 : 0;
            } else {
                white_value = (FAME(cur_pos) / 400) + 0.5;
            }
        }
        real black_value = 1 - white_value;

        foreach (SearchNode node; search_path)
        {
            if (node.side == Side.WHITE)
            {
                node.wins += white_value;
            } else {
                node.wins += black_value;
            }
            node.trials += 1;
        }
        total_trials += 1;

        Position.free(cur_pos);
        StepList.free(cur_steps);
        search_path.length = 0;

        return;
    }

    void set_bestmove()
    {
        Position cur_pos = position.dup;
        StepList cur_steps = StepList.allocate();
        StepList move_steps = StepList.allocate();
        int[] b_trials;
        real[] b_winrate;
        while (cur_pos.side == position.side && (!cur_pos.is_endstate() || cur_pos.inpush))
        {
            cur_pos.get_steps(cur_steps);
            int best_trials = 0;
            real best_winrate;
            Step* best_step = move_steps.newstep();
            best_step.frombit = 0xFF;
            for (int ix=0; ix < cur_steps.numsteps; ix++)
            {
                Position tpos = cur_pos.dup;
                tpos.do_step(cur_steps.steps[ix]);
                SearchNode tnode = search_store.get_node(tpos);
                if (best_step.frombit == 0xFF || tnode.trials > best_trials)
                {
                    best_trials = tnode.trials;
                    best_winrate = cast(real)tnode.wins/tnode.trials;
                    if (tnode.side != position.side)
                    {
                        best_winrate = 1 - best_winrate;
                    }
                    best_step.set(cur_steps.steps[ix]);;
                }
                Position.free(tpos);
            }
            b_trials ~= best_trials;
            b_winrate ~= best_winrate;
            cur_pos.do_step(*best_step);
            cur_steps.clear();
        }

        bestmove = move_steps.to_move_str(position);

        Position.free(cur_pos);
        StepList.free(cur_steps);
        StepList.free(move_steps);

        writef("Trials for bestmove ");
        for (int i=0; i < b_trials.length; i++)
        {
            writef("%d ", b_trials[i]);
        }
        writef('\n');

        writef("winrate ");
        for (int i=0; i < b_winrate.length; i++)
        {
            writef("%.3f ", b_winrate[i]);
        }
        writef('\n');

    }

    char[] get_bestline()
    {
        char[] bline;
        Position cur_pos = position.dup;
        StepList cur_steps = StepList.allocate();
        StepList move_steps = StepList.allocate();
        SearchNode cur_node = search_store.get_node(cur_pos);

        bool[ulong] seen;
        bool repeat = false;
        while (cur_node.trials > 0 && !cur_pos.is_endstate())
        {
            Position start_pos = cur_pos.dup;
            if (start_pos.side == Side.WHITE)
            {
                bline ~= "w ";
            } else {
                bline ~= "b ";
            }

            while (cur_pos.side == start_pos.side
                    && cur_node.trials > 0
                    && !cur_pos.is_endstate())
            {
                cur_pos.get_steps(cur_steps);
                int best_trials = 0;
                real best_winrate;
                Step* best_step = move_steps.newstep();
                best_step.frombit = 0xFF;
                for (int ix=0; ix < cur_steps.numsteps; ix++)
                {
                    Position tpos = cur_pos.dup;
                    tpos.do_step(cur_steps.steps[ix]);
                    SearchNode tnode = search_store.get_node(tpos);
                    if (best_step.frombit == 0xFF || tnode.trials > best_trials)
                    {
                        best_trials = tnode.trials;
                        best_winrate = cast(real)tnode.wins/tnode.trials;
                        if (tnode.side != position.side)
                        {
                            best_winrate = 1 - best_winrate;
                        }
                        best_step.set(cur_steps.steps[ix]);;
                    }
                    Position.free(tpos);
                }
                if (best_step.frombit == 0xFF) // there were no steps
                {
                    move_steps.pop();
                    break;
                }

                seen[cur_pos.zobrist] = true;
                cur_pos.do_step(*best_step);
                cur_steps.clear();
                cur_node = search_store.get_node(cur_pos);
                if (cur_pos.zobrist in seen)
                {
                    repeat = true;
                    break;
                }
            }

            if (move_steps.numsteps == 0) // immobilized
            {
                break;
            }

            bline ~= move_steps.to_move_str(start_pos);
            bline ~= " ";
            move_steps.clear();
            Position.free(start_pos);

            if (repeat)
            {
                bline ~= "repeat ";
                break;
            }
        }

        Position.free(cur_pos);
        StepList.free(cur_steps);
        StepList.free(move_steps);

        return bline[0..length-1];
    }
}

int main(char[][] args)
{
    char[] ip = "127.0.0.1";
    ushort port = 40007;
    int num_trials = 1000;
    int max_playout_len = 0;

    d_time report_interval = 30 * std.date.TicksPerSecond;
    d_time nextreport = 0;

    foreach (char[] arg; args[1..$])
    {
        switch (arg[0])
        {
            case 't':
                try {
                num_trials = std.string.atoi(arg[1..$]);
                writefln("Number of trials set to %d", num_trials);
                } catch { }
                break;
            case 'l':
                try {
                max_playout_len = std.string.atoi(arg[1..$]);
                writefln("Maximum playout length set to %d", max_playout_len);
                } catch { }
                break;
            default:
                writefln("usage: bot_uct [t<number of trials>] [l<max playout length>]");
                return 0;
        }
    }

    char[] name = format("%s %d", BOT_NAME, num_trials);
    if (max_playout_len != 0)
    {
        name ~= format(" L%d", max_playout_len);
    }

    ServerInterface server = new ServerInterface(new SocketServer(ip, port),
            name, BOT_AUTHOR);
    writefln("Connected to server %s:%d", ip, port);
    Engine engine = new Engine(max_playout_len);

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
                    engine.start_search();
                    if (gcmd.option == GoCmd.Option.INFINITE)
                    {
                        num_trials = 0;
                        writefln("Starting infinite analyses.");
                    }
                    nextreport = getUTCtime() + report_interval;
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.MAKEMOVE:
                    MoveCmd mcmd = cast(MoveCmd)server.current_cmd;
                    engine.make_move(mcmd.move);
                    writefln("made move %s\n%s", mcmd.move, engine.position.to_long_str());
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

        switch (engine.state)
        {
            case EngineState.MOVESET:
                writefln("Sending move %s", engine.bestmove);
                server.bestmove(engine.bestmove);
                engine.state = EngineState.IDLE;
                break;
            case EngineState.SEARCHING:
                engine.search();
                if (num_trials > 0 && engine.total_trials >= num_trials)
                {
                    engine.set_bestmove();
                    engine.state = EngineState.MOVESET;
                }
                d_time now = getUTCtime();
                if (now > nextreport)
                {
                    server.info(format("trials %d", engine.total_trials));
                    char [] currline = engine.get_bestline();
                    server.info(format("currline %s", currline));
                    nextreport = now + report_interval;
                }
                break;
            default:
                break;
        }
    }
}

