
import std.math;
import std.random;
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
    int wins;
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
    int num_trials;
    int total_trials;
    SearchStore search_store;

    real initial_ucb;

    private SearchNode[] search_path;

    this()
    {
        super();
        search_store = new SearchStore();
        initial_ucb = 1.2;
    }

    void start_search()
    {
        if (past.length == 0) // white setup move
        {
            bestmove = "Ra1 Rb1 Rc1 Rd1 Re1 Rf1 Rg1 Rh1 Ha2 Db2 Cc2 Md2 Ee2 Cf2 Dg2 Hh2";
            state = EngineState.MOVESET;
        } else if (past.length == 1)
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
        while (cur_node.trials > search_store.min_trials)
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
            SearchNode best_child;
            int best_ix;
            for (int index=0; index < child_nodes.length; index++)
            {
                SearchNode child = child_nodes[index];
                real ucb;
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
                    ucb = winrate + sqrt(ln_ptrials / child.trials);
                }

                if (best_child is null || best_ucb < ucb)
                {
                    best_child = child;
                    best_ucb = ucb;
                    best_ix = index;
                }
            }
            
            cur_pos.do_step(cur_steps.steps[best_ix]);
            cur_node = best_child;
            search_path ~= cur_node;
            cur_steps.clear();
        }

        Side winner;
        if (best_ucb == -1)
        {
            winner = cast(Side)(cur_pos.side ^1);
            search_path = search_path[0..length-1];
        } else {
            PlayoutResult result = playout_steps(cur_pos);
            winner = (result.endscore == 1) ? Side.WHITE : Side.BLACK;
        }

        foreach (SearchNode node; search_path)
        {
            if (node.side == winner)
            {
                node.wins += 1;
            }
            node.trials += 1;
        }
        total_trials += 1;

        Position.free(cur_pos);
        StepList.free(cur_steps);
        search_path.length = 0;

        if (total_trials >= num_trials)
        {
            set_bestmove();
            state = EngineState.MOVESET;
        }
        return;
    }

    void set_bestmove()
    {
        Position cur_pos = position.dup;
        StepList cur_steps = StepList.allocate();
        StepList move_steps = StepList.allocate();
        SearchNode cur_node = search_store.get_node(cur_pos);
        int[] b_trials;
        real[] b_winrate;
        while (cur_pos.side == position.side)
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

}

int main(char[][] args)
{
    char[] ip = "127.0.0.1";
    ushort port = 40007;
    int num_trials = 100;

    if (args.length > 1)
    {
        try {
            num_trials = std.string.atoi(args[1]);
            writefln("Number of trials set to %d", num_trials);
        } catch { }
    }

    ServerInterface server = new ServerInterface(new SocketServer(ip, port),
            format("%s %d", BOT_NAME, num_trials), BOT_AUTHOR);
    writefln("Connected to server %s:%d", ip, port);
    Engine engine = new Engine();
    engine.num_trials = num_trials;

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
                    engine.start_search();
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.MAKEMOVE:
                    MoveCmd mcmd = cast(MoveCmd)server.current_cmd;
                    engine.make_move(mcmd.move);
                    writefln("made move %s\n%s", mcmd.move, engine.position.to_long_str());
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
                break;
            default:
                break;
        }
    }
}

