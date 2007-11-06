
import std.stdio;

import aeibot;
import position;

const char[] BOT_NAME = "AB";
const char[] BOT_AUTHOR = "Janzert";

enum SType { EXACT, ALPHA, BETA }

struct TTNode
{
    ulong zobrist;
    int depth;
    int score;
    SType type;
    Step beststep;
}

class TransTable
{
    TTNode[] store;

    this (int size)
    {
        store.length = (size*1024*1024) / TTNode.sizeof;
        writefln("Initialized transposition table with %dMB and %d nodes.",
                size,
                store.length);
    }

    TTNode* get(Position pos)
    {
        int key = pos.zobrist % store.length;
        return &store[key];
    }
}

void sortsteps(StepList steps, Step* best)
{
    if (best !is null && (best.frombit != 0 || best.tobit != 0))
    {
        int bix = 0;
        while (bix < steps.numsteps && steps.steps[bix] != *best)
        {
            bix++;
        }
        
        assert (bix < steps.numsteps, "Did not find best step in step list");

        if (bix < steps.numsteps)
        {
            steps.steps[bix].copy(steps.steps[0]);
            steps.steps[0].copy(*best);
        }
    }
}

class ABSearch
{
    static const int WIN_SCORE = 32000;
    static const int MAX_SCORE = 32767;
    static const int MIN_SCORE = -32767;
    static Step nullstep = { frombit: INV_STEP, tobit: INV_STEP };

    TransTable ttable;
    Position nullmove;

    this(TransTable tt)
    {
        ttable = tt;
    }

    int eval(Position pos)
    {
        int score = cast(int)fastFAME(pos, 0.1716) + (pos.zobrist % 150);
        if (pos.side == Side.BLACK)
            score = -score;
        return score;
    }

    int alphabeta(Position pos, int depth, int alpha, int beta)
    {
        int score = MIN_SCORE;
        if (pos.is_endstate())
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
            if (node.depth >= depth)
            {
                if (node.type == SType.EXACT
                    || (node.type == SType.ALPHA && node.score <= alpha)
                    || (node.type == SType.BETA && node.score >= beta))
                {
                    return node.score;
                }
            }
            prev_best = &node.beststep;
        }

        if (depth < 1 && !pos.inpush)
        {
            score = eval(pos);
            if (node.zobrist != pos.zobrist)
            {
                node.beststep.clear();
            }
        } else {
            int best_ix;
            StepList steps = StepList.allocate();
            pos.get_steps(steps);
            sortsteps(steps, prev_best);
            for (int six=0; six < steps.numsteps; six++)
            {
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
                    nullmove.do_step(nullstep);

                    cal = -alphabeta(npos, depth-1, -beta, -alpha);

                    Position.free(nullmove);
                    nullmove = mynull;
                } else {
                    cal = alphabeta(npos, depth-1, alpha, beta);
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
            node.beststep.copy(steps.steps[best_ix]);
            StepList.free(steps);
        }

        node.zobrist = pos.zobrist;
        node.depth = depth;
        node.score = score;
        node.type = sflag;

        return score;
    }
}


class Engine : AEIEngine
{
    ABSearch s_eng;
    Position[] pos_list;
    StepList[] move_list;

    this()
    {
        s_eng = new ABSearch(new TransTable(100));
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
            foreach (Position pos; pstore)
            {
                pos_list ~= pos;
                move_list ~= pstore.getpos(pos);
            }
            delete pstore;
            state = EngineState.SEARCHING;
        }
    }

    void search()
    {
        int start_depth = 2;
        int stop_depth = 4;

        int bestix = 0;
        for (int depth = start_depth; depth < stop_depth; depth++)
        {
            Position pos = pos_list[bestix];
            s_eng.nullmove = pos.dup;
            s_eng.nullmove.do_step(ABSearch.nullstep);
            int score = -s_eng.alphabeta(pos, depth, ABSearch.MIN_SCORE, ABSearch.MAX_SCORE);
            Position.free(s_eng.nullmove);

            for (int i = 0; i < pos_list.length; i++)
            {
                pos = pos_list[i];
                s_eng.nullmove = pos.dup;
                s_eng.nullmove.do_step(ABSearch.nullstep);
                int cal = -s_eng.alphabeta(pos, depth, ABSearch.MIN_SCORE, -score);
                Position.free(s_eng.nullmove);
                if (cal > score)
                {
                    score = cal;
                    bestix = i;
                    if (cal >= ABSearch.WIN_SCORE)
                        break;
                }
            }
        }

        bestmove = move_list[bestix].to_move_str(position);
        state = EngineState.MOVESET;
    }

    void cleanup_search()
    {
        if (pos_list.length > 0)
        {
            foreach (Position pos; pos_list)
            {
                Position.free(pos);
            }
            pos_list.length = 0;
            foreach (StepList move; move_list)
            {
                StepList.free(move);
            }
            move_list.length = 0;
        }
    }

}

int main(char[][] args)
{
    char[] ip = "127.0.0.1";
    ushort port = 40007;

    ServerInterface server = new ServerInterface(new SocketServer(ip, port),
            BOT_NAME, BOT_AUTHOR);
    writefln("Connected to server %s:%d", ip, port);
    Engine engine = new Engine();

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
                        writefln("Starting infinite analyses.");
                    }
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
                engine.cleanup_search();
                writefln("Positions allocated %d, now in reserve %d.", Position.allocated, Position.reserved);
                writefln("StepLists allocated %d, now in reserve %d.", StepList.allocated, StepList.reserved);
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

