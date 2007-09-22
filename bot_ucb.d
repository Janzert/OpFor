
import std.math;
import std.random;
import std.stdio;
import std.string;

import position;
import aeibot;

const char[] BOT_NAME = "UCB on moves";
const char[] BOT_AUTHOR = "Janzert";

class Move
{
    Position position;
    StepList steps;
    double wins;
    double tests;
}

class Engine : AEIEngine
{
    Move[] moves;
    double num_tests;
    double total_tests;
    double best_tests;

    this()
    {
        super();
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
            if (moves.length)
            {
                foreach (Move move; moves)
                {
                    Position.free(move.position);
                    StepList.free(move.steps);
                    delete move;
                }
            }

            moves.length = 0;
            total_tests = 0;
            best_tests = 0;

            PosStore pstore = position.get_moves();
            foreach (Position mpos; pstore)
            {
                Move move = new Move;
                move.position = mpos;
                move.steps = pstore.getpos(mpos);
                move.wins = 0;
                move.tests = 0;
                moves ~= move;
            }
            state = EngineState.SEARCHING;
        }
    }

    void search()
    {
        Move tmove;
        double tucb = 0.0;
        double winrate, ucb;
        double log_tt = log(total_tests);
        foreach(Move move; moves)
        {
            if (move.tests == 0)
            {
                winrate = 1;
                ucb = 1.2;
            } else {
                winrate = move.wins/move.tests;
                ucb = winrate * sqrt(log_tt / move.tests);
            }
            if (tmove is null
                    || (tucb < ucb))
            {
                tmove = move;
                tucb = ucb;
            }
        }

        Position pos = tmove.position.dup;
        PlayoutResult result = playout_steps(pos);
        Position.free(pos);
        if (position.side == Side.WHITE)
        {
            if (result.endscore == 1)
            {
                tmove.wins += 1;
            }
        } else {
            if (result.endscore == -1)
            {
                tmove.wins += 1;
            }
        }
        tmove.tests += 1;
        total_tests += 1;

        if (tmove.tests > best_tests)
        {
            best_tests = tmove.tests;
            char[] newmove = tmove.steps.to_move_str(position);
            if (cmp(newmove, bestmove))
            {
                bestmove = newmove;
                writefln("setting bestmove %s", bestmove);
                writefln("wins %.0f tests %.0f total %.0f", tmove.wins, best_tests, total_tests);
            }
        }

        if (total_tests >= num_tests)
        {
            state = EngineState.MOVESET;
        }
        return;
    }
}

int main(char[][] args)
{
    char[] ip = "127.0.0.1";
    ushort port = 40007;
    double num_tests = 10000;

    if (args.length > 1)
    {
        try {
            num_tests = atoi(args[1]);
            writefln("Number of trials set to %.0f", num_tests);
        } catch { }
    }

    ServerInterface server = new ServerInterface(new SocketServer(ip, port),
            format("ucb %.0f trials", num_tests), BOT_AUTHOR);
    writefln("Connected to server %s:%d", ip, port);
    Engine engine = new Engine();
    engine.num_tests = num_tests;

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

