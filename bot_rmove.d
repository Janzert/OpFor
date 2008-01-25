
import std.gc;
import std.random;
import std.stdio;
import std.string;

import position;
import aeibot;

const char[] BOT_NAME = "Random moves";
const char[] BOT_AUTHOR = "Janzert";

class Engine : AEIEngine
{
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
            state = EngineState.SEARCHING;
        }
    }

    void search()
    {
        PosStore moves = position.get_moves();
        int r = rand() % moves.length;
        int i = 0;
        moves.checktable();
        bool mademove = false;
        foreach (Position p; moves)
        {
            if (i == r)
            {
                bestmove = moves.getpos(p).to_move_str(position);
                mademove = true;
                break;
            }
            i++;
        }
        if (!mademove)
            throw new Exception(format("No move made r %d i %d l %d", r, i, moves.length));
        moves.free_items();
        state = EngineState.MOVESET;
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
                    writefln("Starting new game.");
                    engine.new_game();
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.GO:
                    writefln("searching move");
                    engine.start_search();
                    server.clear_cmd();
                    break;
		case ServerCmd.CmdType.STOP:
		    server.clear_cmd();
		    break;
                case ServerCmd.CmdType.MAKEMOVE:
                    MoveCmd mcmd = cast(MoveCmd)server.current_cmd;
                    writefln("received move %s", mcmd.move);
                    engine.make_move(mcmd.move);
                    writefln(engine.position.to_long_str());
                    server.clear_cmd();
                    break;
		case ServerCmd.CmdType.SETOPTION:
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
                std.gc.fullCollect();
                break;
            default:
                break;
        }
    }
}


