
import std.random;
import std.stdio;
import std.string;

import position;
import aeibot;

const char[] BOT_NAME = "Random steps";
const char[] BOT_AUTHOR = "Janzert";

class Engine : AEIEngine
{
    Position search_pos;
    StepList search_steps;

    this()
    {
        super();
        search_steps = StepList.allocate();
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
            search_pos = position.dup;
            state = EngineState.SEARCHING;
        }
    }

    void search()
    {
        StepList steps = StepList.allocate();
        search_pos.get_steps(steps);
        if (steps.numsteps == 0)
        {
            if (search_pos == position)
                throw new ValueException("Trying to search on immobilized position.");

            search_pos = position.dup;
            search_steps.clear();
        } else {
            Step* nextstep = search_steps.newstep();
            nextstep.copy(steps.steps[rand() % steps.numsteps]);
            search_pos.do_step(*nextstep);
            if (search_pos.side != position.side)
            {
                Step nullstep;
                nullstep.set(INV_STEP, INV_STEP);
                search_pos.do_step(nullstep);
                if (search_pos != position)
                {
                    bestmove = search_steps.to_move_str(position);
                    search_pos = null;
                    state = EngineState.MOVESET;
                } else {
                    search_pos = position.dup;
                }
                search_steps.clear();
            }
        }
        StepList.free(steps);
        return;
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
                    engine.start_search();
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.MAKEMOVE:
                    MoveCmd mcmd = cast(MoveCmd)server.current_cmd;
                    engine.make_move(mcmd.move);
                    server.clear_cmd();
                    break;
                default:
                    throw new Exception("Unhandled server command in main loop.");
            }
        }

        switch (engine.state)
        {
            case EngineState.MOVESET:
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


