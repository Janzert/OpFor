
import std.stdio;

import aeibot;
import position;

const char[] BOT_NAME = "AB";
const char[] BOT_AUTHOR = "Janzert";

class ABSearch
{
    const int WIN_SCORE = 32000;
    const int MAX_SCORE = 32767;
    const int MIN_SCORE = -32767;
    static Step nullstep;

    Position nullmove;
    Step[50][50] pvtable;
    int pvdepth = 0;
    int pvlength = 0;

    static this()
    {
        nullstep.set(INV_STEP, INV_STEP);
    }

    void copy_pv_up()
    {
        for (int i = pvdepth+1; i < pvlength; i++)
        {
            pvtable[pvdepth][i].set(pvtable[pvdepth][i]);
        }
    }

    int eval(Position pos)
    {
        return cast(int)FAME(pos);
    }

    int alphabeta(Position pos, int depth, int initialalpha, int initialbeta)
    {
        int score = MIN_SCORE;

        if (pos.is_endstate())
        {
            score = pos.endscore() * WIN_SCORE;
            if (pos.side == Side.BLACK)
            {
                score = -score;
            }
        } else if (depth < 1)
        {
            score = eval(pos);
        } else {
            int alpha = initialalpha;
            int beta = initialbeta;

            StepList steps = StepList.allocate();
            pos.get_steps(steps);

            pvlength++;

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

                    pvdepth++;
                    cal = -alphabeta(npos, depth-1, -beta, -alpha);
                    pvdepth--;

                    Position.free(nullmove);
                    nullmove = mynull;
                } else {
                    pvdepth++;
                    cal = alphabeta(npos, depth-1, alpha, beta);
                    pvdepth--;
                }

                if (cal > score)
                {
                    score = cal;

                    pvtable[pvdepth][pvdepth].copy(steps.steps[six]);
                    copy_pv_up();

                    if (cal > alpha)
                    {
                        alpha = cal;
                        if (cal >= beta)
                            break;
                    }
                }
            }

            StepList.free(steps);
        }
        return score;
    }
}


class Engine : AEIEngine
{

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
            state = EngineState.SEARCHING;
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

