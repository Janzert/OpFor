
import std.math;
import std.random;
import std.stdio;
import std.string;

import position;
import aeibot;

const char[] BOT_AUTHOR = "Janzert";

typedef real function(Position) ScoreFunc;

real arimaa_score(Position pos)
{
    float wscore = 0;
    for (Piece i = Piece.WRABBIT; i <= Piece.WELEPHANT; i++)
    {
        wscore += popcount(pos.bitBoards[i]);
    }
    wscore *= popcount(pos.bitBoards[Piece.WRABBIT]);
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
        bscore += popcount(pos.bitBoards[i]);
    }
    bscore *= popcount(pos.bitBoards[Piece.BRABBIT]);
    float brpoints = 0;
    for (int rank = 1; rank <= 8; rank++)
    {
        ulong rmask = position.RANK_8 >> (8*(rank-1));
        brpoints += popcount(pos.bitBoards[Piece.BRABBIT] & rmask) * pow(cast(real)rank, 3);
    }
    bscore += brpoints;

    return wscore - bscore;
}

real FAME(Position pos)
{
    return position.FAME(pos);
}

class Engine : AEIEngine
{
    ScoreFunc score_pos;

    this(ScoreFunc s)
    {
        super();
        score_pos = s;
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
            state = EngineState.SEARCHING;
        }
    }

    void search()
    {
        PosStore moves = position.get_moves();
        Position[] bestpos;
        float bestscore;
        foreach(Position pos; moves)
        {
            float score;
            if (pos.is_endstate())
            {
                score = pos.endscore() * 100000;
            } else {
                score = score_pos(pos);
            }
            if (position.side == Side.BLACK)
            {
                score = -score;
            }
            if (bestscore != bestscore || score >= bestscore)
            {
                bestscore = score;
                if (score > bestscore)
                {
                    bestpos.length = 0;
                }

                bestpos ~= pos;
            }
        }
        
        if (bestpos.length > 0)
        {
            int r = rand() % bestpos.length;
            bestpos[0] = bestpos[r];
        }

        bestmove = moves.getpos(bestpos[0]).to_move_str(position);
        state = EngineState.MOVESET;
        moves.free_items();
        return;
    }
}

int main(char[][] args)
{
    char[] ip = "127.0.0.1";
    ushort port = 40007;

    bool fame = false;
    char[] name = "Arimaa score";

    if (args.length > 1)
    {
        if (icmp(args[1], "fame") == 0)
        {
            fame = true;
            name = "FAME score";
        }
    }

    ServerInterface server = new ServerInterface(new SocketServer(ip, port),
            name, BOT_AUTHOR);
    writefln("Connected to server %s:%d", ip, port);
    Engine engine;
    if (fame)
    {
        engine = new Engine(&FAME);
    } else {
        engine = new Engine(&arimaa_score);
    }

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


