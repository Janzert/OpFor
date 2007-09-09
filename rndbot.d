
import std.conv;
import std.socket;
import std.stdio;
import std.string;
import std.c.time;

import position;

const char[] BOT_NAME = "Random play";
const char[] BOT_AUTHOR = "Janzert";

void handleAEI()
{
    if (!feof(stdin))
    {
        char[] buf;
        while (!ferror(stdin))
        {
            char c = getc(stdin);
            buf ~= c;
            fwritef(stderr, ".%s", c);
        }
        fwritefln(stderr, "Buf: %s", buf);
        char[][] lines = splitlines(buf);
        for (int ix=0; ix < lines.length; ix++)
        {
            char[] line = stripl(lines[ix]);
            char[] cmd = tolower(split(line)[0]);
            switch(cmd)
            {
                case "isready":
                    writefln("readyok");
                    break;
                default:
                    fwritefln(stderr, "Unrecognized command: %s", cmd);
                    break;
            }
        }
    }
}

class TimeoutException : Exception
{
    this(char[] msg)
    {
        super(msg);
    }
}

interface ServerConnection
{
    void shutdown();
    char[] receive(float timeout=-1);
    void send(char[]);
}

class SocketServer : ServerConnection
{
    TcpSocket sock;

    this(char[] ip, ushort port)
    {
        sock = new TcpSocket(new InternetAddress(ip, port));
        sock.blocking(false);
    }

    ~this()
    {
        shutdown();
    }

    void shutdown()
    {
        if (sock !is null)
        {
            sock.shutdown(SocketShutdown.BOTH);
            sock.close();
            delete sock;
            sock = null;
        }
    }

    char[] receive(float timeout=-1)
    {
        SocketSet sset = new SocketSet(1);
        sset.add(sock);
        int ready_sockets;
        if (timeout < 0)
        {
            ready_sockets = Socket.select(sset, null, null);
        } else {
            ready_sockets = Socket.select(sset, null, null, cast(int)(timeout*1000*1000));
        }
        if (!ready_sockets)
            throw new TimeoutException("No data received.");

        const int bufsize = 5000;
        char[bufsize] buf;
        char[] resp;
        int val = 0;
        do {
            val = sock.receive(buf);
            if (val == Socket.ERROR)
            {
                throw new Exception("Socket Error");
            }
            resp ~= buf[0..val];
        } while (val == bufsize)
        return resp;
    }

    void send(char[] buf)
    {
        int sent = 0;
        while (sent < buf.length)
        {
            int val = sock.send(buf[sent..length]);
            if (val == sock.ERROR)
                throw new Exception("Socket Error");
            sent += val;
        }
    }
}

enum ServerCmd { NONE, ISREADY, QUIT, NEWGAME, GO };

struct GoCmd {
    enum Option { NONE, PONDER, INFINITE, GOAL, MOVETIME } 
    Option option;
    int time;
    int depth;
}

class ServerInterface
{
    ServerConnection con;
    char[] partial;

    ServerCmd[] cmd_queue;
    GoCmd go_options;

    this(ServerConnection cn)
    {
        con = cn;
        char[] greet = con.receive();
        if (cmp(strip(greet), "aei") != 0)
            throw new Exception("Invalid greeting from server.");
        con.send(format("id name %s\n", BOT_NAME));
        con.send(format("id author %s\n", BOT_AUTHOR));
        con.send("aeiok\n");
    }

    bool check(int timeout=0)
    {
        try
        {
            bool got_partial = false;
            char[] packet = con.receive(timeout);
            if (packet && packet[length-1] != '\n' && packet[length-1] != '\r')
            {
                got_partial = true;
            }
            if (partial)
            {
                packet = partial ~ packet;
                partial = "";
            }
            char[][] cmds = splitlines(packet);
            if (got_partial)
            {
                partial = cmds[length-1];
                cmds = cmds[0..length-1];
            }
            foreach (char[] line; cmds)
            {
                char[] cmd = strip(split(line)[0]);
                switch (cmd)
                {
                    case "isready":
                        cmd_queue ~= ServerCmd.ISREADY;
                        break;
                    case "quit":
                        cmd_queue ~= ServerCmd.QUIT;
                        break;
                    case "newgame":
                        cmd_queue ~= ServerCmd.NEWGAME;
                        break;
                    case "go":
                        cmd_queue ~= ServerCmd.GO;
                        char[][] words = split(line);
                        if (words.length > 1)
                        {
                            switch (strip(words[1]))
                            {
                                case "ponder":
                                    go_options.option = GoCmd.Option.PONDER;
                                    break;
                                case "infinite":
                                    go_options.option = GoCmd.Option.INFINITE;
                                    break;
                                case "goal":
                                    go_options.option = GoCmd.Option.GOAL;
                                    if (words.length < 3)
                                        throw new Exception("No search depth supplied for goal search");
                                    go_options.depth = toInt(strip(words[2]));
                                    break;
                                case "movetime":
                                    go_options.option = GoCmd.Option.MOVETIME;
                                    if (words.length < 3)
                                        throw new Exception("No time length supplied for movetime");
                                    go_options.time = toInt(strip(words[2]));
                                    break;
                                default:
                                throw new Exception("Unrecognized go command option");
                            }
                        }
                        break;
                    default:
                        throw new Exception("Unrecognized command.");
                }
            }
        }
        catch (TimeoutException e)
        {

        }
        return cast(bool)cmd_queue.length;
    }

    void readyok()
    {
        con.send("readyok\n");
    }

    void bestmove(char[] move)
    {
        con.send(format("bestmove %s\n", move));
    }

    ServerCmd current_cmd()
    {
        if (cmd_queue.length)
        {
            return cmd_queue[0];
        } else {
            return ServerCmd.NONE;
        }
    }

    bool clear_cmd()
    {
        if (cmd_queue)
        {
            cmd_queue = cmd_queue[1..length];
            return cast(bool)cmd_queue.length;
        }
        return false;
    }
}

enum EngineState { UNINITIALIZED, IDLE, SEARCHING, MOVESET };

class Engine
{
    EngineState state;
    char[] bestmove;

    Position position;
    Position[] past;
    char[][] moves;

    this()
    {
        state = EngineState.UNINITIALIZED;
    }

    void new_game()
    {
        position = new Position();
        past.length = 0;
        moves.length = 0;
        state = EngineState.IDLE;
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
                bestmove = "Ra8 Rb8 Rc8 Rd8 Re8 Rf8 Rg8 Rh8 Ha7 Db7 Cc7 Ed7 Me7 Cf7 Dg7 Hh7";
            } else {
                bestmove = "Ra8 Rb8 Rc8 Rd8 Re8 Rf8 Rg8 Rh8 Ha7 Db7 Cc7 Md7 Ee7 Cf7 Dg7 Hh7";
            }
            state = EngineState.MOVESET;
        }
    }
}

int main(char[][] args)
{
    char[] ip = "127.0.0.1";
    ushort port = 40007;


    ServerInterface server = new ServerInterface(new SocketServer(ip, port));
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
        while (server.current_cmd != ServerCmd.NONE)
        {
            switch (server.current_cmd)
            {
                case ServerCmd.ISREADY:
                    server.readyok();
                    server.clear_cmd();
                    break;
                case ServerCmd.QUIT:
                    writefln("Exiting by server command.");
                    return 0;
                case ServerCmd.NEWGAME:
                    writefln("Starting new game.");
                    engine.new_game();
                    server.clear_cmd();
                    break;
                case ServerCmd.GO:
                    writefln("searching move");
                    engine.start_search();
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
            default:
                break;
        }
    }
}


