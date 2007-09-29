
/**
 * Base for implementing an Arimaa Engine Interface bot.
 */

import std.conv;
import std.string;
import std.socket;

import position;

pragma(lib, "ws2_32.lib");

class NotImplementedException : Exception
{
    this(char[] msg)
    {
        super(msg);
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


class ServerCmd
{
    enum CmdType { NONE, ISREADY, QUIT, NEWGAME, GO, MAKEMOVE };
    CmdType type;

    this(CmdType t)
    {
        type = t;
    }
}

class GoCmd : ServerCmd
{
    enum Option { NONE, PONDER, INFINITE, GOAL, MOVETIME } 
    Option option;
    int time;
    int depth;

    this()
    {
        super(CmdType.GO);
    }

}

class MoveCmd : ServerCmd
{
    char [] move;

    this()
    {
        super(CmdType.MAKEMOVE);
    }
}

class ServerInterface
{
    ServerConnection con;
    char[] partial;

    ServerCmd[] cmd_queue;

    this(ServerConnection cn, char[] bot_name, char[] bot_author)
    {
        con = cn;
        char[] greet = con.receive();
        if (cmp(strip(greet), "aei") != 0)
            throw new Exception("Invalid greeting from server.");
        con.send(format("id name %s\n", bot_name));
        con.send(format("id author %s\n", bot_author));
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
                        cmd_queue ~= new ServerCmd(ServerCmd.CmdType.ISREADY);
                        break;
                    case "quit":
                        cmd_queue ~= new ServerCmd(ServerCmd.CmdType.QUIT);
                        break;
                    case "newgame":
                        cmd_queue ~= new ServerCmd(ServerCmd.CmdType.NEWGAME);
                        break;
                    case "go":
                        GoCmd go_cmd = new GoCmd();
                        cmd_queue ~= go_cmd;
                        char[][] words = split(line);
                        if (words.length > 1)
                        {
                            switch (strip(words[1]))
                            {
                                case "ponder":
                                    go_cmd.option = GoCmd.Option.PONDER;
                                    break;
                                case "infinite":
                                    go_cmd.option = GoCmd.Option.INFINITE;
                                    break;
                                case "goal":
                                    go_cmd.option = GoCmd.Option.GOAL;
                                    if (words.length < 3)
                                        throw new Exception("No search depth supplied for goal search");
                                    go_cmd.depth = toInt(strip(words[2]));
                                    break;
                                case "movetime":
                                    go_cmd.option = GoCmd.Option.MOVETIME;
                                    if (words.length < 3)
                                        throw new Exception("No time length supplied for movetime");
                                    go_cmd.time = toInt(strip(words[2]));
                                    break;
                                default:
                                throw new Exception("Unrecognized go command option");
                            }
                        }
                        break;
                    case "makemove":
                        MoveCmd move_cmd = new MoveCmd();
                        cmd_queue ~= move_cmd;
                        int mix = find(line, "makemove") + 8; // end of makemove
                        move_cmd.move = strip(line[mix..length]);
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
            return null;
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

class AEIEngine
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
        throw new NotImplementedException("AEIEngine.start_search() has not been implemented.");
    }

    void search()
    {
        throw new NotImplementedException("AEIEngine.search() has not been implemented.");
    }

    void make_move(char[] move)
    {
        past ~= position.dup;
        moves ~= move;
        position.do_str_move(move);
        bestmove = null;
        state = EngineState.IDLE;
    }
}

