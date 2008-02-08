
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

class UnknownCommand : Exception
{
    char[] command;

    this(char[] msg, char[] cmd)
    {
        super(msg);
        this.command = cmd;
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
    enum CmdType { NONE,
        ISREADY,
        QUIT,
        NEWGAME,
        GO,
        STOP,
        MAKEMOVE,
        SETPOSITION,
        SETOPTION };

    CmdType type;

    this(CmdType t)
    {
        type = t;
    }
}

class GoCmd : ServerCmd
{
    enum Option { NONE, PONDER } 
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
    char[] move;

    this()
    {
        super(CmdType.MAKEMOVE);
    }
}

class PositionCmd : ServerCmd
{
    char[] pos_str;
    Side side;

    this()
    {
        super(CmdType.SETPOSITION);
    }
}

class OptionCmd : ServerCmd
{
    char[] name;
    char[] value;

    this()
    {
        super(CmdType.SETOPTION);
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
                                default:
                                    throw new Exception("Unrecognized go command option");
                            }
                        }
                        break;
                    case "stop":
                        cmd_queue ~= new ServerCmd(ServerCmd.CmdType.STOP);
                        break;
                    case "makemove":
                        MoveCmd move_cmd = new MoveCmd();
                        cmd_queue ~= move_cmd;
                        int mix = find(line, "makemove") + 8; // end of makemove
                        move_cmd.move = strip(line[mix..length]);
                        break;
                    case "setposition":
                        PositionCmd p_cmd = new PositionCmd();
                        cmd_queue ~= p_cmd;
                        int six = find(line, "setposition") + 11;
                        switch(stripl(line[six..length])[0])
                        {
                            case 'w':
                                p_cmd.side = Side.WHITE;
                                break;
                            case 'b':
                                p_cmd.side = Side.BLACK;
                                break;
                            default:
                                throw new Exception("Bad side sent in setposition from server.");
                        }
                        int pix = find(line, "[");
                        p_cmd.pos_str = strip(line[pix..length]);
                        break;
                    case "setoption":
                        OptionCmd option_cmd = new OptionCmd();
                        cmd_queue ~= option_cmd;
                        int nameix = find(line, "name") + 4;
                        int valueix = find(line, "value");
                        valueix = (valueix == -1) ? line.length : valueix;
                        option_cmd.name = strip(line[nameix..valueix]);
                        if (valueix != line.length)
                        {
                            option_cmd.value = strip(line[valueix+5..length]);
                        } else {
                            option_cmd.value = "";
                        }
                        break;
                    default:
                        throw new UnknownCommand("Unrecognized command.", line);
                }
            }
        } catch (TimeoutException e) { }

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

    void info(char[] msg)
    {
        con.send(format("info %s\n", msg));
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
    int ply;
    Position[] past;
    char[][] moves;

    this()
    {
        state = EngineState.UNINITIALIZED;
    }

    void new_game()
    {
        if (position !is null)
        {
            Position.free(position);
            foreach (Position pos; past)
            {
                Position.free(pos);
            }
        }
        position = Position.allocate();
        position.clear();
        ply = 1;
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
        ply += 1;
        bestmove = null;
        state = EngineState.IDLE;
    }

    void set_position(Side side, char[] pstr)
    {
        if (position !is null)
        {
            Position.free(position);
        }

        position = parse_short_str(side, 4, pstr);
        if (ply < 3)
        {
            ply = 3;
        }
        state = EngineState.IDLE;
    }
}

