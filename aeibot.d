
/**
 * Base for implementing an Arimaa Engine Interface bot.
 */

import tango.core.Exception;
import tango.core.Thread;
import tango.core.sync.Mutex;
import tango.core.sync.Condition;
import tango.io.Console;
import tango.io.Stdout;
import tango.net.device.Socket;
import tango.text.convert.Format;
import tango.text.Text;
import tango.text.Util;
import tango.time.Time;

import logging;
import position;
import utility;

version(windows)
{
    pragma(lib, "ws2_32.lib");
}

private int find(char[] src, char[] pattern)
{
    int index = locatePattern!(char)(src, pattern);
    if (index == src.length)
        index = -1;
    return index;
}

class NotImplementedException : Exception
{
    this(char[] msg)
    {
        super(msg);
    }
}

class ConnectException : Exception
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

class _StdioCom : Thread
{
    Queue!(char[]) inq;
    bool stop = false;

    this()
    {
        super(&run);
        inq = new Queue!(char[])();
        isDaemon(true);
    }

    void run()
    {
        try
        {
            char[] buf;
            while (!stop && Cin.readln(buf, true))
            {
                inq.set(buf.dup);
            }
        }
        catch (Exception err)
        {
            if (!stop)
            {
                void writer(char[] str)
                {
                    Stderr(str);
                }
                Stderr("Caught error in stdin thread:").newline;
                err.writeOut(&writer);
                Stderr.newline;
            }
        }
    }
}

class StdioServer : ServerConnection
{
    _StdioCom comt;
    Mutex out_lock;

    this()
    {
        out_lock = new Mutex();
        comt = new _StdioCom();
        comt.start();
    }

    ~this()
    {
        shutdown();
    }

    void shutdown()
    {
        comt.stop = true;
    }

    char[] receive(float timeout=-1)
    {
        char[] msg = comt.inq.get(timeout);
        if (msg is null)
            throw new TimeoutException("No data received");
        return msg;
    }

    void send(char[] msg)
    {
        synchronized (out_lock)
        {
            Stdout(msg);
            Stdout.flush();
        }
    }
}

class SocketServer : ServerConnection
{
    Berkeley sock;

    this(char[] ip, ushort port)
    {
        try
        {
            sock.open(AddressFamily.INET, SocketType.STREAM,
                    ProtocolType.TCP);
            sock.connect(new IPv4Address(ip, port));
            int[1] send_buffer_size = 24 * 1024;
            sock.setOption(SocketOptionLevel.SOCKET, SocketOption.SNDBUF,
                    cast(void[])send_buffer_size);
        } catch (SocketException e)
        {
            throw new ConnectException(e.msg);
        }
        sock.blocking(false);
    }

    ~this()
    {
        shutdown();
    }

    void shutdown()
    {
        if (sock.isAlive())
        {
            sock.shutdown(SocketShutdown.BOTH);
            sock.detach();
            //delete sock;
            //sock = null;
        }
    }

    char[] receive(float timeout=-1)
    {
        SocketSet sset = new SocketSet(1);
        SocketSet null_set = cast(SocketSet)null;
        sset.add(&sock);
        int ready_sockets;
        if (timeout < 0)
        {
            ready_sockets = SocketSet.select(sset, null_set, null_set);
        } else {
            long utimeout = cast(long)(timeout * 1000000);
            ready_sockets = SocketSet.select(sset, null_set, null_set,
                    utimeout);
        }
        if (!ready_sockets)
        {
            if (sock.isAlive())
                throw new TimeoutException("No data received.");
            else
                throw new Exception("Socket Error, not alive");
        }

        const int bufsize = 5000;
        char[bufsize] buf;
        char[] resp;
        bool gotresponse = false;
        int val = 0;
        do {
            val = sock.receive(buf);
            if (val == SOCKET_ERROR)
            {
                throw new Exception("Socket Error, receiving");
            } else if (val > 0)
            {
                gotresponse = true;
            }
            resp ~= buf[0..val];
        } while (val == bufsize)
        if (!gotresponse)
        {
            throw new Exception("Socket closed");
        }
        return resp;
    }

    void send(char[] buf)
    {
        int sent = 0;
        while (sent < buf.length)
        {
            int val = sock.send(buf[sent..length]);
            if (val == SOCKET_ERROR)
                throw new Exception(Format("Socket Error, sending. Sent {} bytes", sent));
            sent += val;
        }
    }
}


class ServerCmd
{
    enum CmdType {
        NONE,
        SETOPTION,
        GO,
        ISREADY,
        CRITICAL,   // Any commands past this are critical to handle ASAP
                    // i.e. stop the current search for
        NEWGAME,
        MAKEMOVE,
        SETPOSITION,
        STOP,
        QUIT,
    };

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

class ServerInterface : LogConsumer
{
    ServerConnection con;
    char[] partial;

    ServerCmd[] cmd_queue;
    bool have_critical = false;

    this(ServerConnection cn, char[] bot_name, char[] bot_author)
    {
        con = cn;
        auto greet = new Text!(char)(con.receive());
        greet.trim();
        if (!greet.equals("aei"))
            throw new Exception("Invalid greeting from server.");
        con.send("protocol-version 1\n");
        con.send(Format("id name {}\n", bot_name));
        con.send(Format("id author {}\n", bot_author));
        con.send("aeiok\n");
    }

    void shutdown()
    {
        con.shutdown();
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
            char[][] cmds = splitLines!(char)(packet)[0..length-1];
            if (got_partial)
            {
                if (cmds.length)
                {
                    partial = cmds[length-1];
                    cmds = cmds[0..length-1];
                } else {
                    partial = packet;
                }
            }
            foreach (char[] line; cmds)
            {
                char[] cmd = trim!(char)(delimit!(char)(line, " \t\n")[0]);
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
                        char[][] words = delimit!(char)(line, " \t");
                        if (words.length > 1)
                        {
                            switch (trim!(char)(words[1]))
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
                        // find end of makemove
                        int mix = find(line, "makemove") + 8;
                        move_cmd.move = trim!(char)(line[mix..length]);
                        break;
                    case "setposition":
                        PositionCmd p_cmd = new PositionCmd();
                        cmd_queue ~= p_cmd;
                        int six = find(line, "setposition") + 11;
                        switch(triml!(char)(line[six..length])[0])
                        {
                            case 'g':
                                p_cmd.side = Side.WHITE;
                                break;
                            case 's':
                                p_cmd.side = Side.BLACK;
                                break;
                            default:
                                throw new Exception("Bad side sent in setposition from server.");
                        }
                        int pix = find(line, "[");
                        p_cmd.pos_str = trim!(char)(line[pix..length]);
                        break;
                    case "setoption":
                        OptionCmd option_cmd = new OptionCmd();
                        cmd_queue ~= option_cmd;
                        int nameix = find(line, "name") + 4;
                        int valueix = find(line, "value");
                        valueix = (valueix == -1) ? line.length : valueix;
                        option_cmd.name = trim!(char)(line[nameix..valueix]);
                        if (valueix != line.length)
                        {
                            option_cmd.value = trim!(char)(line[valueix+5..length]);
                        } else {
                            option_cmd.value = "";
                        }
                        break;
                    default:
                        throw new UnknownCommand("Unrecognized command.", line);
                }
                if (cmd_queue[0].type > ServerCmd.CmdType.CRITICAL)
                    have_critical = true;
            }
        } catch (TimeoutException e) { }

        return cast(bool)cmd_queue.length;
    }

    bool should_abort()
    {
        return check() && have_critical;
    }

    void readyok()
    {
        con.send("readyok\n");
    }

    void bestmove(char[] move)
    {
        con.send(Format("bestmove {}\n", move));
    }

    void info(char[] message)
    {
        con.send(Format("info {}\n", message));
    }

    void log(char[] message)
    {
        con.send(Format("log {}\n", message));
    }

    void warn(char[] message)
    {
        con.send(Format("log Warning: {}\n", message));
    }

    void error(char[] message)
    {
        con.send(Format("log Error: {}\n", message));
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
            have_critical = false;
            if (cmd_queue[0].type > ServerCmd.CmdType.CRITICAL
                    && cmd_queue.length > 1)
            {
                for (int i=1; i < cmd_queue.length; i++)
                {
                    if (cmd_queue[i].type > ServerCmd.CmdType.CRITICAL)
                    {
                        have_critical = true;
                        break;
                    }
                }
            }
            cmd_queue = cmd_queue[1..length];
            return cast(bool)cmd_queue.length;
        }
        return false;
    }

    static bool is_standard_option(char[] n)
    {
        static char[][] stdopts = ["tcmove", "tcreserve", "tcpercent", "tcmax",
            "tctotal", "tcturns", "tcturntime", "greserve", "sreserve",
            "gused", "sused", "lastmoveused", "moveused", "opponent",
            "opponent_rating", "rated", "event", "hash", "depth"];
        auto name = new Text!(char)(n);
        for (int i=0; i < stdopts.length; i++)
        {
            if (name.equals(stdopts[i]) == 0)
            {
                return true;
            }
        }
        return false;
    }
}

enum EngineState { UNINITIALIZED, IDLE, SEARCHING, MOVESET };

class AEIEngine
{
    Logger logger;

    EngineState state;
    char[] bestmove;

    Position position;
    int ply;
    Position[] past;
    char[][] moves;

    this(Logger l)
    {
        logger = l;
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

    void cleanup_search()
    {
        throw new NotImplementedException("AEIEngine.cleanup_search() has not been implemented.");
    }

    void start_search()
    {
        throw new NotImplementedException("AEIEngine.start_search() has not been implemented.");
    }

    void search(double check_time, bool delegate() should_abort)
    {
        throw new NotImplementedException("AEIEngine.search() has not been implemented.");
    }

    void set_bestmove()
    {
        throw new NotImplementedException("AEIEngine.set_bestmove() has not been implemented.");
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

