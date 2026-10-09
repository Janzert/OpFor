
/**
 * Base for implementing an Arimaa Engine Interface bot.
 */

import core.stdc.errno : EINTR, errno;
import core.sync.mutex;
import core.thread;
import std.algorithm : canFind, splitter;
import std.array : array;
import std.socket;
import std.stdio : stderr, stdout;
import std.string : indexOf, indexOfAny, strip, stripLeft;

import tango_compat;

import logging;
import position;
import utility;

version(Windows)
{
    pragma(lib, "ws2_32.lib");
    // The C runtime's name for POSIX read.
    extern(C) nothrow @nogc int _read(int fd, void* buf, uint count);
    alias read = _read;
}
else
{
    import core.sys.posix.unistd : read;
}

private int find(const(char)[] src, const(char)[] pattern)
{
    return cast(int)indexOf(src, pattern);
}

class NotImplementedException : Exception
{
    this(string msg)
    {
        super(msg);
    }
}

class ConnectException : Exception
{
    this(string msg)
    {
        super(msg);
    }
}

class TimeoutException : Exception
{
    this(string msg)
    {
        super(msg);
    }
}

class UnknownCommand : Exception
{
    string command;

    this(string msg, string cmd)
    {
        super(msg);
        this.command = cmd;
    }
}

interface ServerConnection
{
    void shutdown();
    string receive(float timeout=-1);
    void send(const(char)[]);
}

class _StdioCom : Thread
{
    Queue!(string) inq;
    bool stop = false;

    this()
    {
        super(&run);
        inq = new Queue!(string)();
        isDaemon = true;
    }

    void run()
    {
        try
        {
            // Read the descriptor directly. std.stdio's readln holds the
            // stdin FILE lock while it blocks, which deadlocks the C runtime
            // flushing streams at exit.
            char[4096] buf;
            string pending;
            while (!stop)
            {
                auto got = read(0, buf.ptr, buf.length);
                if (got < 0 && errno == EINTR)
                    continue;
                if (got <= 0) // end of input or error
                {
                    // The controller is gone (closed our stdin or died), so
                    // quit rather than wait forever as an orphan.
                    if (pending.length)
                        inq.set(pending ~ "\n");
                    inq.set("quit\n");
                    break;
                }
                pending ~= buf[0..got];
                ptrdiff_t eol;
                while ((eol = indexOf(pending, '\n')) >= 0)
                {
                    inq.set(pending[0..eol+1]);
                    pending = pending[eol+1..$];
                }
            }
        }
        catch (Exception err)
        {
            if (!stop)
            {
                stderr.writeln("Caught error in stdin thread:");
                stderr.writeln(err);
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

    string receive(float timeout=-1)
    {
        string msg = comt.inq.get(timeout);
        if (msg is null)
            throw new TimeoutException("No data received");
        return msg;
    }

    void send(const(char)[] msg)
    {
        synchronized (out_lock)
        {
            stdout.write(msg);
            stdout.flush();
        }
    }
}

class SocketServer : ServerConnection
{
    Socket sock;

    this(string ip, ushort port)
    {
        try
        {
            sock = new TcpSocket();
            sock.connect(new InternetAddress(ip, port));
            sock.setOption(SocketOptionLevel.SOCKET, SocketOption.SNDBUF,
                    24 * 1024);
        } catch (SocketException e)
        {
            throw new ConnectException(e.msg);
        }
        sock.blocking = false;
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
            sock.close();
        }
    }

    string receive(float timeout=-1)
    {
        SocketSet sset = new SocketSet(1);
        sset.add(sock);
        int ready_sockets;
        if (timeout < 0)
        {
            ready_sockets = Socket.select(sset, null, null);
        } else {
            ready_sockets = Socket.select(sset, null, null,
                    fromSeconds(timeout));
        }
        if (!ready_sockets)
        {
            if (sock.isAlive())
                throw new TimeoutException("No data received.");
            else
                throw new Exception("Socket Error, not alive");
        }

        enum int bufsize = 5000;
        char[bufsize] buf;
        string resp;
        bool gotresponse = false;
        ptrdiff_t val = 0;
        do {
            val = sock.receive(buf[]);
            if (val == Socket.ERROR)
            {
                throw new Exception("Socket Error, receiving");
            } else if (val > 0)
            {
                gotresponse = true;
            }
            resp ~= buf[0..val];
        } while (val == bufsize);
        if (!gotresponse)
        {
            throw new Exception("Socket closed");
        }
        return resp;
    }

    void send(const(char)[] buf)
    {
        size_t sent = 0;
        while (sent < buf.length)
        {
            auto val = sock.send(buf[sent..$]);
            if (val == Socket.ERROR)
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
    string move;

    this()
    {
        super(CmdType.MAKEMOVE);
    }
}

class PositionCmd : ServerCmd
{
    string pos_str;
    Side side;

    this()
    {
        super(CmdType.SETPOSITION);
    }
}

class OptionCmd : ServerCmd
{
    string name;
    string value;

    this()
    {
        super(CmdType.SETOPTION);
    }
}

class ServerInterface : LogConsumer
{
    ServerConnection con;
    string partial;

    ServerCmd[] cmd_queue;
    bool have_critical = false;

    this(ServerConnection cn, string bot_name, string bot_author)
    {
        con = cn;
        if (strip(con.receive()) != "aei")
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
            string packet = partial ~ con.receive(timeout);
            // Handle complete lines, keeping any unterminated rest for the
            // next packet.
            auto end = packet.length;
            while (end > 0 && packet[end-1] != '\n')
                end--;
            partial = packet[end..$];
            string[] cmds;
            foreach (line; packet[0..end].splitter('\n'))
            {
                if (line.length && line[$-1] == '\r')
                    line = line[0..$-1];
                cmds ~= line;
            }
            if (cmds.length)
                cmds = cmds[0..$-1]; // the empty rest after the last newline
            foreach (string line; cmds)
            {
                auto cmd_end = indexOfAny(line, " \t\n");
                string cmd = strip(cmd_end < 0 ? line : line[0..cmd_end]);
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
                        string[] words = line.splitter!(c => c == ' ' || c == '\t').array;
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
                        // find end of makemove
                        int mix = find(line, "makemove") + 8;
                        move_cmd.move = strip(line[mix..$]);
                        break;
                    case "setposition":
                        PositionCmd p_cmd = new PositionCmd();
                        cmd_queue ~= p_cmd;
                        int six = find(line, "setposition") + 11;
                        switch(stripLeft(line[six..$])[0])
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
                        p_cmd.pos_str = strip(line[pix..$]);
                        break;
                    case "setoption":
                        OptionCmd option_cmd = new OptionCmd();
                        cmd_queue ~= option_cmd;
                        int nameix = find(line, "name") + 4;
                        int valueix = find(line, "value");
                        valueix = (valueix == -1) ? cast(int)line.length : valueix;
                        option_cmd.name = strip(line[nameix..valueix]);
                        if (valueix != line.length)
                        {
                            option_cmd.value = strip(line[valueix+5..$]);
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

    void bestmove(string move)
    {
        con.send(Format("bestmove {}\n", move));
    }

    void info(string message)
    {
        con.send(Format("info {}\n", message));
    }

    void log(string message)
    {
        con.send(Format("log {}\n", message));
    }

    void warn(string message)
    {
        con.send(Format("log Warning: {}\n", message));
    }

    void error(string message)
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
            cmd_queue = cmd_queue[1..$];
            return cast(bool)cmd_queue.length;
        }
        return false;
    }

    static bool is_standard_option(string n)
    {
        static immutable string[] stdopts = ["tcmove", "tcreserve",
            "tcpercent", "tcmax", "tctotal", "tcturns", "tcturntime",
            "greserve", "sreserve", "gused", "sused", "lastmoveused",
            "moveused", "opponent", "opponent_rating", "rated", "event",
            "hash", "depth"];
        return stdopts.canFind(n);
    }
}

enum EngineState { UNINITIALIZED, IDLE, SEARCHING, MOVESET };

class AEIEngine
{
    Logger logger;

    EngineState state;
    string bestmove;

    Position position;
    int ply;
    Position[] past;
    string[] moves;
    int checked_moves;

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

    void make_move(string move)
    {
        past ~= position.dup;
        moves ~= move;
        position.do_str_move(move);
        ply += 1;
        bestmove = null;
        state = EngineState.IDLE;
    }

    void set_position(Side side, string pstr)
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

