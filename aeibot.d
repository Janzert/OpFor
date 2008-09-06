
/**
 * Base for implementing an Arimaa Engine Interface bot.
 */

import std.conv;
import std.format;
import std.string;
import std.stdio;
import std.socket;
import std.utf;

import tango.core.Thread;
import tango.core.sync.Mutex;
import tango.core.sync.Condition;

import logging;
import position;

pragma(lib, "ws2_32.lib");

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

class SQueue
{
    struct QMsg
    {
        QMsg* next;
        char[] msg;
    }
    QMsg* qhead = null;
    QMsg* qtail = null;
    QMsg* qbuf = null;

    Mutex mutex;
    Condition cnd;

    this()
    {
        mutex = new Mutex();
        cnd = new Condition(mutex);
    }

    char[] get(double timeout=0)
    {
        synchronized (mutex)
        {
            if (qhead is null && timeout != 0)
            {
                if (timeout > 0)
                {
                    cnd.wait(timeout);
                } else {
                    cnd.wait();
                }
            }

            if (qhead !is null)
            {
                QMsg* qmsg = qhead;
                qhead = qhead.next;
                char[] msg = qmsg.msg;
                qmsg.msg = null;
                qmsg.next = qbuf;
                qbuf = qmsg;
                if (qtail == qmsg)
                    qtail = null;

                return msg;
            }
            return null;
        }
    }

    void set(char[] msg)
    {
        synchronized (mutex)
        {
            QMsg* qmsg;
            if (qbuf !is null)
            {
                qmsg = qbuf;
                qbuf = qmsg.next;
            } else {
                qmsg = new QMsg();
            }

            qmsg.msg = msg;
            if (qtail !is null)
            {
                qtail.next = qmsg;
                qtail = qmsg;
            } else {
                qhead = qmsg;
                qtail = qmsg;
            }
            cnd.notify();
        }
    }
}

class _StdioCom : Thread
{
    SQueue inq;
    bool stop = false;

    this()
    {
        super(&run);
        inq = new SQueue();
    }

    void run()
    {
        char[] buf;
        while (!stop && ((buf = readln()) != null))
        {
            inq.set(buf);
        }
    }
}

class StdioServer : ServerConnection
{
    _StdioCom comt;

    this()
    {
        comt = new _StdioCom();
        comt.start();
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
        fwritef(stdout, msg);
        fflush(stdout);
    }
}

class SocketServer : ServerConnection
{
    TcpSocket sock;

    this(char[] ip, ushort port)
    {
        try
        {
            sock = new TcpSocket(new InternetAddress(ip, port));
            int bufsize;
            sock.setOption(SocketOptionLevel.SOCKET, SocketOption.SNDBUF, 24*1024);
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
            if (val == Socket.ERROR)
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
            if (val == Socket.ERROR)
                throw new Exception(format("Socket Error, sending. Sent %d bytes", sent));
            sent += val;
        }
    }
}


class ServerCmd
{
    enum CmdType {
        NONE,
        SETOPTION,
        CHECKEVAL,
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

class CheckCmd : ServerCmd
{
    bool current = false;
    char[] pos_str;
    Side side;

    this()
    {
        super(CmdType.CHECKEVAL);
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
                    case "checkeval":
                        CheckCmd c_cmd = new CheckCmd();
                        cmd_queue ~= c_cmd;
                        int six = find(line, "checkeval") + 9;
                        switch(stripl(line[six..length])[0])
                        {
                            case 'w':
                                c_cmd.side = Side.WHITE;
                                break;
                            case 'b':
                                c_cmd.side = Side.BLACK;
                                break;
                            case 'c':
                                c_cmd.current = true;
                                break;
                            default:
                                throw new Exception("Bad side sent in setposition from server.");
                        }
                        if (!c_cmd.current)
                        {
                            int pix = find(line, "[");
                            c_cmd.pos_str = strip(line[pix..length]);
                        }
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
        con.send(format("bestmove %s\n", move));
    }

    void info(char[] message)
    {
        con.send(format("info %s\n", message));
    }

    void log(char[] message)
    {
        con.send(format("log %s\n", message));
    }

    void warn(char[] message)
    {
        con.send(format("log Warning: %s\n", message));
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

    void start_search()
    {
        throw new NotImplementedException("AEIEngine.start_search() has not been implemented.");
    }

    void search(uint check_nodes, bool delegate() should_abort)
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

