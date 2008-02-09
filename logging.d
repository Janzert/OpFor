
import std.format;
import std.stdio;
import std.utf;

interface LogConsumer
{
    void log(char[]);
    void warn(char[]);
    void info(char[]);
}

class Logger
{
    LogConsumer[] consumers;
    bool to_console = false;

    this()
    {
        consumers.length = 0;
    }

    void register(LogConsumer c)
    {
        consumers.length = consumers.length + 1;
        consumers[length-1] = c;
    }

    void console(...)
    {
        if (to_console)
        {
            char[] message;
            void putc(dchar c)
            {
                std.utf.encode(message, c);
            }
            std.format.doFormat(&putc, _arguments, _argptr);

            writefln(message);
        }
    }

    void log(...)
    {
        char[] message;
        void putc(dchar c)
        {
            std.utf.encode(message, c);
        }
        std.format.doFormat(&putc, _arguments, _argptr);

        foreach(LogConsumer con; consumers)
        {
            con.log(message);
        }

        if (to_console)
            writefln("log: %s", message);
    }

    void warn(...)
    {
        char[] message;
        void putc(dchar c)
        {
            std.utf.encode(message, c);
        }
        std.format.doFormat(&putc, _arguments, _argptr);

        foreach(LogConsumer con; consumers)
        {
            con.warn(message);
        }

        if (to_console)
            writefln("Warning: %s", message);
    }

    void info(...)
    {
        char[] message;
        void putc(dchar c)
        {
            std.utf.encode(message, c);
        }
        std.format.doFormat(&putc, _arguments, _argptr);

        foreach(LogConsumer con; consumers)
        {
            con.info(message);
        }
    }
}

