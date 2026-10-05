
import core.sync.mutex;
import std.stdio : stderr;

import tango_compat;

interface LogConsumer
{
    void log(string);
    void error(string);
    void warn(string);
    void info(string);
}

class Logger
{
    LogConsumer[] consumers;
    bool to_console = false;
    Mutex console_lock;

    this()
    {
        console_lock = new Mutex();
        consumers.length = 0;
    }

    void register(LogConsumer c)
    {
        consumers ~= c;
    }

    private void _console_print(Args...)(const(char)[] fmt, Args args)
    {
        synchronized (console_lock)
        {
            stderr.writeln(Format(fmt, args));
        }
    }

    void console(Args...)(const(char)[] fmt, Args args)
    {
        if (to_console)
        {
            _console_print(fmt, args);
        }
    }

    void log(Args...)(const(char)[] fmt, Args args)
    {
        string message = Format(fmt, args);
        foreach(LogConsumer con; consumers)
        {
            con.log(message);
        }

        if (to_console)
            _console_print("log: {}", message);
    }

    void error(Args...)(const(char)[] fmt, Args args)
    {
        string message = Format(fmt, args);
        foreach(LogConsumer con; consumers)
        {
            con.error(message);
        }

        if (to_console)
            _console_print("Error: {}", message);
    }

    void warn(Args...)(const(char)[] fmt, Args args)
    {
        string message = Format(fmt, args);
        foreach(LogConsumer con; consumers)
        {
            con.warn(message);
        }

        if (to_console)
            _console_print("Warning: {}", message);
    }

    void info(Args...)(const(char)[] fmt, Args args)
    {
        string message = Format(fmt, args);
        foreach(LogConsumer con; consumers)
        {
            con.info(message);
        }
    }
}

