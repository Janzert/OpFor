
import tango.io.Stdout;
import tango.text.convert.Format;

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

    void console(char[] fmt, ...)
    {
        if (to_console)
        {
            Stderr(Stderr.layout.convert(_arguments, _argptr, fmt)).newline;
        }
    }

    void log(char[] fmt, ...)
    {
        char[] message = Format.convert(_arguments, _argptr, fmt);
        foreach(LogConsumer con; consumers)
        {
            con.log(message);
        }

        if (to_console)
            Stderr(Format("log: %s", message));
    }

    void warn(char[] fmt, ...)
    {
        char[] message = Format.convert(_arguments, _argptr, fmt);
        foreach(LogConsumer con; consumers)
        {
            con.warn(message);
        }

        if (to_console)
            Stderr(Format("log: %s", message));
    }

    void info(char[] fmt, ...)
    {
        char[] message = Format.convert(_arguments, _argptr, fmt);
        foreach(LogConsumer con; consumers)
        {
            con.info(message);
        }
    }
}

