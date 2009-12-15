
import tango.core.sync.Mutex;
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
    Mutex console_lock;

    this()
    {
        console_lock = new Mutex();
        consumers.length = 0;
    }

    void register(LogConsumer c)
    {
        consumers.length = consumers.length + 1;
        consumers[length-1] = c;
    }

    private
    {
    void _console_print(char[] fmt, ...)
    {
        _console_print(_arguments, _argptr, fmt);
    }

    void _console_print(TypeInfo[] _arguments, void* _argptr, char[] fmt)
    {
        synchronized (console_lock)
        {
            Stderr(Stderr.layout.convert(_arguments, _argptr, fmt)).newline;
        }
    }
    }


    void console(char[] fmt, ...)
    {
        if (to_console)
        {
            _console_print(_arguments, _argptr, fmt);
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
            _console_print("log: {}", message);
    }

    void warn(char[] fmt, ...)
    {
        char[] message = Format.convert(_arguments, _argptr, fmt);
        foreach(LogConsumer con; consumers)
        {
            con.warn(message);
        }

        if (to_console)
            _console_print("log: {}", message);
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

