/**
 * Small stand-ins for the parts of Tango that OpFor used before its port to
 * D2, so the engine code keeps its original shape: Tango-style format
 * strings, Time/TimeSpan/Clock/StopWatch, and Atomic.
 */
module tango_compat;

import core.atomic;
import core.time;
import std.algorithm : canFind;
import std.array : appender;
import std.string : stripRight;
import std.format : formattedWrite;
import std.conv : to;
import std.math : fabs, floor, isFinite;
import std.traits : isFloatingPoint, isIntegral, OriginalType;
static import stdio = std.stdio;

/**
 * Format with Tango placeholders: `{}` for the next argument, plus the
 * specifiers OpFor uses: `{:X}` (uppercase hex), `{:fN}` (N decimals) and
 * `{:.N}` (at most N decimals). Floats format like Tango's `{}`, with two decimals. Enums
 * format as their numeric value, as in Tango.
 */
string Format(Args...)(const(char)[] fmt, Args args)
{
    auto result = appender!string();
    size_t argix = 0;
    size_t i = 0;
    while (i < fmt.length)
    {
        if (fmt[i] != '{')
        {
            result.put(fmt[i++]);
            continue;
        }
        size_t close = i + 1;
        while (close < fmt.length && fmt[close] != '}')
            close++;
        if (close == fmt.length)
        {
            result.put(fmt[i .. $]);
            break;
        }
        const(char)[] spec = fmt[i + 1 .. close];
        i = close + 1;
        if (spec.length && spec[0] == ':')
            spec = spec[1 .. $];
        bool found = false;
        foreach (n, arg; args)
        {
            if (n == argix)
            {
                formatArg(result, spec, arg);
                found = true;
            }
        }
        if (!found)
            result.put("{}");
        argix++;
    }
    return result.data;
}

private void formatArg(W, T)(ref W w, const(char)[] spec, T arg)
{
    static if (is(T == enum))
    {
        formatArg(w, spec, cast(OriginalType!T) arg);
    }
    else static if (isFloatingPoint!T)
    {
        // {:fN} gives N decimals; {:.N} at most N, without trailing zeros.
        // Tango rounds halves away from zero.
        if (spec.length > 1 && spec[0] == 'f')
            formattedWrite(w, "%." ~ spec[1 .. $] ~ "f", roundHalfAway(arg, spec[1 .. $]));
        else if (spec.length > 1 && spec[0] == '.')
        {
            auto fixed = appender!string();
            formattedWrite(fixed, "%." ~ spec[1 .. $] ~ "f", roundHalfAway(arg, spec[1 .. $]));
            string digits = fixed.data;
            if (digits.canFind('.'))
                digits = digits.stripRight("0").stripRight(".");
            w.put(digits);
        }
        else if (isFinite(arg) && fabs(arg) >= 1e10)
            formattedWrite(w, "%.2e", arg);
        else
            formattedWrite(w, "%.2f", arg);
    }
    else static if (isIntegral!T)
    {
        if (spec == "X")
            formattedWrite(w, "%X", arg);
        else
            formattedWrite(w, "%d", arg);
    }
    else
    {
        formattedWrite(w, "%s", arg);
    }
}

private real roundHalfAway(real value, const(char)[] decimals)
{
    if (!isFinite(value))
        return value;
    real scale = 10.0L ^^ to!int(decimals);
    real scaled = floor(fabs(value) * scale + 0.5L) / scale;
    return value < 0 ? -scaled : scaled;
}

/// A span of time in 100ns ticks, like Tango's TimeSpan.
struct TimeSpan
{
    long ticks;

    enum TimeSpan zero = TimeSpan(0);

    static TimeSpan fromInterval(double seconds)
    {
        return TimeSpan(cast(long)(seconds * 10_000_000));
    }

    static TimeSpan fromSeconds(long seconds)
    {
        return TimeSpan(seconds * 10_000_000);
    }

    static TimeSpan fromMinutes(long minutes)
    {
        return TimeSpan(minutes * 60 * 10_000_000);
    }

    /// Length in seconds.
    double interval() const
    {
        return ticks / 10_000_000.0;
    }

    long seconds() const
    {
        return ticks / 10_000_000;
    }

    long minutes() const
    {
        return ticks / (60 * 10_000_000L);
    }

    TimeSpan opBinary(string op)(TimeSpan other) const
        if (op == "+" || op == "-")
    {
        return TimeSpan(mixin("ticks " ~ op ~ " other.ticks"));
    }

    TimeSpan opBinary(string op)(long n) const
        if (op == "*" || op == "/")
    {
        return TimeSpan(mixin("ticks " ~ op ~ " n"));
    }

    ref TimeSpan opOpAssign(string op)(TimeSpan other)
        if (op == "+" || op == "-")
    {
        mixin("ticks " ~ op ~ "= other.ticks;");
        return this;
    }

    int opCmp(TimeSpan other) const
    {
        return (ticks > other.ticks) - (ticks < other.ticks);
    }
}

/// A point in time, like Tango's Time. Measured on the monotonic clock.
struct Time
{
    long ticks;

    enum Time min = Time(long.min);
    enum Time max = Time(long.max);

    Time opBinary(string op)(TimeSpan span) const
        if (op == "+" || op == "-")
    {
        return Time(mixin("ticks " ~ op ~ " span.ticks"));
    }

    TimeSpan opBinary(string op : "-")(Time other) const
    {
        return TimeSpan(ticks - other.ticks);
    }

    ref Time opOpAssign(string op)(TimeSpan span)
        if (op == "+" || op == "-")
    {
        mixin("ticks " ~ op ~ "= span.ticks;");
        return this;
    }

    int opCmp(Time other) const
    {
        return (ticks > other.ticks) - (ticks < other.ticks);
    }
}

struct Clock
{
    static Time now()
    {
        return Time((MonoTime.currTime - MonoTime.zero).total!"hnsecs");
    }
}

/// Like Tango's StopWatch: stop() and microsec() measure from start().
struct StopWatch
{
    private MonoTime started;

    void start()
    {
        started = MonoTime.currTime;
    }

    /// Seconds since start().
    double stop()
    {
        return (MonoTime.currTime - started).total!"hnsecs" / 10_000_000.0;
    }

    ulong microsec()
    {
        return (MonoTime.currTime - started).total!"usecs";
    }
}

/// Like Tango's Atomic: a value shared between threads.
struct Atomic(T)
{
    private shared T value;

    T load()
    {
        return atomicLoad(value);
    }

    void store(T v)
    {
        atomicStore(value, v);
    }

    /// Store `v` only if the current value is `expected`.
    bool storeIf(T v, T expected)
    {
        return cas(&value, expected, v);
    }
}

/**
 * Like Tango's Stdout and Stderr, for the test tools: format and formatln
 * take Tango format strings, calling it prints its arguments separated by
 * ", ", and every method returns the output so calls chain.
 */
struct TangoOutput
{
    private bool to_stderr;

    private void put(const(char)[] s)
    {
        if (to_stderr)
            stdio.stderr.write(s);
        else
            stdio.stdout.write(s);
    }

    TangoOutput format(Args...)(const(char)[] fmt, Args args)
    {
        put(Format(fmt, args));
        return this;
    }

    TangoOutput formatln(Args...)(const(char)[] fmt, Args args)
    {
        put(Format(fmt, args));
        return newline();
    }

    TangoOutput opCall(Args...)(Args args)
    {
        foreach (i, arg; args)
        {
            if (i)
                put(", ");
            put(Format("{}", arg));
        }
        return this;
    }

    TangoOutput newline()
    {
        put("\n");
        return flush();
    }

    TangoOutput flush()
    {
        if (to_stderr)
            stdio.stderr.flush();
        else
            stdio.stdout.flush();
        return this;
    }
}

enum Stdout = TangoOutput(false);
enum Stderr = TangoOutput(true);

/// Seconds as a Duration, for waits that Tango took as a double.
Duration fromSeconds(double s)
{
    return dur!"hnsecs"(cast(long)(s * 10_000_000));
}

unittest
{
    assert(Format("a {} b {}", 1, "x") == "a 1 b x");
    assert(Format("{:X} {:X}", 255, 0xDEADBEEF12345678UL) == "FF DEADBEEF12345678");
    assert(Format("{} {}", 0.24, 1.0f) == "0.24 1.00");
    assert(Format("{:f1} {:.2}", 12.36, 1234.5678) == "12.4 1234.57");
    assert(Format("{:.2} {:.2} {:.2} {:f1}", 100.0, 87.1, 1e9, 0.0) == "100 87.1 1000000000 0.0");
    assert(Format("{:.2} {:f2} {:.2}", 90.625, 0.125, -2.675L) == "90.63 0.13 -2.68");
    assert(Format("{} {}", true, 'x') == "true x");
    enum E { A, B }
    assert(Format("{}", E.B) == "1");
    assert(Format("missing {}") == "missing {}");
    assert(Format("{}", 1e20) == "1.00e+20");
    assert(TimeSpan.fromInterval(1.5).seconds == 1);
    assert((TimeSpan.fromSeconds(2) * 4).interval == 8.0);
    assert(Time.max > Clock.now());
}
