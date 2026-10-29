/// Test runner main for `dub test`. Add new test modules here.
module ut;

import std.meta : AliasSeq;
import unit_threaded;

alias Modules = AliasSeq!(
    "tango_compat",
    "movegen_test",
    "fuzz_test",
    "goal_test",
    "eval_test",
    "search_test",
    "tunables_test",
);

// Otherwise druntime runs the unittest blocks itself before main.
mixin disableDefaultRunner;

/// Like unit-threaded's runTestsMain, except that tests tagged "tunables"
/// run after the others, on one thread. They change the tunable values
/// every other test reads (setting one rebuilds whole tables in place), so
/// running them alongside the rest made those tests fail now and then.
int main(string[] args)
{
    import std.algorithm : any, canFind, filter;
    import std.array : array;
    import unit_threaded.runner.factory : isWantedTest;
    import unit_threaded.runner.options : Options;
    import unit_threaded.runner.reflection : allTestData;
    import unit_threaded.runner.runner : runTests;

    // Options' getopt rearranges the array it's given.
    auto options = Options(args.dup);
    auto all = allTestData!Modules;
    if (options.exit)
        return runTests(options, all);

    auto rest = all.filter!(t => !t.tags.canFind("tunables")).array;
    auto writers = all.filter!(t => t.tags.canFind("tunables")).array;
    // A group none of the named tests are in would report an error. With
    // none in either, let unit-threaded report it.
    bool wanted(typeof(all) group)
    {
        return group.any!(t => isWantedTest(t, options.testsToRun));
    }
    if (!wanted(rest) && !wanted(writers))
        return runTests(options, all);

    int result = 0;
    if (wanted(rest))
        result |= runTests(options, rest);
    if (wanted(writers))
    {
        options.numThreads = 1;
        result |= runTests(options, writers);
    }
    return result;
}
