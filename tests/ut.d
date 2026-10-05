/// Test runner main for `dub test`. Add new test modules here.
module ut;

import unit_threaded;

mixin runTestsMain!(
    "tango_compat",
    "movegen_test",
    "fuzz_test",
);
