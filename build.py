#!/usr/bin/env python3
"""Build bot_opfor, or the test tools, with LDC.

    build.py [-static] [compiler args]   build bot_opfor
    build.py tools [compiler args]       build the test tools

With no compiler arguments the bot is optimized and the tools are built
optimized with assertions on. "-static" builds a statically linked bot.
Other arguments are passed to the compiler in place of the defaults. Set
LDC to use a compiler that isn't ldc2 on the path.
"""

import os
import subprocess
import sys

SOURCES = ["bot_opfor.d", "aeibot.d", "alphabeta.d", "logging.d",
           "movement.d", "goalsearch.d", "position.d", "setupboard.d",
           "staticeval.d", "tango_compat.d", "trapmoves.d", "utility.d",
           "zobristkeys.d"]
ENGINE = [s for s in SOURCES if s != "bot_opfor.d"]

# Each tool's own sources. The movement tester is the test code in
# movement.d, compiled in with a debug identifier.
TOOLS = {
    "eval_eval": ["eval_eval.d"],
    "goal_fuzzer": ["goal_fuzzer.d"],
    "handicaptest": ["handicaptest.d"],
    "mcdud": ["mcdud.d"],
    "movement": ["-d-debug=test_movement"],
    "parseboard": ["parseboard.d", "trap_check.d"],
    "trap_fuzzer": ["trap_fuzzer.d", "trap_check.d"],
}

OPTIMIZE = ["-O3", "-release", "-boundscheck=off"]
TOOL_FLAGS = ["-O2", "-g"]


def compile(args, sources, output):
    if os.name == "nt":
        output += ".exe"
    cmd = [os.environ.get("LDC", "ldc2")] + args + sources + ["-of=" + output]
    print(" ".join(cmd))
    return subprocess.call(cmd, cwd=os.path.dirname(os.path.abspath(__file__)))


def main():
    args = sys.argv[1:]
    if args[:1] == ["tools"]:
        args = args[1:] or TOOL_FLAGS
        status = 0
        for name, sources in TOOLS.items():
            status |= compile(args, sources + ENGINE, name)
        return status
    static = "-static" in args
    if static:
        args.remove("-static")
    if not args:
        args = OPTIMIZE
    if static:
        args.append("-static")
    return compile(args, SOURCES, "bot_opfor")


if __name__ == "__main__":
    sys.exit(main())
