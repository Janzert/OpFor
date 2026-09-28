#!/usr/bin/env python3
"""Build bot_opfor with LDC.

With no arguments this builds an optimized executable. "-static" builds a
statically linked one. Any other arguments are passed to the compiler in
place of the default optimization flags. Set LDC to use a compiler that
isn't ldc2 on the path.
"""

import os
import subprocess
import sys

SOURCES = ["bot_opfor.d", "aeibot.d", "alphabeta.d", "logging.d",
           "movement.d", "goalsearch.d", "position.d", "setupboard.d",
           "staticeval.d", "tango_compat.d", "trapmoves.d", "utility.d",
           "zobristkeys.d"]

OPTIMIZE = ["-O3", "-release", "-boundscheck=off"]


def main():
    args = sys.argv[1:]
    static = "-static" in args
    if static:
        args.remove("-static")
    if not args:
        args = OPTIMIZE
    cmd = [os.environ.get("LDC", "ldc2")] + args + SOURCES + ["-of=bot_opfor"]
    if static:
        cmd.append("-static")
    print(" ".join(cmd))
    return subprocess.call(cmd, cwd=os.path.dirname(os.path.abspath(__file__)))


if __name__ == "__main__":
    sys.exit(main())
