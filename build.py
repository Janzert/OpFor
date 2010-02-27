#!/usr/bin/python

import os
import sys

from subprocess import Popen


library_path = os.path.expanduser("~/dmd/lib")

sourcefiles = ["bot_opfor.d", "aeibot.d", "alphabeta.d", "logging.d",
        "movement.d", "goalsearch.d", "position.d", "setupboard.d",
        "staticeval.d", "trapmoves.d", "utility.d", "zobristkeys.d",
        "Arguments.d"]


args = sys.argv[1:]
build_static = False
if len(args) and ("-static" in args):
    for i, arg in enumerate(args):
        if arg == "-static":
            args[i] = "-c"
            build_static = True
            break

if len(args) == 0 or (len(args) == 1
        and args[0] == "-c"):
    args += ["-release", "-O", "-inline"]

cmd = ["dmd"] + args + sourcefiles

print " ".join(cmd)
Popen(cmd).wait()

if build_static:
    cmd = ["gcc"]
    cmd += [f.replace(".d", ".o") for f in sourcefiles]
    cmd += ["-o", "bot_opfor", "-m32", "-static", "-Xlinker",
            "-L"+library_path, "-ltango-dmd", "-lpthread", "-lm"]
    print " ".join(cmd)
    Popen(cmd).wait()

