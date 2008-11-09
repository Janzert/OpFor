#!/usr/bin/python

import sys

from subprocess import Popen

sourcefiles = ["bot_opfor.d", "aeibot.d", "alphabeta.d", "logging.d",
        "goalsearch.d", "position.d", "setupboard.d", "staticeval.d",
        "trapmoves.d", "zobristkeys.d", "Arguments.d"]
if len(sys.argv) > 1:
    cmd = ["dmd"] + sys.argv[1:] + sourcefiles
else:
    cmd = ["dmd", "-release", "-O", "-inline"] + sourcefiles
print " ".join(cmd)

p = Popen(cmd)
p.wait()

