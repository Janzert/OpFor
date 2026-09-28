To build OpFor use LDC, the LLVM based D compiler (tested with 1.43). If
ldc2 is on the path, or the LDC environment variable names it, the script
build.py will build the bot.

Running build.py with no arguments builds an optimized executable. Giving
the argument "-static" to the script will build a statically linked executable.
Any other arguments will be passed directly to the compiler and will stop the
script from giving the compiler its own default arguments.

OpFor was originally written in D 1 with the Tango library. The last version
of that is tagged d1-final. The D 2 port gives identical search results; the
comments in d1_literals.d, alphabeta.d (TT_ENTRY_SIZE) and staticeval.d
(d1_int_shift) explain the places where that took care. The test tools
(eval_eval.d, goal_fuzzer.d, handicaptest.d, mcdud.d, parseboard.d,
trap_check.d, trap_fuzzer.d) have not been ported yet.

This software is being provided with a written authorization from Arimaa.com
and in compliance with "Section 3 of the Arimaa Public License".
Authorization #90819. Any rights granted by the end user license of this
software apply only to this software and do not extend to the Arimaa game. The
end user is responsible to ensure that any derivate work based on this software
complies with the Arimaa Public License and obtain any authorization or license
by contacting Arimaa.com. The Arimaa name is a trademark of Arimaa.com. The
Arimaa game is patented. The Arimaa game rules, the Arimaa board design and the
Arimaa piece design are copyright protected. The Arimaa Public License allows
cost free use of the Arimaa game for non-commercial use.

