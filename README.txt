OpFor is an Arimaa engine that talks the Arimaa Engine Interface (AEI)
protocol. See https://github.com/Janzert/AEI for the protocol and for tools
to run engines against each other or on a game server.

Building
--------

Build OpFor with LDC, the LLVM based D compiler (tested with 1.43 on 64-bit
Linux). If ldc2 is on the path, or the LDC environment variable names it,
the script build.py builds bot_opfor:

    python3 build.py

With no arguments it builds an optimized executable. "-static" builds a
statically linked executable. Any other arguments are passed to the compiler
in place of the default optimization flags.

Running
-------

By default bot_opfor talks AEI over stdin/stdout and uses the multithreaded
search. Command line options:

    --seq               single threaded search (deterministic at a fixed
                        depth, useful for testing)
    --threads           multithreaded search (the default)
    --server, -s IP     connect to a controller over TCP instead of stdio
    --port, -p PORT     port for --server (default 40015)
    --stdio, --socket   choose the connection explicitly
    --help              list the options

Besides the standard AEI time control options, setoption accepts:

    depth               fixed search depth in steps (4 or more), or
                        "infinite" to use the time control
    hash                transposition table size in MB (default 10)
    threads             number of search threads for --threads
    target_min_time, target_max_time
                        seconds to aim for, independent of the time control
    setup_rabbits       ANY, STANDARD, 99OF9 or FRITZ
    setup_random_minor  1 to randomize the minor pieces in the setup
    log_console         true to echo the log to stderr
    check_eval          log an evaluation breakdown of the current position

Search tuning options (true or false): history, capture_sort, use_killers,
prune_unrelated, use_lmr, use_nmh, use_early_beta, and for --seq, root_lmr
and opening_book (1 or 0). The eval_* options set evaluation weights.

History
-------

OpFor was written in D 1 with the Tango library and played in the Arimaa
Computer Championships 2008 to 2011 (see the ArimaaCC_* tags). The last D 1
version is tagged d1-final. The port to D 2 gives search results identical
to that version. The comments in d1_literals.d, alphabeta.d (TT_ENTRY_SIZE)
and staticeval.d (d1_int_shift) explain where that took care.

The port changed behavior only outside normal play:

- A position with no legal moves gets a warning and an empty bestmove
  rather than a crash.
- setoption warns about unrecognized options (the check was inverted).
- Commands split across socket packets are put back together correctly.
- Moves may be separated by any amount of whitespace.

The test tools (eval_eval.d, goal_fuzzer.d, handicaptest.d, mcdud.d,
parseboard.d, trap_check.d, trap_fuzzer.d) have not been ported yet.

License
-------

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

