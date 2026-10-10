# Changelog

Notable changes to OpFor. Releases since 2026 are tagged with their date
(`v2026.10.6`). Before that, each year's Arimaa Computer Championship
version is tagged `ArimaaCC_<year>`. Entries up to 2012 are a summary
drawn from the commit history.

## 2026.10.10 (2026-10-10)

- **Changed:** a `depth` only caps the search, as in Sharp. With a time
  control the search now ends at the depth or the clock, whichever
  comes first, and a fixed-depth search is one with no time control.
  Before, setting a depth turned the time control off (a deliberate
  choice since 2009).
- **Fixed:** `depth` 0 or less means no fixed depth, as AEI specifies.
  Only `infinite` did, and 0 searched to depth 4.
- **Fixed:** the bot quits when its input closes. A controller that died
  or exited without sending `quit` used to leave it running.
- The engine manifest (`engine.json`) is kept in the repository. The
  release workflow adds each release's version and downloads. It now
  lists the `depth` option.

## 2026.10.6 (2026-10-06)

The first release since 2011, ported to current D. Each release
publishes builds for Linux, Windows and macOS with an engine manifest
(`engine.json`, AEI's `ENGINE_MANIFEST.md`) that controllers can install
from.

- **Changed:** ported from D1 and Tango to D2, built with LDC (64-bit)
  and dub. At first the port's search results were identical to the
  last D1 build (`d1-final`); the fixes below then changed them.
- **Changed:** `stop`, `makemove` and `newgame` are handled within about
  a tenth of a second (0.2-0.3 s for the threaded engine's `stop`)
  rather than up to a second, since the search now runs in 0.1 s slices.
- **Fixed:** goal threat sectors for gold are shifted as 64-bit values.
  The D1 build's int shift by 40 gave gold a sector covering almost the
  whole board, so play changes in positions with goal threats.
- **Fixed:** the transposition table is sized by its real entry size, so
  `hash` sets the memory used.
- **Fixed:** evaluation constants are correctly rounded (DMD 1 misread
  16 decimal literals in their last bit).
- **Fixed:** a position with no legal moves gets a warning and an empty
  `bestmove` instead of a crash.
- **Fixed:** unrecognized options are reported (the check was inverted),
  socket input split mid-line is reassembled, and moves may have extra
  whitespace.
- **Fixed:** the threaded engine checks that PV steps are legal (only the
  reported PV was affected).
- **Fixed:** builds on Windows.
- Unit tests (unit-threaded) and a self-play test checked by pyrimaa,
  run by CI on Linux, Windows and macOS. The test tools (parseboard,
  the goal, trap and mobility fuzzers, eval_eval, handicaptest) build
  with dub.

## D1 final (`d1-final`, 2012-04-15)

The last D1/Tango commit, with no engine changes since the 2011
Championship version. It builds only as a 32-bit program
(`tools/build-opfor-d1.sh` in the development repo).

## 2011 Championship (`ArimaaCC_2011`, 2011-02-21)

- **Changed:** evaluation: more weight on static mobility, reworked
  hostage, blockade and rabbit strength terms, and fixes to the hostage
  evaluation. An opponent's goal is no longer scored as a forced goal.
- **Changed:** search: keeps searching when the current best move loses
  and there is time and another move left; search extensions get at
  least 5 seconds or a quarter of the time left. The goal defence search
  is back in the quiescence search.
- **Fixed:** a fixed-depth search with a time control also given still
  stopped at the time control's limit.
- `parseboard` shows the static evaluation, and `eval_eval` finds
  positions the static evaluation may misjudge.
- The search time is logged to a tenth of a second.

## 2010 Championship (`ArimaaCC_2010`, 2010-02-27)

- **Added:** root parallel search with threads (`--threads`, the default,
  or `--seq` for a single-threaded search). The root score
  is checked during the search, which restarts if it changes.
- **Changed:** ported to the Tango library. The old experimental bots
  were removed.
- **Changed:** AEI protocol version 1. The logged evaluation no longer
  uses its own AEI command.
- **Changed:** evaluation: mobility, blockades, hostages and frames
  unified into one mobility evaluation (with cat mobility and rabbit
  frames), with frame, hostage and on-trap values relative to the FAME
  score. The quiescence search goes full width under a goal threat.
- **Fixed:** two serious bugs in the static mobility evaluation, long
  positions with `g`/`w` for the side to move, time management with an
  uncapped reserve, random moves in forced wins in the threaded engine,
  and several threaded engine crashes.
- A README and the MIT license.

## 2009 Championship (`ArimaaCC_2009`, 2009-02-28)

- **Added:** a decision-tree static goal search, replacing the old one,
  with a fuzzer and a regression test script for it and the capture
  generator.
- **Added:** negascout, goal extensions, early beta pruning, capture
  evasion steps in the quiescence search, and pruning of moves made of
  unrelated steps.
- **Added:** a static evaluation cache, and evaluation of the strongest
  pieces' mobility, threats, threat area and strong blockaders.
- **Added:** AEI over stdio, now the default (the socket connection is
  an option), and a build script with a static build.
- **Changed:** a fixed-depth search doesn't use the time control.
- **Changed:** random setups prefer 99of9's over the standard setup over
  Fritzlein's; four forward rabbits are much rarer.
- **Changed:** losing moves go straight to a losing list, and when every
  move loses a second pass finds the longest loss.
- **Changed:** the tournament rules option was removed (they are used in
  every game), and garbage collection is off in live games.
- **Fixed:** many capture generator and goal search bugs, a memory leak
  of step lists, a node counter that overflowed after about 20 hours
  (now 64-bit), and an overflow in the killer moves past 24 steps deep.

## 2008 Championship (`ArimaaCC_2008`, 2008-03-01)

The first Championship version.

- **Added:** an alpha-beta search with a transposition table (probing four
  entries), history and killer move heuristics, late move reductions,
  root reductions for poor moves, a quiescence search over captures and
  goal threats, and a goal search.
- **Added:** an evaluation of material (FAME), trap control and
  safety, hostages and blockades, frames, mobility, piece and rabbit
  strength, and goal threats.
- **Added:** AEI over a socket: `setoption` (including `depth` and the
  time control), `stop`, pondering, time management, and `log` and
  `info` output. The server address and port can be given on the
  command line.
- **Added:** an in-memory opening book.

After the 2008 Championship: null move pruning, several setups with
random minor piece placement, target search times separate from the
time control (for postal games), and a handicap playout tool.

## Beginnings (2007)

Started in August 2007 as a board and move generator with random, UCB
and UCT bots, then an alpha-beta bot, `bot_ab`, renamed `bot_opfor` in
December 2007.
