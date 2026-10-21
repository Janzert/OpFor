# Changelog

Notable changes to OpFor. Releases since 2026 are tagged with their date
(`v2026.10.6`). Before that, each year's Arimaa Computer Championship
version is tagged `ArimaaCC_<year>`. Entries up to 2012 are a summary
drawn from the commit history.

## Unreleased

- **Added:** about 250 of the evaluation's and search's constants can
  be set by AEI `setoption`, as `tune_<name>` or `tune_<name>_<i>` for a
  table entry (`source/tunables.d` lists them), for automatic tuning.
  Tables kept for both colours are set as gold's half and mirrored, so a
  tuned set stays symmetric. Most tables can also be reshaped as a whole
  by two to four `tune_<table>_shape_<k>` values (56 in all): an added
  curve by rank for the rabbit tables, a factor that changes how fast
  the decaying tables fall off. With nothing set OpFor plays as before:
  fixed-depth comparison 200 of 200 positions identical at depth 6, and
  the same speed.

- **Changed:** the goal-threat term counts 2.8 times as much (the
  `eval_goal` option, which defaulted to 1). Fitting the evaluation's
  weights to the results of 7.7 million positions from engine and
  arimaa.com games put it at 2.7 to 3 times its old value every way the
  fit was set up, so the threat of a rabbit reaching goal next turn was
  badly undervalued. Test: 765 games of 2.8 (set by the option) against
  the default, at 1s/move and a 100-turn limit: +51.3 Elo [+26.6,
  +76.6] (95%), SPRT [0, 10] passed after 382 pairs (LLR 2.95).

- **Fixed:** the goal search reported goals that don't exist and missed
  some that do. Most of the false ones came from finishing a pull with
  the piece that last stepped: the pulled piece could land on the goal
  square or on the square the rabbit had to cross, a rabbit could be
  sent through an occupied square or step while frozen by another piece,
  a pull onto a trap counted as unfreezing the rabbit while another
  piece still froze it, a pull could take the only square the piece on
  the goal square could step aside to, and a piece of equal strength
  counted as able to pull. With 3 steps left, these made the
  evaluation score a win that wasn't there. At any point in a turn, a
  check of whether a piece would be frozen beside the goal compared the
  wrong square and always passed, and moving an enemy rabbit away
  counted as unfreezing a rabbit. Missed: when the only piece freezing a
  rabbit was the one on the goal square ahead of it, pulling that piece
  aside wasn't seen to free the rabbit, so a goal in 3 came out as 4 or
  as none, and some goals in 4 as none. Checked against a search of
  every step on 470,000 turn starts from games, each in both colours:
  with a pull pending, false wins for the side to move fell from 338 of
  158,276 checks to 6, and at the start of a turn, missed goals for the
  side not to move fell from 44 of 940,038 to 6. At depth 6, 185 of 200
  comparison positions are identical, the rest differing in node counts
  only. Test: 5537 games against the build before, at 1s/move and a
  100-turn limit: +8.4 Elo [−0.6, +17.4] (95%), SPRT [0, 10] undecided
  at its 3000-pair cap (LLR 1.63). 144 of the games repeat earlier ones,
  so the error bars are somewhat too narrow.
- **Fixed:** four search errors. The quiescence search played on at
  the start of a turn when the opponent's rabbit was already on goal,
  so it could "save" a lost game by pulling the rabbit back. A late
  move reduction's full-depth re-search used the reduced search's
  value as its lower bound, which can leave an empty or inverted
  window; it now uses the node's own window, as does a principal
  variation re-search when the null-window search already reached
  beta. The null-move search ignored an abort (it checked the wrong
  variable), and inside it the opponent could play a move that changes
  nothing. Fixed-depth comparison: 192 of 200 positions identical at
  depth 6, the rest differing in node counts only; at depth 8, 21 of
  40 differ in node counts, 8% less time in all. Test: 2465 games
  against the build before, at 1s/move and a 100-turn limit: +18.6 Elo
  [+5.3, +32.0] (95%), SPRT [0, 10] passed (LLR 2.95).

- **Fixed:** the bonus for a strong advanced rabbit was all or nothing.
  Its share of support was an integer division, so it was 0 unless the
  rabbit had full support, and then 1; it now grows with the support as
  intended. The rabbit square table also gave c3 (and silver's f6) 0.13
  where its mirror has 0.14, so the term changed when the board was
  mirrored; it no longer does. Over the game positions of a 6000-game
  test the rabbit term changed in 38.8%, by a median of 21 points (90th
  percentile 137). Test: 4452 games against the build before, at
  1s/move and a 100-turn limit: +5.5 Elo [−4.9, +15.9] (95%), SPRT
  [0, 10] undecided (LLR 0.16), stopped once it had under a 5% chance
  of deciding within 3000 pairs.
- **Fixed:** a rare crash while reporting the principal variation
  during a search (the default multithreaded engine). The report walks
  the hash table while the search thread writes it, and read each
  entry's best step twice, so it could check one step and use another
  and then fail on an impossible move ("Piece disappeared without being
  trapped"). It happened once in 6000 test games. Each entry is now
  read once. Play is unchanged (fixed-depth comparison: 200 of 200
  positions identical).
- **Fixed:** the capture-threat eval's choice of its three victims. A
  victim could be counted twice, its traps could stay with another
  victim after a reorder, and ties between equal victims went to
  whichever capture was found first, so a frozen victim or one with
  several traps could lose its place and the score changed when the
  board was mirrored. The reduction for several victims sharing one
  trap never applied, since the traps used were never recorded; it does
  now. Each victim is now counted once with all its traps, and ties go
  to the victim that scores more. Over the game positions of a
  6000-game test the opponent's threats changed in 10.6% and the side
  to move's in 6.7%, by a median of 30 and 22 points. Test: 6000 games
  against the build before, at 1s/move and a 100-turn limit: +3.9 Elo
  [−4.8, +12.7] (95%), SPRT [0, 10] undecided at 3000 pairs (LLR −0.53).
- **Fixed:** the goal-threat eval counted the goal squares it found as
  one threat or two depending on which side of the board they were on.
  Its two defence sectors (files a to e and d to h) overlap on d and e,
  and the first sector claimed those files, so goal squares b to e made
  one threat but their mirror d to g made two, which halves the defence
  allowance (one position scored +128, its mirror −376). Two threats now
  needs goal squares on both sides of d/e. Over the game positions of a
  6000-game test the term changed in 0.48%, by a median of 215 points.
  Test: 1102 games against the build before, at 1s/move and a 100-turn
  limit: −28.4 Elo [−49.3, −7.8] (95%), SPRT [0, 10] rejected after 551
  pairs (LLR −3.02). Kept as a correct fix, to be balanced by retuning
  the eval weights: the old count's extra threats seem to have made goal
  threats stronger, and that helped.
- **Changed:** the quiescence search now goes 4 steps beyond its first
  step (the `eval_qdepth` option, which had defaulted to 0 since 2008, so
  it could never finish a capture), and only its first step searches
  every step when the opponent threatens a goal; deeper it looks at
  captures and evasions only. Test: 655 games against the build before,
  at 1s/move and a 100-turn limit: +60.1 Elo [+33.4, +87.5] (95%), SPRT
  [0, 10] passed after 325 pairs (LLR 2.98). Without the second part,
  depth 4 lost 59 Elo and depth 8 212, from searching every step at
  every level; with it, depth 8 lost 41.6 Elo [−66.8, −16.9] to depth 4.
- **Fixed:** after a score-cache hit the quiescence search chose between
  captures and every step from the goal search of whatever position was
  evaluated last. The cache now keeps each position's shortest goals.
- **Fixed:** the penalty for pieces standing on traps counted only the
  last occupied trap (in square order, from h1 up) instead of adding up
  every one, so with two or more trap squares occupied it depended on
  which trap came last. Test: 4563 games against the build before, at
  1s/move and a 100-turn limit: −2.9 Elo [−12.9, +7.1] (95%), SPRT
  [0, 10] rejected after 2281 pairs (LLR −3.01). Kept as a correct fix
  with no measurable effect; the weight was tuned around the old
  behaviour.
- **Fixed:** the goal search for the side not to move could finish a
  pull with the piece the side to move had just stepped, which only the
  side to move can do. Mid-turn, this gave gold (and silver, mid-push)
  phantom goal threats
  (silver's step c8-b8 beside a gold rabbit on d7 made a goal "in 2"),
  which fed the goal-threat eval, the PV goal extension and the
  quiescence search's choice of steps. That side's goal search now
  ignores the last step. A shift by 64 when there was no last step,
  which made h1 look like the last step's square, is gone too.
  Test: 6000 games against the build before, at 1s/move and a 100-turn
  limit: +2.0 Elo [−6.8, +10.7] (95%), SPRT [0, 10] undecided at 3000
  pairs (LLR −1.52).
- **Fixed:** the blockade term's "even blockader" factor used the gold
  piece of the same rank for both sides, so for gold equal-rank
  blockers never counted as even and were counted as weak ones instead.
  It now uses the enemy piece of the same rank. Test: 8000 games against
  the build before, at 1s/move: +3.8 Elo [−3.8, +11.4] (95%), SPRT
  [0, 10] undecided at 4000 pairs (LLR −0.79).
- **Fixed:** memory no longer grows with every move under a time
  control. Garbage collection has been off during timed games since
  2008, to keep collection pauses out of the search, so a process
  reused for many games (as in engine test runs) grew by about 60 MB a
  game, without limit. It now collects after each search, once the move
  is sent (about 0.01 s). A repeated `tcmove` no longer stacks
  `GC.disable` calls, which a later long `tcmove` couldn't undo.

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
