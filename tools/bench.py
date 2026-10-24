#!/usr/bin/env python3
"""Measure how fast a machine runs OpFor.

    python3 bench.py path/to/bot_opfor

searches a fixed set of positions, each to a fixed depth, and reports
the machine's speed in nodes per second. It needs only Python 3.8 or
later and a bot_opfor binary: the positions are built in.

The work is the same from run to run. With the default --seq engine
and hash size, a given OpFor version searches exactly the same nodes on
every machine, Linux or Windows, so the total node count works as a
signature: two runs with the same signature did the same work, and their
times compare directly. A different OpFor version, --hash or the
threaded engine searches differently: those give a different signature,
and their speeds are only roughly comparable.

Speed varies a lot from position to position, so compare nodes per
second only between runs on the same position set.

On shared machines, such as most VPSes, the speed can change from
minute to minute with the load from other tenants. --rounds repeats the
set and reports the spread; --jobs runs that many engines at once, to
see how the machine does with all its cores busy (it reports the speed
of each engine and of all of them together).

Each search runs in a fresh engine process, since some state survives
`newgame` and would make a position's node count depend on the ones
before it. The time is taken from sending `go` to receiving `bestmove`,
so process startup and hash allocation aren't counted.
"""

import argparse
import hashlib
import os
import platform
import statistics
import subprocess
import sys
import threading
import time

# Positions from seeded self-play games, as `<id> <depth> <side> <board>`
# with the board as AEI's 64 squares from a8 to h1. The id is the game and
# ply. Each depth is set so the search takes one to ten seconds on a 2025
# laptop (a Ryzen AI 7 350, about 1.5 million nodes per second); the set
# takes about 47 seconds there. Changing a line changes the signature.
POSITIONS = """\
g008p006 8 g [drrr rrd cc  m h   r  r     e    R       RRDE  Ch    DR HRRMHRCR]
g033p007 8 s [rr rhrrcc h d  r d  M r      m          CRD R    EH  D CR  HRRRR]
g025p008 8 g [dmrrrrrr   drh   c  rcE          e         DR   D H RMCRRRRHRCR ]
g019p015 8 s [rr rr rd hhc rc M    mEHerCr   d         R        RHRRR CR  DR R]
g001p018 8 g [r  r rdrhrc  m  dM cr       Ee  R  r Rh     R  R RC  D  H RCRH  ]
g031p023 8 s [r r r dcrrh  dc r  m    R  rr   MEeh     D RR H  DR  CR C  RR H ]
g012p035 7 s [r rrh c  m   r c    E        e r   rrD   R RC M   R  R  RHRD CRR]
g010p049 8 s [rr   r    c  m   rrdE hcR     r         dH CeHR DC   DR    RR  R]
g020p050 8 g [  r r r  rcr   rdDRHd r              e        ED    RHh    RR   ]
g024p051 7 s [dr    r r r  r hH     r m E c  reC  c   D   Mrh   CDdRRR R   RH ]
g029p057 8 s [ r    r rdMh e        Rr    cER Cr      R  H   h  DcRR R C    R ]
g023p059 7 s [ r rdrr    rHrDr    C rc   R E R         R  R   R C eMd R D hh  ]
g037p068 7 g [rrr r   c    r d   h  cR   R            Cd r   M R   e    CmH R ]
g017p075 7 s [crh    mr        r   RE R r D    rd  e r    C H RDR       C    R]
g006p077 8 s [  dc    r RE d   h e  m   RR   r   rHD     C   r     MRDC  R  R ]
g009p079 8 s [     r rr    Rr He    D c   E c RHd    R       CR h        RR  C]
g007p084 7 g [c     r      r     h     Rc R      R    R r   Hr rrerHRdCdERR  R]
g005p088 7 g [ cdh  r r  c    R     EM     eRrr r r C HR  C   rh R R         R]
g030p091 8 s [        cD  r HcRe  M r rC  r R r  r E R R C  R R    D      R  R]
g002p093 8 s [ h   Dr  M d e rRdcE R RR r rC   R      r  H    C hrR     HR    ]
g015p104 7 g [ rr     r          r  h    RrcE mC       r e   C Rr R  R  D     ]
g035p118 7 g [     rd  h   rrrrrhrd M rERm    Re RR   c     DCH H  D  RcRR RC ]
""".splitlines()

SIDES = "gs"


class EngineError(Exception):
    pass


class Engine:
    """Minimal AEI client over stdio."""

    def __init__(self, cmd, options):
        try:
            self.proc = subprocess.Popen(
                cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, text=True, bufsize=1)
        except OSError as exc:
            raise EngineError(f"can't start {cmd[0]}: {exc}") from None
        self.send("aei")
        self.wait_for("aeiok")
        for name, value in options:
            self.send(f"setoption name {name} value {value}")
        self.send("isready")
        self.wait_for("readyok")

    def send(self, line):
        self.proc.stdin.write(line + "\n")
        self.proc.stdin.flush()

    def wait_for(self, token):
        seen = []
        while True:
            line = self.proc.stdout.readline()
            if not line:
                raise EngineError(f"engine exited (status {self.proc.wait()})")
            line = line.rstrip("\n")
            seen.append(line)
            if line.split()[:1] == [token]:
                return seen
            if line.startswith("log Error"):
                raise EngineError(line[4:])

    def search(self, depth, side, board):
        """Search to a fixed depth. Returns (nodes, seconds, bestmove)."""
        self.send("newgame")
        self.send(f"setposition {side} [{board}]")
        self.send(f"setoption name depth value {depth}")
        self.send("isready")
        self.wait_for("readyok")
        start = time.perf_counter()
        self.send("go")
        lines = self.wait_for("bestmove")
        seconds = time.perf_counter() - start
        nodes = None
        for line in lines:
            words = line.split()
            if words[:2] == ["info", "nodes"]:
                nodes = int(words[2])  # the last report has the total
        if nodes is None:
            raise EngineError("the engine reported no node count")
        return nodes, seconds, lines[-1].split(None, 1)[1]

    def close(self):
        try:
            self.send("quit")
            self.proc.wait(timeout=10)
        except (OSError, subprocess.TimeoutExpired):
            self.proc.kill()
            self.proc.wait()


def read_positions(lines):
    positions = []
    for line in lines:
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        pid, depth, side, board = line.split(None, 3)
        board = board.strip("[]")
        if side not in SIDES or len(board) != 64:
            raise ValueError(f"bad position line: {line}")
        positions.append((pid, int(depth), side, board))
    return positions


def cpu_name():
    """A best-effort CPU model name."""
    try:
        if sys.platform.startswith("linux"):
            with open("/proc/cpuinfo") as f:
                for line in f:
                    if line.startswith(("model name", "Model", "Hardware")):
                        return line.split(":", 1)[1].strip()
        elif sys.platform == "darwin":
            return subprocess.run(
                ["sysctl", "-n", "machdep.cpu.brand_string"],
                capture_output=True, text=True).stdout.strip()
        elif sys.platform == "win32":
            import winreg
            with winreg.OpenKey(
                    winreg.HKEY_LOCAL_MACHINE,
                    r"HARDWARE\DESCRIPTION\System\CentralProcessor\0") as key:
                return winreg.QueryValueEx(key, "ProcessorNameString")[0].strip()
    except OSError:
        pass
    return platform.processor() or platform.machine()


def run_set(args, positions, job, results, report):
    """Search every position once; fills results[job]."""
    out = []
    try:
        for pid, depth, side, board in positions:
            engine = Engine([args.engine] + args.engine_args, args.options)
            try:
                nodes, seconds, _ = engine.search(depth, side, board)
            finally:
                engine.close()
            out.append((pid, depth, nodes, seconds))
            report(job, pid, depth, nodes, seconds)
        results[job] = out
    except EngineError as exc:
        results[job] = exc


def run_round(args, positions):
    """One pass over the set by each of args.jobs engines at once."""
    lock = threading.Lock()

    def report(job, pid, depth, nodes, seconds):
        if args.verbose:
            with lock:
                tag = f"[{job + 1}] " if args.jobs > 1 else ""
                print(f"  {tag}{pid}  depth {depth:2}  {nodes:>11,} nodes"
                      f"  {seconds:7.2f}s  {nodes / seconds:>11,.0f} nps",
                      flush=True)

    results = [None] * args.jobs
    threads = [threading.Thread(target=run_set,
                                args=(args, positions, job, results, report))
               for job in range(args.jobs)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    for r in results:
        if isinstance(r, Exception):
            raise r
    return results


def main():
    p = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("engine", help="path to a bot_opfor binary")
    p.add_argument("-r", "--rounds", type=int, default=1,
                   help="times to search the whole set (default 1)")
    p.add_argument("-j", "--jobs", type=int, default=1,
                   help="engines to run at once (default 1)")
    p.add_argument("--hash", type=int,
                   help="transposition table size in MB (changes the "
                   "signature; default: the engine's own)")
    p.add_argument("--engine-arg", dest="engine_args", action="append",
                   help="engine argument, replacing the default --seq "
                   "(repeatable; write as --engine-arg=--threads)")
    p.add_argument("-p", "--positions",
                   help="a file of `<id> <depth> <g|s> <board>` lines to "
                   "use instead of the built-in set")
    p.add_argument("-n", "--count", type=int,
                   help="use only the first N positions (a quick check; "
                   "changes the signature)")
    p.add_argument("-q", "--quiet", dest="verbose", action="store_false",
                   help="don't print each search")
    args = p.parse_args()
    if args.engine_args is None:
        args.engine_args = ["--seq"]
    if os.sep not in args.engine and not (os.altsep and os.altsep in args.engine):
        # A bare name would be looked up on PATH rather than here.
        args.engine = os.path.join(".", args.engine)
    args.options = [("hash", args.hash)] if args.hash else []

    if args.positions:
        with open(args.positions) as f:
            positions = read_positions(f)
    else:
        positions = read_positions(POSITIONS)
    if args.count:
        positions = positions[:args.count]

    print(f"cpu: {cpu_name()} ({os.cpu_count()} logical cores)")
    print(f"os: {platform.system()} {platform.release()} {platform.machine()}")
    try:
        with open(args.engine, "rb") as f:
            digest = hashlib.sha256(f.read()).hexdigest()[:16]
    except OSError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    print(f"engine: {' '.join([args.engine] + args.engine_args)}"
          f" (sha256 {digest}...)"
          + (f", hash {args.hash} MB" if args.hash else ""))
    print(f"positions: {len(positions)}"
          + (f" from {args.positions}" if args.positions else " (built in)")
          + (f", {args.jobs} engines at once" if args.jobs > 1 else ""))

    rounds = []  # per round: (nodes per engine, seconds per engine)
    signature = None
    try:
        for r in range(args.rounds):
            if args.rounds > 1:
                print(f"round {r + 1}/{args.rounds}", flush=True)
            results = run_round(args, positions)
            totals = [(sum(x[2] for x in res), sum(x[3] for x in res))
                      for res in results]
            for nodes, _ in totals:
                if signature is None:
                    signature = nodes
                elif nodes != signature:
                    print(f"warning: node total {nodes:,} differs from "
                          f"{signature:,}; the searches aren't deterministic "
                          "(threaded engine?)", file=sys.stderr)
            rounds.append(totals)
            nps = [n / s for n, s in totals]
            print(f"  round {r + 1}: {sum(s for _, s in totals) / len(totals):.1f}s"
                  f", {statistics.mean(nps):,.0f} nps per engine"
                  + (f", {sum(nps):,.0f} nps together" if args.jobs > 1 else ""),
                  flush=True)
    except EngineError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("interrupted", file=sys.stderr)
        if not rounds:
            return 1

    print(f"signature: {signature:,} nodes per pass")
    per_engine = [n / s for totals in rounds for n, s in totals]
    together = [sum(n / s for n, s in totals) for totals in rounds]
    if len(per_engine) > 1:
        print(f"nps per engine: median {statistics.median(per_engine):,.0f}"
              f" (min {min(per_engine):,.0f}, max {max(per_engine):,.0f})")
    print(f"nps: {statistics.median(per_engine):,.0f}"
          + (f" per engine, {statistics.median(together):,.0f} with "
             f"{args.jobs} engines together" if args.jobs > 1 else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
