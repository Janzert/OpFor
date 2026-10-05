#!/usr/bin/env python3
"""Play bot_opfor against itself over AEI, checking every move with pyrimaa.

    selfplay.py [--moves N] [--depth D] [engine]

Starts two engine processes, plays the setup and then up to N moves each
(default 30) at a fixed search depth (default 4 steps), and exits 1 if
either engine sends an illegal move or stops responding. Needs the aei
package (pip install aei), or the AEI submodule on PYTHONPATH.
"""

import argparse
import os
import shlex
import subprocess
import sys
import time

from pyrimaa import aei
from pyrimaa.board import IllegalMove
from pyrimaa.game import Game

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_ENGINE = os.path.join(os.path.dirname(HERE),
                              "bot_opfor.exe" if os.name == "nt" else "bot_opfor")


def start_engine(path, depth):
    # StdioEngine runs its command through the shell.
    if os.name == "nt":
        cmd = subprocess.list2cmdline([path])
    else:
        cmd = shlex.join([path])
    engine = aei.EngineController(aei.get_engine("stdio", cmd))
    engine.setoption("depth", depth)
    return engine


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("engine", nargs="?", default=DEFAULT_ENGINE)
    parser.add_argument("--moves", type=int, default=30)
    parser.add_argument("--depth", type=int, default=4)
    args = parser.parse_args()

    engines = [start_engine(os.path.abspath(args.engine), args.depth)
               for _ in range(2)]
    try:
        game = Game(engines[0], engines[1])
        start = time.time()
        result = None
        try:
            while game.insetup or (not game.position.is_end_state()
                                   and game.movenumber <= args.moves):
                result = game.play_next_move(start)
                if result:
                    break
        except IllegalMove as exc:
            print(f"Illegal move: {exc}")
            print("\n".join(game.moves))
            return 1
        print("\n".join(game.moves))
        print(game.position.board_to_str())
        if result:
            print(f"Game ended early: {result}")
            return 1
        print(f"{len(game.moves)} legal moves in {time.time() - start:.1f}s")
        return 0
    finally:
        for engine in engines:
            engine.quit()
            engine.cleanup()


if __name__ == "__main__":
    sys.exit(main())
