#!/usr/bin/env python3
"""Run the mobility and parseboard checks on every board in a file.

A board starts with a line like "12w" (a number and the side to move) and
is 12 lines long, in the format parseboard reads. Build the tools first
with "dub build -c mobility -b checked" and "dub build -c parseboard -b
checked".
"""

import os
import re
import subprocess
import sys
import tempfile

TOOL_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                        "build")
EXE = ".exe" if os.name == "nt" else ""


def boards(path):
    with open(path) as f:
        lines = f.readlines()
    i = 0
    while i < len(lines):
        if re.match(r"[0-9]+[wbgs]", lines[i]):
            yield lines[i].strip(), "".join(lines[i:i + 12])
            i += 12
        else:
            i += 1


def main():
    if len(sys.argv) < 2:
        print(f"usage: {os.path.basename(sys.argv[0])} <board file>")
        return 2
    count = 0
    with tempfile.TemporaryDirectory() as tmp:
        board_file = os.path.join(tmp, "regression_board")
        for name, board in boards(sys.argv[1]):
            with open(board_file, "w") as f:
                f.write(board)
            count += 1
            for tool in ("mobility", "parseboard"):
                print(f"Checking {tool} on #{count}, {name}")
                status = subprocess.call(
                    [os.path.join(TOOL_DIR, tool + EXE), board_file])
                print()
                if status:
                    print(f"{tool} found an error")
                    return 1
    print(f"Finished checking {count} boards without an error.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
