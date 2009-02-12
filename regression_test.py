
import re
import sys

from subprocess import Popen

if len(sys.argv) < 2:
    print "usage: %s <board file>" & sys.args[0]

test_boards = open(sys.argv[1], "rU")

next_line = test_boards.readline()
while next_line != "":
    while re.match("[0-9]+[wb]", next_line) == None:
        next_line = test_boards.readline()
        if next_line == "":
            sys.exit(0)
    board_name = next_line
    check_file = open("regression_board", "w")
    for i in range(12):
        check_file.write(next_line)
        next_line = test_boards.readline()
    check_file.close()

    print "Checking", board_name
    parseboard = Popen(["parseboard", "regression_board"])
    if parseboard.wait():
        break

