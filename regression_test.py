
import re
import sys
import time

from subprocess import Popen

if len(sys.argv) < 2:
    print "usage: %s <board file>" & sys.args[0]

test_boards = open(sys.argv[1], "rU")

board_num = 0
while True:
    next_line = test_boards.readline()
    while re.match("[0-9]+[wb]", next_line) == None:
        next_line = test_boards.readline()
        if next_line == "":
            break
    if next_line == "":
        break
    board_name = next_line
    while True:
        try:
            check_file = open("regression_board", "w")
            break
        except IOError:
            print "Could not open regression_board"
            time.sleep(1)
    for i in range(12):
        check_file.write(next_line)
        next_line = test_boards.readline()
    check_file.close()

    board_num += 1
    print "Checking #%d, %s" % (board_num, board_name)
    parseboard = Popen(["parseboard", "regression_board"])
    if parseboard.wait():
        print "Error found"
        sys.exit(0)
    print

print "Finished checking %d boards without an error." % board_num
