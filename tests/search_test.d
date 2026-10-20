/// Tests of the search.
module search_test;

import alphabeta;
import logging;
import position;

private ABQSearch searcher(Position pos)
{
    Logger log = new Logger();
    ABQSearch s = new ABQSearch(log, new TransTable(log, 1));
    s.nullmove = pos.dup;
    s.nullmove.do_step(NULL_STEP);
    s.check_nodes = ulong.max;
    s.should_abort = () => false;
    return s;
}

@("quiescence ends the game on a goal at the start of a turn")
unittest
{
    // Silver's turn ended with its rabbit on d1. Gold's elephant on d2
    // could pull it back, but the game is already over.
    enum board = "[    e   " ~ "r      r" ~ "        " ~ "        "
        ~ "        " ~ "        " ~ "R  E   R" ~ "   r    ]";
    Position pos = parse_short_str(Side.WHITE, 4, board);
    ABQSearch s = searcher(pos);
    assert(s.quiesce(pos, 0, MIN_SCORE, MAX_SCORE) == -WIN_SCORE);
    assert(s.quiesce(pos, -1, MIN_SCORE, MAX_SCORE) == -WIN_SCORE);
}
