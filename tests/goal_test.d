/// Goal search cases that it once got wrong, each checked against the
/// shortest goal found by searching every step.
module goal_test;

import goalsearch;
import position;

/// Runs the goal search on board (8 rows of 8, rank 8 first, gold to move)
/// after gold's last step from lastfrom, if any, and returns the shortest
/// goals for gold and silver.
private int[2] goals(string board, Piece last = Piece.EMPTY,
        bitix lastfrom = 64)
{
    Position pos = parse_short_str(Side.WHITE, last == Piece.EMPTY ? 4 : 3,
            "[" ~ board ~ "]");
    pos.set_last_step(last, lastfrom);
    GoalSearchDT gs = new GoalSearchDT();
    gs.set_start(pos);
    gs.find_goals();
    return gs.shortest;
}

@("a pending pull doesn't open a blocked back square")
unittest
{
    // Gold's elephant has stepped b8-a8 and can pull the cat off c8, but the
    // d7 rabbit can't reach c8: c7 holds a dog, d8 a horse.
    enum board =
          "E chr   "
        ~ "  dRr   "
        ~ "   D    "
        ~ "        "
        ~ "        "
        ~ "        "
        ~ "        "
        ~ "        ";
    assert(goals(board, Piece.WELEPHANT, 62) == [5, 5]);
}

@("a pending pull can't clear the back square onto the goal")
unittest
{
    // Gold's camel stepped g8-f8. Pulling the g7 cat into g8 puts it on the
    // goal square the rabbits need.
    enum board =
          "     M r"
        ~ "      cR"
        ~ "      R "
        ~ "        "
        ~ "        "
        ~ "        "
        ~ "        "
        ~ "        ";
    assert(goals(board, Piece.WCAMEL, 57) == [5, 5]);
}

@("a pending pull into the back square blocks it")
unittest
{
    // Gold's elephant stepped from c7 (and was captured on c6). Pulling the
    // b7 cat into c7 blocks the d7 rabbit's way to c8.
    enum board =
          "r  rr  e"
        ~ "Hc RRhd "
        ~ "D   r  r"
        ~ "RR  h RC"
        ~ " rR   R "
        ~ "      r "
        ~ "  R     "
        ~ "    C   ";
    assert(goals(board, Piece.WELEPHANT, 53) == [4, 2]);
}

@("a pending pull can't take the only side square")
unittest
{
    // Gold's camel stepped g8-h8, onto the goal square above the h7 rabbit.
    // Pulling the g7 cat into g8 takes the only square it could step aside
    // to.
    enum board =
          "rCrrrr M"
        ~ "H D R cR"
        ~ "R     R "
        ~ "m  E Rh "
        ~ "  dDC   "
        ~ "   c  eR"
        ~ " h d   R"
        ~ " R     H";
    assert(goals(board, Piece.WCAMEL, 57) == [4, 5]);
}

@("an equal piece can't finish a pull")
unittest
{
    // Gold's dog stepped a7-a6; it can't pull the silver dog on b7 that
    // freezes the c7 rabbit.
    enum board =
          "       r"
        ~ " dR     "
        ~ "Dr      "
        ~ "        "
        ~ "        "
        ~ "        "
        ~ "        "
        ~ "        ";
    assert(goals(board, Piece.WDOG, 55) == [4, 5]);
}

@("the goal square piece can't unfreeze from a side square where it freezes")
unittest
{
    // Gold's cat on d8 would be frozen on e8 by the camel on f8, so it can't
    // come down to e7 to unfreeze the d7 rabbit.
    enum board =
          "  hC m r"
        ~ "  dR d  "
        ~ "   r    "
        ~ "        "
        ~ "        "
        ~ "        "
        ~ "        "
        ~ "        ";
    assert(goals(board) == [5, 5]);
}

@("moving an enemy rabbit doesn't unfreeze a rabbit")
unittest
{
    // The e7 rabbit is frozen by the elephant on d7; pushing the e6 rabbit
    // away doesn't help. From a game.
    enum board =
          "r M D d "
        ~ "DcheRrRr"
        ~ " R ErRHR"
        ~ " rC R   "
        ~ "  R     "
        ~ "        "
        ~ "        "
        ~ "        ";
    assert(goals(board) == [5, 5]);
}

@("pulling the goal square piece aside unfreezes the rabbit behind it")
unittest
{
    // The dog on e8 is all that freezes the e7 rabbit: Hd8w de8w Re7n.
    enum board =
          "hr Hd  r"
        ~ "R ErR   "
        ~ "        "
        ~ " r Rc r "
        ~ " R      "
        ~ "C      H"
        ~ "  r    r"
        ~ "       R";
    assert(goals(board) == [3, 1]);
}

@("the waiting side's corner goal by pulling the goal square piece")
unittest
{
    // Silver's elephant on g1 pulls the gold cat off h1 and the h2 rabbit,
    // frozen only by that cat, goals. From a game, silver waiting.
    enum board =
          "rrr  crr"
        ~ " dhcdDRr"
        ~ "r  hE H "
        ~ "  m H  R"
        ~ " M C    "
        ~ "    R  R"
        ~ "R  D  Rr"
        ~ "RR    eC";
    assert(goals(board) == [5, 3]);
}

@("a pending pull doesn't unfreeze a rabbit frozen by another piece")
unittest
{
    // Gold's cat stepped e7-f7 and can pull the d7 rabbit away, but the c7
    // rabbit that would step through d7 is frozen by the c6 cat.
    enum board =
          "r       "
        ~ "  Rr C  "
        ~ "  cr    "
        ~ "        "
        ~ "        "
        ~ "        "
        ~ "        "
        ~ "        ";
    assert(goals(board, Piece.WCAT, 51) == [4, 5]);
}

@("a pull onto a trap doesn't remove the other freezers")
unittest
{
    // Gold's horse stepped c6-b6. Pulling the c7 rabbit onto c6 captures
    // it, but the b7 rabbit would still be frozen on c7 by the d7 dog.
    enum board =
          " c     r"
        ~ "dRrd    "
        ~ " H      "
        ~ "        "
        ~ "        "
        ~ "        "
        ~ "        "
        ~ "        ";
    assert(goals(board, Piece.WHORSE, 45)[0] > 3);
}

@("a goal in 4 by pulling the goal square piece aside")
unittest
{
    // The dog on g8 steps to f8 and pulls the h8 cat to g8; the h6 rabbit
    // walks up to h8. The cat is the only piece next to h7 that could
    // freeze it.
    enum board =
          "      Dc"
        ~ " Re   r "
        ~ "  rH   R"
        ~ "c rh  ME"
        ~ "      H "
        ~ "r       "
        ~ "  h  dm "
        ~ "        ";
    assert(goals(board) == [4, 2]);
}
