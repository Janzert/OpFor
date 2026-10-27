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

/// Whether the goal search marks the goal square sq (such as "f8") for the
/// board, gold to move, after gold's last step from lastfrom, if any.
private bool marks(string board, string sq, Piece last = Piece.EMPTY,
        bitix lastfrom = 64)
{
    Position pos = parse_short_str(Side.WHITE, last == Piece.EMPTY ? 4 : 3,
            "[" ~ board ~ "]");
    pos.set_last_step(last, lastfrom);
    GoalSearchDT gs = new GoalSearchDT();
    gs.set_start(pos);
    gs.find_goals();
    bitix ix = cast(bitix)((sq[1] - '1') * 8 + 7 - (sq[0] - 'a'));
    return (gs.goal_squares & (1UL << ix)) != 0;
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

@("the rabbit can't leave the only support of the piece guarding the back square")
unittest
{
    // The b6 rabbit would go b7, c7, c8, kept unfrozen on c7 by the c6
    // camel. But the rabbit is the camel's only support, so the camel is
    // captured as it leaves and the d7 cat freezes it on c7. From a game.
    enum board =
          "rr     r"
        ~ "   c    "
        ~ " RMr    "
        ~ "  dR  rH"
        ~ "   R h r"
        ~ "   er mH"
        ~ "  C E   "
        ~ "R  h  R ";
    assert(goals(board) == [5, 4]);
}

@("the waiting side's rabbit can't leave the only support on the trap")
unittest
{
    // Silver's e3 rabbit would go e2, f2, f1, but it is the only support of
    // the horse on f3, and without it the g2 horse freezes it on f2.
    enum board =
          "e   r   "
        ~ " RRMR Rr"
        ~ "RRC d rD"
        ~ "   R rD "
        ~ " Rr   r "
        ~ "r   rh  "
        ~ "c     H "
        ~ "        ";
    assert(!marks(board, "f1"));
}

@("the back square piece can't push onto an unsupported trap")
unittest
{
    // The f7 dog pushes the f6 cat aside and steps onto f6, where it is
    // captured; the g7 rabbit would then be frozen on f7 by the e7 dog.
    enum board =
          "   re rH"
        ~ "rR  dDRR"
        ~ "RrMR c  "
        ~ " RCcRrD "
        ~ "        "
        ~ "       r"
        ~ "     hr "
        ~ "        ";
    assert(!marks(board, "f8"));
}

@("a rabbit can't step backward to unfreeze another")
unittest
{
    // Only the f7 rabbit could unfreeze the g6 rabbit (from f6), and that
    // is a step backward.
    enum board =
          "  C   r "
        ~ "RhrRDRr "
        ~ "rr    R "
        ~ "Rh R Re "
        ~ "     r  "
        ~ "    C   "
        ~ "E r H   "
        ~ "     d c";
    assert(!marks(board, "h8"));
}

@("the waiting side's rabbit can't step backward to unfreeze another")
unittest
{
    // Silver's b3 rabbit, frozen by the b4 cat, could be unfrozen from a3,
    // but only by the a2 rabbit stepping backward. From a game.
    enum board =
          "    drr "
        ~ "r   HhrM"
        ~ "   cm  r"
        ~ "  rc e D"
        ~ " ChD  R "
        ~ " r E H  "
        ~ "rR dRR  "
        ~ "R       ";
    assert(goals(board) == [5, 5]);
}

@("a rabbit can't step backward to unfreeze the unfreezer")
unittest
{
    // Silver's h2 rabbit needs the g3 cat on h3; the cat needs the e3 dog
    // next to it, and the dog needs a piece next to it first. Only the f2
    // rabbit is near, and f3 is behind it. From a game.
    enum board =
          " r      "
        ~ "r M     "
        ~ " eH     "
        ~ "        "
        ~ "R  hE   "
        ~ "    d c "
        ~ "R   RrDr"
        ~ "    RdR ";
    assert(goals(board) == [5, 5]);
}

@("the rabbit needs support on the back square, not where it stands")
unittest
{
    // The c8 cat and c7 horse step aside (the horse onto c6, where it is
    // captured) for the d7 rabbit, but the b7 cat freezes it on c7.
    enum board =
          "  CDe   "
        ~ " cHRRrdR"
        ~ "R  rRr  "
        ~ "rmr cr R"
        ~ "  H  R M"
        ~ "        "
        ~ " E     r"
        ~ "   h    ";
    assert(!marks(board, "c8"));
}

@("a pending pull doesn't drag the goal square piece beside the rabbit")
unittest
{
    // Gold's camel stepped b8-c8. Pulling the a8 dog into b8 puts it beside
    // the b7 rabbit, which then can't move.
    enum board =
          "d MrD  r"
        ~ " R Rr R "
        ~ "  ehR  H"
        ~ "rRmRC RD"
        ~ "     EH "
        ~ " r    r "
        ~ "   cr Rr"
        ~ " d      ";
    assert(!marks(board, "a8", Piece.WCAMEL, 62));
}

@("a pending pull only takes the freezer if it is next to lastfrom")
unittest
{
    // Gold's horse stepped a8-b8. The a7 rabbit beside a8 is no freezer, and
    // the c7 dog that is can't be pulled into a8: no goal in 3.
    enum board =
          " H      "
        ~ "rRd     "
        ~ "r       "
        ~ "        "
        ~ "        "
        ~ "        "
        ~ "        "
        ~ "        ";
    assert(goals(board, Piece.WHORSE, 63)[0] == 4);
}

@("a lone guard on a trap is lost when its only support moves")
unittest
{
    // The b6 rabbit would go b7, c7, c8 past the cat on c8, with the c6
    // horse beside c7. But the rabbit is the horse's only support.
    enum board =
          "  Cd Ch "
        ~ "   cRER "
        ~ "RRH    c"
        ~ "  rD   d"
        ~ "  rrr RD"
        ~ " r  r   "
        ~ "h r     "
        ~ "      RR";
    assert(!marks(board, "c8", Piece.WCAT, 62));
}

@("an unfreezer can't take the goal square piece's only way out")
unittest
{
    // The g8 dog could unfreeze the f7 rabbit from f8, but f8 is the only
    // square the e8 cat could step aside to.
    enum board =
          "rc hC D "
        ~ " e   RrR"
        ~ " R   mr "
        ~ "  R DRMR"
        ~ "    c r "
        ~ " rdrr   "
        ~ "R RH    "
        ~ "        ";
    assert(!marks(board, "e8"));
}

@("a guard lost with its rabbit needs another supporter, not itself")
unittest
{
    // The c6 cat guards c7 but only the b6 rabbit supports it; the cat
    // itself can't be the piece that supports it on c6.
    enum board =
          "Cr D rEh"
        ~ "   dRRh "
        ~ "HRC  R  "
        ~ "RRd   R "
        ~ "     R  "
        ~ "r  r   c"
        ~ " r   r r"
        ~ "    c   ";
    assert(!marks(board, "c8", Piece.WDOG, 59));
}

@("supporting a lost guard doesn't help a rabbit frozen on the way")
unittest
{
    // The e6 dog could support the c6 horse from d6, but the b6 rabbit would
    // be frozen on b7 by the a7 cat and b8 dog.
    enum board =
          "rd rCDMr"
        ~ "c  dRRhr"
        ~ "mRH DR  "
        ~ "RE e RR "
        ~ "  r     "
        ~ " r      "
        ~ "    r   "
        ~ "        ";
    assert(!marks(board, "c8", Piece.WHORSE, 53));
}

@("the guard on a trap falls when the rabbit stepping past leaves")
unittest
{
    // The g7 horse steps aside for the g6 rabbit, which then reaches f7;
    // but the f6 cat guarding f7 is captured when the rabbit leaves g6.
    enum board =
          "hrH r   "
        ~ "RRR e H "
        ~ " DRrrCRr"
        ~ "R dM c d"
        ~ " r     R"
        ~ "    r   "
        ~ "        "
        ~ "        ";
    assert(!marks(board, "f8"));
}

@("an unfreezer can't step onto the goal square")
unittest
{
    // The d8 horse, unfrozen by the rabbit on d7, could only guard c7 from
    // c8, the goal itself.
    enum board =
          "r  He m "
        ~ "rd    RR"
        ~ " R RR Rr"
        ~ "   CRr r"
        ~ "h       "
        ~ "        "
        ~ "c r  Er "
        ~ "       D";
    assert(!marks(board, "c8"));
}

@("a pending pull of a trap's holder can't land on the back square")
unittest
{
    // Gold's cat stepped b7-a7. Pulling the b6 rabbit into b7 captures the
    // c6 dog, but blocks b7 for the c7 rabbit.
    enum board =
          "r r     "
        ~ "C Rr    "
        ~ "rrd     "
        ~ " DE     "
        ~ "        "
        ~ "        "
        ~ "        "
        ~ "        ";
    assert(goals(board, Piece.WCAT, 54)[0] == 4);
}

@("capturing the trap piece doesn't help with another freezer")
unittest
{
    // Pushing the e6 rabbit away captures the elephant on f6, but the e7
    // dog still freezes the f7 rabbit.
    enum board =
          "D H     "
        ~ " c CdRr "
        ~ "r RCreRR"
        ~ "   rRH R"
        ~ "    rR  "
        ~ "rh d  r "
        ~ "    E   "
        ~ "        ";
    assert(!marks(board, "f8", Piece.WHORSE, 62));
}

@("pulling a rabbit off the back square captures the freezer it held")
unittest
{
    // Gold's camel stepped d7-d8 and pulls the c7 rabbit to d7. That leaves
    // the c6 cat unsupported, and the b7 rabbit goals in 3.
    enum board =
          "rr M   r"
        ~ "rRr  cr "
        ~ "C c m   "
        ~ "   R d r"
        ~ "     E  "
        ~ " H De hR"
        ~ "     CD "
        ~ "R R  RRR";
    assert(goals(board, Piece.WCAMEL, 52)[0] == 3);
}

@("pulling a rabbit off the back square in 4 captures the freezer it held")
unittest
{
    // The d7 camel pulls the c7 rabbit; the c6 cat it supported is captured
    // and the b7 rabbit walks in. From a game.
    enum board =
          "rr     r"
        ~ "rRrM cr "
        ~ "C c m   "
        ~ "   R d r"
        ~ "     E  "
        ~ " H De hR"
        ~ "     CD "
        ~ "R R  RRR";
    assert(goals(board)[0] == 4);
}

@("a piece makes room for the puller beside the goal")
unittest
{
    // Silver's elephant steps c1-c2, the camel b1-c1 pulls the a1 horse to
    // b1, and the a2 rabbit, frozen only by the horse, goals. From a game.
    enum board =
          "  r  r  "
        ~ " cr rr  "
        ~ "   d    "
        ~ "        "
        ~ "   Rr c "
        ~ " h  C D "
        ~ "rR  h R "
        ~ "HmeE   R";
    assert(goals(board)[1] == 4);
}

@("the room-making pull for the side to move")
unittest
{
    // The same pattern for gold on h8, gold waiting in a game.
    enum board =
          "r   eEMh"
        ~ " r H  rR"
        ~ " d c  H "
        ~ " C Rr   "
        ~ "        "
        ~ "    D   "
        ~ "  RR RC "
        ~ "  R  R  ";
    assert(goals(board)[0] == 4);
}

@("pushing an enemy off a square beside the rabbit to guard it")
unittest
{
    // Silver's c3 dog pushes the b3 rabbit to b4 and takes b3, beside the b2
    // rabbit; the b1 horse steps aside and the rabbit goals. From a game.
    enum board =
          "      rr"
        ~ " Hr m  r"
        ~ " r    dR"
        ~ " C R    "
        ~ "c r  R D"
        ~ "hRd     "
        ~ "DrEeR   "
        ~ " hRH   R";
    assert(goals(board)[1] == 4);
}

@("a rabbit can support the guard on a trap first")
unittest
{
    // The b6 rabbit is the only support of the c6 horse, which guards c7.
    // The e6 rabbit steps to d6 to support it, then the b6 rabbit goals
    // through b7 and c7.
    enum board =
          "hr     C"
        ~ "   cr cR"
        ~ "HRH R h "
        ~ "Rr rDrR "
        ~ " r r R  "
        ~ "        "
        ~ "     dM "
        ~ " D    R ";
    assert(goals(board)[0] == 4);
}
