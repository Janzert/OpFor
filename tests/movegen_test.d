/// Move generation and board strings, checked against pyrimaa, the
/// reference implementation of the rules in github.com/Janzert/AEI.
module movegen_test;

import tango_compat;

import position;

private struct MoveCount
{
    Side side;
    string board;
    size_t moves;  /// distinct positions after a whole move
}

// Positions from the opfor_compare set of self-play positions, each with the
// number of moves pyrimaa's Position.get_moves finds.
private immutable MoveCount[] MOVE_COUNTS = [
    MoveCount(Side.BLACK, "[rhrrd  cMrhrrd r        r ecEm   R     H   R    C R  CDHRR RRR  ]", 10361),
    MoveCount(Side.BLACK, "[ r r rdr Mc cm  re  r   h E     R Hd RhD C  R R R   H     RC R  ]", 12715),
    MoveCount(Side.WHITE, "[ h   Dr  Mcd e r  RE R RRdr rC   R      r  H    C hrR     HR    ]", 15178),
    MoveCount(Side.BLACK, "[rr cc  rrrd dhmr   r hr         DR    D  E R  H  eR H  R MCRRRRC]", 22323),
    MoveCount(Side.WHITE, "[ cdh  r r  c    R     EM     eRrr r r C HR  C   rh R R         R]", 12420),
    MoveCount(Side.BLACK, "[c  h   r  rrrrd  c  r e r C  d       Eh  R Hr   R  R RH D R R RR]", 20743),
    MoveCount(Side.BLACK, "[ rr   Hddc    r Rc       R  rEm h r    C R eh R M R DD   H   RCR]", 8283),
    MoveCount(Side.WHITE, "[     r rr   eRr H     D c   E c RHd    R       CR h        RR  C]", 16727),
    MoveCount(Side.BLACK, "[rrr  rcc hm  d   h rr    r  R  r    eEd  C       HMRCHRRDR  DR R]", 25103),
    MoveCount(Side.BLACK, "[      cc rE r   rR  h          r   r e   H RCrD   R  RM   R DCRR]", 5287),
    MoveCount(Side.BLACK, "[ rdcrcr hrrd h e  mMr r HrE              R    R H   RC RCD RRRRD]", 7685),
    MoveCount(Side.WHITE, "[ rr     rmr        rrch    RE    R      rC e   C    D DRR   RR  ]", 16227),
    MoveCount(Side.WHITE, "[    hdr r Mr   rR  H       r H           r     h Ee  RDR m  R R ]", 12976),
    MoveCount(Side.BLACK, "[ rcrrhr r e  r  rR        MR        C Eh     Dm   R  C RRR  R  H]", 3629),
    MoveCount(Side.BLACK, "[     r      r R              E        c        R     e          ]", 1578),
    MoveCount(Side.WHITE, "[r r h rrrch  r dcHRe      mE      RD r  H  Rr d     MCRRR  DR CR]", 10899),
    MoveCount(Side.WHITE, "[ r c  rr  r rr   d  h r  R dM R   e        DD H rCE   C R mRR   ]", 22743),
    MoveCount(Side.WHITE, "[ r rdrr    rHrDr R RC rc     E R           R    R C eMd R  D h  ]", 14417),
    MoveCount(Side.BLACK, "[    rrrr drr rh  m       REdr c cDDe  M  H  R C    H C RRRR R R ]", 14282),
    MoveCount(Side.WHITE, "[ r r   rrHr         h c    rdH      Eh  re    r  D c RC    R  R ]", 3672),
    MoveCount(Side.BLACK, "[d  r   r  r   c  c    d     r     mE hrD MDeCrR   HRRHh R RR  CR]", 23608),
    MoveCount(Side.BLACK, "[ r    r rdMh e        Rr    cER Cr      R  H   h  DcRR R C    R ]", 3456),
    MoveCount(Side.WHITE, "[ D      c   r HcR   M r rC  r R r  r E R R C  R R    D      R  R]", 101363),
    MoveCount(Side.BLACK, "[dm c r h  Erc r    rr H  rdHeR      R    C h      RRCR  RDD  M R]", 15170),
    MoveCount(Side.WHITE, "[   c    rM E        D     R r                  rRCHH D C    RRRR]", 40351),
    MoveCount(Side.BLACK, "[     rd  h   rrrrrhrd M rERm    Re RR   c     DCHcH  D   RRR RC ]", 6004),
    MoveCount(Side.BLACK, "[ r dMr  r c  Rh    rE   r dm e     R C  rD HR C  D      R RR    ]", 14065),
    MoveCount(Side.BLACK, "[rrr r   c    r d   h  cR   R   M        Cd r     R  He    Cm R  ]", 42919),
    MoveCount(Side.WHITE, "[cr    rr  r    d   Dh ER Rd Re      hHc    R      R  R          ]", 998),
];

@("unique moves match pyrimaa")
unittest
{
    foreach (c; MOVE_COUNTS)
    {
        Position pos = parse_short_str(c.side, 4, c.board);
        PosStore moves = pos.get_moves();
        assert(moves.length == c.moves, Format("{} moves, expected {}, for\n{}",
                moves.length, c.moves, pos.to_long_str()));
        moves.free_items();
        Position.free(pos);
    }
}

@("board strings round trip")
unittest
{
    foreach (c; MOVE_COUNTS)
    {
        Position pos = parse_short_str(c.side, 4, c.board);
        assert(pos.to_short_str() == c.board, pos.to_short_str());
        Position again = parse_long_str("1" ~ "wb"[c.side] ~ "\n"
                ~ pos.to_long_str());
        assert(again == pos, pos.to_long_str());
        assert(again.zobrist == pos.zobrist);
        Position.free(again);
        Position.free(pos);
    }
}
