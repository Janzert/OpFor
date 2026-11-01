/// Tests of the setup book.
module setup_test;

import std.exception : assertThrown;

import position;
import setupboard;

private enum book_text = "# a comment\n"
    ~ "g 1 RHCMECHR/RRRDDRRR\n"
    ~ "s 2.5 DHCEMCHD/RRRRRRRR  # and another\n";

private Position empty_board(Side side)
{
    return parse_short_str(side, 1, "[" ~ repeat64(' ') ~ "]");
}

private string repeat64(char c)
{
    char[] s;
    s.length = 64;
    s[] = c;
    return s.idup;
}

@("a book setup lands on the squares written, or their mirror")
unittest
{
    SetupBook book = new SetupBook(book_text);
    bool[string] seen;
    for (int i = 0; i < 200; i++)
    {
        Position pos = empty_board(Side.WHITE);
        book.place(Side.WHITE, pos);
        seen[pos.to_placing_move(Side.WHITE)] = true;
        assert(pos.bitBoards[Piece.WELEPHANT] == 1UL << 11
                || pos.bitBoards[Piece.WELEPHANT] == 1UL << 12);
        Position.free(pos);
    }
    assert(seen.length == 2);

    for (int i = 0; i < 200; i++)
    {
        Position pos = empty_board(Side.BLACK);
        book.place(Side.BLACK, pos);
        // Silver's elephant is written on d7 or mirrored to e7, and its
        // rabbits fill the eighth rank.
        assert(pos.bitBoards[Piece.BELEPHANT] == 1UL << 52
                || pos.bitBoards[Piece.BELEPHANT] == 1UL << 51);
        assert(pos.bitBoards[Piece.BRABBIT] == 0xFFUL << 56);
        Position.free(pos);
    }
}

@("a book must have setups for both sides")
unittest
{
    assertThrown(new SetupBook("g 1 RHCMECHR/RRRDDRRR\n"));
}

@("a book refuses lines that aren't a full setup")
unittest
{
    enum silver = "s 1 RHCMECHR/RRRDDRRR\n";
    assertThrown(new SetupBook(silver ~ "g 1 RHCMECHR/RRRDDRR\n"));
    assertThrown(new SetupBook(silver ~ "g 1 RHCMECHR/RRRDDRRM\n"));
    assertThrown(new SetupBook(silver ~ "g 0 RHCMECHR/RRRDDRRR\n"));
    assertThrown(new SetupBook(silver ~ "x 1 RHCMECHR/RRRDDRRR\n"));
    assertThrown(new SetupBook(silver ~ "g RHCMECHR/RRRDDRRR\n"));
}
