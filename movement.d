
import position;

void movement(Position pos, ulong pbit, ulong[] reachable,
        out ulong frozen)
in
{
    assert (popcount(pbit) == 1);
    assert (pbit & ~pos.bitBoards[Piece.EMPTY]);
    assert (pbit & ~(pos.bitBoards[Piece.WRABBIT] |
                pos.bitBoards[Piece.BRABBIT]));
}
body
{
    if (pbit & pos.frozen)
    {
        frozen = pbit;
        reachable[1] = pbit;
        reachable[2] = pbit;
        reachable[3] = pbit;
        reachable[4] = pbit;
        return;
    }

    Side side = (pos.placement[Side.WHITE] & pbit) ? Side.WHITE : Side.BLACK;
    bitix pix = bitindex(pbit);
    Piece piece = pos.pieces[pix];
    int pieceoffset = 0;
    int enemyoffset = -6;
    int opieceoffset = 6;
    if (side == Side.BLACK)
    {
        pieceoffset = 6;
        enemyoffset = 6;
        opieceoffset = 0;
    }

    ulong weaker;
    for (int w = Piece.WRABBIT + opieceoffset; w < piece - enemyoffset; w++)
    {
        weaker |= pos.bitBoards[w];
    }
    ulong empties = pos.bitBoards[Piece.EMPTY];
    ulong safe_empties = pos.bitBoards[Piece.EMPTY]
        & ~(TRAPS & ~neighbors_of(pos.placement[side] & ~pbit));
    ulong trapped = neighbors_of(pbit) & pos.placement[side]
        & (TRAPS & ~neighbors_of(pos.placement[side] & ~pbit));
    ulong freeze_sq = neighbors_of(pos.placement[side^1] & ~weaker
            & ~pos.bitBoards[piece - enemyoffset])
        & ~neighbors_of(pos.placement[side] & ~pbit & ~trapped);

    reachable[1] = neighbors_of(pbit) & safe_empties;
    frozen |= reachable[1] & freeze_sq;
    reachable[2] = neighbors_of(reachable[1] & ~frozen) & safe_empties & ~pbit;
    frozen |= reachable[2] & freeze_sq;
    reachable[3] = neighbors_of(reachable[2] & ~frozen) & safe_empties
        & ~(pbit | reachable[1]);
    frozen |= reachable[3] & freeze_sq;
    reachable[4] = neighbors_of(reachable[3] & ~frozen) & safe_empties
        & ~(pbit | reachable[1] | reachable[2]);
    frozen |= reachable[4] & freeze_sq;
    ulong fmove = neighbors_of(pbit) & pos.placement[side];
    if (popcount(fmove) > 1
            || (pbit & ~neighbors_of(pos.placement[side^1] & ~weaker
                    & ~pos.bitBoards[piece - enemyoffset])
                & ~TRAPS))
    {
        fmove &= ~(pos.bitBoards[Piece.WRABBIT + pieceoffset]
                & ~rabbit_steps(cast(Side)(side^1), safe_empties))
            & neighbors_of(safe_empties);
    } else {
        fmove = 0;
    }
    while (fmove)
    {
        ulong fbit = fmove & -fmove;
        fmove ^= fbit;
        ulong filled = 0;
        ulong se_neighbors = neighbors_of(fbit) & pos.bitBoards[Piece.EMPTY]
            & ~(TRAPS & ~neighbors_of(pos.placement[side] & ~pbit & ~fbit));
        ulong f_steps = se_neighbors;
        bool is_r = false;
        if (fbit & pos.bitBoards[Piece.WRABBIT + pieceoffset])
        {
            is_r = true;
            f_steps &= rabbit_steps(side, fbit);
        }
        if (popcount(f_steps) > 1)
        {
            reachable[3] |= se_neighbors;
            frozen |= reachable[3] & neighbors_of(pos.placement[side^1] & ~weaker
                    & ~pos.bitBoards[piece - enemyoffset])
                & ~neighbors_of(pos.placement[side] & ~(pbit | fbit));
            reachable[4] |= neighbors_of(se_neighbors & ~frozen)
                & pos.bitBoards[Piece.EMPTY]
                & ~(TRAPS & ~neighbors_of(pos.placement[side]
                            & ~pbit & ~fbit));
        } else {
            bitix fix = bitindex(fbit);
            if ((neighbors_of(fbit) & pos.placement[side] & ~pbit)
                    || ((fbit & ~TRAPS)
                        && piece >= pos.strongest[side^1][fix] + enemyoffset))
            {
                filled = f_steps;
            }
        }
        if (f_steps)
        {
            reachable[2] |= fbit;
            reachable[4] |= neighbors_of(fbit) & (pos.placement[side] | filled)
                & ~((pos.bitBoards[Piece.WRABBIT + pieceoffset]
                            | (is_r ? filled : 0))
                        & ~rabbit_steps(cast(Side)(side^1), safe_empties & ~filled))
                & neighbors_of(safe_empties & ~filled);
            frozen |= reachable[4] & neighbors_of(pos.placement[side^1] & ~weaker
                    & ~pos.bitBoards[piece - enemyoffset])
                & ~neighbors_of(pos.placement[side] & ~(pbit | fbit));
        }
    }
    ulong pmove = neighbors_of(pbit) & weaker & neighbors_of(empties)
        & ~(TRAPS & ~neighbors_of(pos.placement[side] & ~pbit));
    reachable[2] |= pmove;
    frozen |= pmove & freeze_sq;
    while (pmove)
    {
        ulong obit = pmove & -pmove;
        pmove ^= obit;
        ulong filled = 0;
        ulong on_empties = neighbors_of(obit) & empties;
        if (on_empties & (TRAPS & ~neighbors_of(pos.placement[side^1] & ~obit))
                || popcount(on_empties) > 1)
        {
            if (obit & ~frozen)
            {
                ulong onr = neighbors_of(obit) & safe_empties;
                reachable[3] |= onr;
                reachable[4] |= neighbors_of(onr & ~freeze_sq) & safe_empties;
                frozen |= (reachable[3] | reachable[4]) & freeze_sq;
            }
        } else {
            filled = on_empties;
        }
        if (obit & ~frozen)
        {
            reachable[4] |= neighbors_of(obit) & (weaker | filled) & neighbors_of(empties)
                & ~(TRAPS & ~neighbors_of(pos.placement[side] & ~pbit));
                frozen |= reachable[4] & freeze_sq;
        }
    }
    reachable[1] |= pbit;
    reachable[2] |= reachable[1];
    reachable[3] |= reachable[2];
    reachable[4] |= reachable[3];
}

debug (test_movement)
{
    import std.file;
    import std.path;
    import std.stdio;

    char[] bits_to_str(ulong bits)
    {
        char[] boardstr = " +-----------------+\n".dup;
        for (int rownum = 8; rownum > 0; rownum--)
        {
            char[] rowstr = std.string.toString(rownum) ~ "| ";
            int rowix = 8 * (rownum - 1);
            for (int colnum = 0; colnum < 8; colnum++)
            {
                int index = rowix + (7 - colnum);
                ulong squarebit = 1UL << index;
                char[] piecestr;
                if (squarebit & bits)
                {
                    piecestr = "* ";
                } else
                {
                    if (squarebit & TRAPS)
                    {
                        piecestr = "x ";
                    } else
                    {
                        piecestr = ". ";
                    }
                }
                rowstr ~= piecestr;
            }
            rowstr ~= "|\n";
            boardstr ~= rowstr;
        }
        boardstr ~= " +-----------------+\n";
        boardstr ~= "   a b c d e f g h\n";
        return boardstr;
    }


    int main(char[][] args)
    {
        if (args.length < 2)
        {
            writefln("usage: %s boardfile [run_playouts]", getBaseName(args[0]));
            return 1;
        }
        char[] boardstr;
        try
        {
            boardstr = cast(char[])read(args[1]);
        } catch (FileException fx)
        {
            writefln("A file exception occured: " ~ fx.toString());
            return 2;
        }

        Position pos = position.parse_long_str(boardstr);
        writefln("wb"[pos.side]);
        writefln(pos.to_long_str(true));
        writefln(pos.to_placing_move());
        writefln();

        pos.set_side(Side.WHITE);
        ulong[Piece.max+1] true_movement;
        PosStore moves = pos.get_moves();
        foreach (Position result; moves)
        {
            for (int p = Piece.WRABBIT; p <= Piece.WELEPHANT; p++)
            {
                true_movement[p] |= result.bitBoards[p];
            }
        }
        moves.free_items();
        delete moves;
        pos.set_side(Side.BLACK);
        moves = pos.get_moves();
        foreach (Position result; moves)
        {
            for (int p = Piece.BRABBIT; p <= Piece.BELEPHANT; p++)
            {
                true_movement[p] |= result.bitBoards[p];
            }
        }

        ulong[Piece.max+1] reported_movement;
        for (int p = Piece.WCAT; p <= Piece.max; p++)
        {
            if (p == Piece.BRABBIT)
                continue;
            ulong pbits = pos.bitBoards[p];
            while (pbits)
            {
                ulong pbit = pbits & -pbits;
                pbits ^= pbit;
                ulong[5] move_sq;
                ulong frozen;
                movement(pos, pbit, move_sq, frozen);
                reported_movement[p] |= move_sq[4];
            }
        }

        int total_true;
        int total_reported;
        for (int p = Piece.WCAT; p <= Piece.max; p++)
        {
            if (p == Piece.BRABBIT)
                continue;
            if (reported_movement[p] & ~true_movement[p])
            {
                writefln("Reported moves for %s that could not be made.", ".RCDHMErcdhme"[p]);
                writefln("%s", bits_to_str(reported_movement[p] & ~true_movement[p]));
                return 1;
            }
            int true_count = popcount(true_movement[p]);
            int reported_count = popcount(reported_movement[p]);
            real found_per = (cast(real)reported_count / true_count) * 100.0;
            writefln("For %s found %d of %d (%.2f) move squares.", ".RCDHMErcdhme"[p],
                    reported_count, true_count, found_per);
            total_true += true_count;
            total_reported += reported_count;
        }
        real total_per = (cast(real)total_reported / total_true) * 100.0;
        writefln("Overall found %d of %d (%.2f) move squares.", total_reported, total_true,
                total_per);

        return 0;
    }
}
