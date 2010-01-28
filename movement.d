
import position;

import tango.util.log.Trace;

void piece_mobility(Position pos, ulong pbit, ulong freezers,
        ulong[] reachable, out ulong frozen)
in
{
    assert (popcount(pbit) == 1);
    assert (pbit & ~pos.bitBoards[Piece.EMPTY]);
    assert (pbit & ~(pos.bitBoards[Piece.WRABBIT] |
                pos.bitBoards[Piece.BRABBIT]));
}
body
{
    reachable[0] = pbit;
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

    ulong empties = pos.bitBoards[Piece.EMPTY];
    ulong bad_traps = TRAPS & ~neighbors_of(pos.placement[side] & ~pbit);
    ulong safe_empties = empties & ~bad_traps;
    ulong trapped = neighbors_of(pbit) & pos.placement[side] & bad_traps;
    ulong fr_neighbors = neighbors_of(freezers);
    ulong freeze_sq = fr_neighbors & ~neighbors_of(pos.placement[side] & ~pbit & ~trapped);
    ulong p_neighbors = neighbors_of(pbit);

    reachable[1] = p_neighbors & safe_empties;
    frozen |= reachable[1] & freeze_sq;
    reachable[2] = neighbors_of(reachable[1] & ~frozen) & safe_empties & ~pbit;
    frozen |= reachable[2] & freeze_sq;
    reachable[3] = neighbors_of(reachable[2] & ~frozen) & safe_empties
        & ~(pbit | reachable[1]);
    frozen |= reachable[3] & freeze_sq;
    reachable[4] = neighbors_of(reachable[3] & ~frozen) & safe_empties
        & ~(pbit | reachable[1] | reachable[2]);
    frozen |= reachable[4] & freeze_sq;
    ulong fmove = p_neighbors & pos.placement[side];
    if (popcount(fmove) > 1
            || (pbit & ~fr_neighbors & ~TRAPS))
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
        ulong f_neighbors = neighbors_of(fbit);
        ulong filled = 0;
        ulong se_neighbors = f_neighbors & empties
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
            frozen |= reachable[3] & fr_neighbors
                & ~neighbors_of(pos.placement[side] & ~(pbit | fbit));
            reachable[4] |= neighbors_of(se_neighbors & ~frozen)
                & empties
                & ~(TRAPS & ~neighbors_of(pos.placement[side]
                            & ~pbit & ~fbit));
        } else {
            bitix fix = bitindex(fbit);
            ulong emptied = (f_neighbors & TRAPS & pos.placement[side])
                & ~(neighbors_of(pos.placement[side] & ~fbit));
            if ((f_neighbors & pos.placement[side] & ~pbit & ~emptied)
                    || ((fbit & ~TRAPS)
                        && piece >= pos.strongest[side^1][fix] + enemyoffset))
            {
                filled = f_steps;
            }
        }
        if (f_steps)
        {
            reachable[2] |= fbit;
            reachable[4] |= f_neighbors & (pos.placement[side] | filled)
                & ~((pos.bitBoards[Piece.WRABBIT + pieceoffset]
                            | (is_r ? filled : 0))
                        & ~rabbit_steps(cast(Side)(side^1),
                            safe_empties & ~filled))
                & neighbors_of(safe_empties & ~filled);
            frozen |= reachable[4] & fr_neighbors
                & ~neighbors_of(pos.placement[side] & ~(pbit | fbit));
        }
    }

    fmove = neighbors_of(reachable[1]) & pos.placement[side];
    fmove &= ~(pos.bitBoards[Piece.WRABBIT + pieceoffset]
            & ~rabbit_steps(cast(Side)(side^1), safe_empties))
        & neighbors_of(safe_empties);
    while (fmove)
    {
        ulong fbit = fmove & -fmove;
        fmove ^= fbit;
        ulong f_neighbors = neighbors_of(fbit);
        ulong filled = 0;
        ulong safe_fempties = f_neighbors & empties
            & ~(TRAPS & ~neighbors_of(pos.placement[side] & ~pbit & ~fbit));
        ulong f_steps = safe_fempties;
        if (fbit & pos.bitBoards[Piece.WRABBIT + pieceoffset])
        {
            f_steps &= rabbit_steps(side, fbit);
        }
        if (!f_steps)
            continue;
        ulong first_steps = safe_fempties & p_neighbors;
        while (first_steps)
        {
            ulong first_step = first_steps & -first_steps;
            first_steps ^= first_step;
            if (!(neighbors_of(first_step) & ~fbit & ~pbit
                        & pos.placement[side])
                    && (neighbors_of(first_step) & freezers))
                continue;
            if (!(f_steps & ~first_step))
                continue;
            reachable[3] |= fbit;
            frozen |= fbit & freeze_sq;
            if (popcount(f_steps & ~first_step) > 1)
            {
                reachable[4] |= safe_fempties;
                frozen |= safe_fempties & freeze_sq;
                break;
            }
        }
    }

    ulong weaker = pos.placement[side^1] & ~freezers
        & ~pos.bitBoards[piece - enemyoffset];
    ulong pmove = neighbors_of(pbit) & weaker & neighbors_of(empties)
        & ~bad_traps;
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
            reachable[4] |= neighbors_of(obit) & (weaker | filled)
                & neighbors_of(empties) & ~bad_traps;
                frozen |= reachable[4] & freeze_sq;
        }
    }

    pmove = neighbors_of(reachable[1] & ~frozen) & weaker
        & neighbors_of(empties) & ~bad_traps;
    while (pmove)
    {
        ulong obit = pmove & -pmove;
        pmove ^= obit;

        ulong on_empties = neighbors_of(obit) & empties;
        ulong pfrom = on_empties & reachable[1] & ~frozen;
        if (pfrom & safe_empties)
        {
            auto pop_one = popcount(on_empties);
            if (pop_one <= 1)
                continue;
            reachable[3] |= obit;
            if (pop_one > 2 && !(obit & freeze_sq))
                reachable[4] |= on_empties & safe_empties;
            frozen |= (reachable[3] | reachable[4]) & freeze_sq;
        }
    }

    reachable[1] |= pbit;
    reachable[2] |= reachable[1];
    reachable[3] |= reachable[2];
    reachable[4] |= reachable[3];
}

debug (test_movement)
{
    import tango.io.FilePath;
    import tango.io.Stdout;
    import tango.io.UnicodeFile;
    import tango.math.random.Random;
    import tango.text.Ascii;

    void test_pos(Position pos, out uint true_moves,
            out uint reported_moves, out uint false_blockade,
            out uint true_blockade, out uint no_blockade)
    {
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
        for (int p = Piece.WRABBIT; p <= Piece.BELEPHANT; p++)
            true_movement[p] |= pos.bitBoards[p];

        ulong enemyoffset = 6;
        ulong freezers;
        ulong[Piece.max+1] reported_movement;
        for (int p = Piece.BELEPHANT; p > Piece.WRABBIT; p--)
        {
            if (p == Piece.BRABBIT)
            {
                enemyoffset = -6;
                freezers = 0UL;
                continue;
            }
            ulong pbits = pos.bitBoards[p];
            while (pbits)
            {
                ulong pbit = pbits & -pbits;
                pbits ^= pbit;
                ulong[5] move_sq;
                ulong frozen;
                piece_mobility(pos, pbit, freezers, move_sq, frozen);
                reported_movement[p] |= move_sq[4];
            }
            freezers |= pos.bitBoards[p - enemyoffset];
        }

        true_moves = 0;
        reported_moves = 0;
        for (int p = Piece.WCAT; p <= Piece.max; p++)
        {
            if (p == Piece.BRABBIT)
                continue;
            if (reported_movement[p] & ~true_movement[p])
            {
                Stdout.format("Incorrect moves for {}",
                    ".RCDHMErcdhme"[p]).newline;
                Stdout(bits_to_str(reported_movement[p]
                            & ~true_movement[p])).newline;
                throw new Exception("Moves reported that could not be made.");
            }
            int true_count = popcount(true_movement[p]);
            int reported_count = popcount(reported_movement[p]);
            real found_per = true_count > 0
                ? (cast(real)reported_count / true_count) * 100.0
                : 100.0;
            Stdout.format("For {} found {} of {} ({:.2}) move squares.",
                    ".RCDHMErcdhme"[p],
                    reported_count, true_count, found_per).newline;
            if (reported_count == 0 && true_count != 0)
            {
                Stdout.format("False complete blockade for {}",
                        ".RCDHMErcdhme"[p]).newline;
                throw new Exception("False full blockade found.");
            }
            true_moves += true_count;
            reported_moves += reported_count;
            if (reported_count < 4 && true_count >= 4)
            {
                false_blockade += 1;
            }
            else if (true_count < 4)
            {
                true_blockade += 1;
            } else {
                no_blockade += 1;
            }
        }
        real total_per = (cast(real)reported_moves / true_moves) * 100.0;
        Stdout.format("Overall for pos found {} of {} ({:.2}) move squares.",
                reported_moves, true_moves, total_per).newline;
    }

    ulong random_bit(ulong bits)
    {
        int num = popcount(bits);
        int bix = rand.uniformR!(int)(num);
        ulong b;
        for (int i=0; i <= bix; i++)
        {
            b = bits & -bits;
            bits ^= b;
        }
        return b;
    }
    void random_pos(inout Position pos)
    {
        Piece[] white_pieces;
        white_pieces = [Piece.WELEPHANT, Piece.WCAMEL, Piece.WHORSE,
            Piece.WHORSE, Piece.WDOG, Piece.WDOG, Piece.WCAT, Piece.WCAT].dup;
        Piece[] black_pieces;
        black_pieces = [Piece.BELEPHANT, Piece.BCAMEL, Piece.BHORSE,
            Piece.BHORSE, Piece.BDOG, Piece.BDOG, Piece.BCAT, Piece.BCAT].dup;

        ulong[] restricted_sqr = [0UL, RANK_8, 0, 0, 0, 0, 0,
            RANK_1, 0, 0, 0, 0, 0];
        int[] num_piece = [0, 8, 2, 2, 2, 1, 1, 8, 2, 2, 2, 1, 1];

        ulong empty = ALL_BITS_SET;
        ulong sqb;
        for (Piece pt=Piece.WRABBIT; pt <= Piece.BELEPHANT; pt++)
        {
            int pt_side = pt < Piece.BRABBIT ? Side.WHITE : Side.BLACK;
            auto place_num = rand.uniformR!(int)(num_piece[pt]);
            if ((pt_side == Side.WHITE && pt >= Piece.WHORSE)
                    || (pt_side == Side.BLACK && pt >= Piece.BHORSE))
                place_num = num_piece[pt];
            for (int n=0; n < place_num; n++)
            {
                sqb = random_bit(empty & ~(TRAPS
                            & ~neighbors_of(pos.placement[pt_side]))
                            & ~restricted_sqr[pt]);
                empty ^= sqb;
                pos.place_piece(pt, sqb);
            }
        }
        pos.set_steps_left(4);
    }

    int main(char[][] args)
    {
        if (args.length < 2)
        {
            FilePath exec = new FilePath(args[0]);
            Stdout.format("usage: {} <boardfile> | -r",
                    exec.name).newline;
            return 1;
        }

        if (compare("-r", args[1]))
        {
            char[] boardstr;
            boardstr = UnicodeFile!(char)(args[1], Encoding.Unknown).read();

            Position pos = position.parse_long_str(boardstr);
            Stdout("wb"[pos.side]).newline;
            Stdout(pos.to_long_str(true)).newline;
            Stdout(pos.to_placing_move()).newline;
            Stdout().newline;

            uint pos_moves, pos_reported, fb, tb, nb;
            test_pos(pos, pos_moves, pos_reported, fb, tb, nb);

            return 0;
        }

        // Check randomly generated positions
        ulong total_moves, total_reported, total_false, total_true, total_none;
        Position pos = new Position();
        uint pos_num;
        while (true)
        {
            pos_num++;
            random_pos(pos);
            Stdout(pos_num);
            Stdout("wb"[pos.side]).newline;
            Stdout(pos.to_long_str(true)).newline;
            Stdout(pos.to_placing_move()).newline;
            uint pos_moves, pos_reported, false_blk, true_blk, no_blk;
            test_pos(pos, pos_moves, pos_reported, false_blk, true_blk, no_blk);
            total_moves += pos_moves;
            total_reported += pos_reported;
            total_false += false_blk;
            total_true += true_blk;
            total_none += no_blk;
            Stdout.format("All positions found {} moves of {} total ({:.2}), blockades {} false {} true {} not a blockade.",
                    total_reported, total_moves,
                    (cast(real)total_reported/total_moves) * 100.0,
                    total_false, total_true, total_none).newline;
            Stdout.newline;
            pos.clear();
        }

        return 0;
    }
}
