
import position;


void piece_mobility(Position pos, ulong pbit, ulong freezers,
        ulong[] reachable, out ulong frozen)
in
{
    assert (popcount(pbit) == 1);
    assert (pbit & ~pos.bitBoards[Piece.EMPTY]);
    assert (pbit & ~(pos.bitBoards[Piece.WRABBIT] |
                pos.bitBoards[Piece.BRABBIT]));
}
do
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
