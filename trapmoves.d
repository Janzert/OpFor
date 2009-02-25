
import std.stdio;

import position;

struct CaptureInfo
{
    Piece victim;
    ulong victim_bit;
    int length;
    ulong trap_bit;
    Step first_step;
}

class TrapGenerator
{
    static const int MAX_CAPTURES = 80;

    int num_captures;
    CaptureInfo[MAX_CAPTURES] captures;

    private Position pos;
    private Side side;

    void clear()
    {
        if (pos !is null)
        {
            pos = null;
        }
        num_captures = 0;
    }

    void add_capture(Piece piece, ulong vbit, int steps, ulong tbit, ulong frombit, ulong tobit, bool ispush=false)
    in
    {
        assert (tbit & TRAPS, "trap_bit not a trap");
        assert (popcount(tbit) == 1, "more than one trap in trap_bit");
    }
    body
    {
        debug (static_captures)
        {
            writefln("cap %s at %s in %d steps %s trap step from %s to %s is push %d",
                    ".RCDHMErcdhme"[piece], ix_to_alg(bitindex(vbit)), steps, ix_to_alg(bitindex(tbit)),
                    ix_to_alg(bitindex(frombit)), ix_to_alg(bitindex(tobit)), ispush);
        }
        captures[num_captures].victim = piece;
        captures[num_captures].victim_bit = vbit;
        captures[num_captures].length = steps;
        captures[num_captures].trap_bit = tbit;
        captures[num_captures].first_step.set(frombit, tobit, ispush);
        num_captures++;
    }

    void add_capture(Piece piece, ulong vbit, int steps, ulong tbit, Step* step)
    in
    {
        assert (tbit & TRAPS, "trap_bit not a trap");
        assert (popcount(tbit) == 1, "more than one trap in trap_bit");
    }
    body
    {
        debug (static_captures)
        {
            writefln("cap %s at %s in %d steps %s trap using step %s to %s is push %d",
                    ".RCDHMErcdhme"[piece], ix_to_alg(bitindex(vbit)), steps, ix_to_alg(bitindex(tbit)),
                    ix_to_alg(bitindex(step.frombit)), ix_to_alg(bitindex(step.tobit)), step.push);
        }
        captures[num_captures].victim = piece;
        captures[num_captures].victim_bit = vbit;
        captures[num_captures].length = steps;
        captures[num_captures].trap_bit = tbit;
        captures[num_captures].first_step = *step;
        num_captures++;
    }

    private void gen_0n(ulong tbit)
    {
        // There are no enemy pieces neighboring the trap
        int enemyoffset = -6;
        if (side == Side.BLACK)
        {
            enemyoffset = 6;
        }

        ulong t_neighbors = neighbors_of(tbit);
        if (tbit & pos.bitBoards[Piece.EMPTY])
        {
            // The Trap is empty
            ulong ncheckbits = t_neighbors;
            while (ncheckbits)
            {
                ulong nbit = ncheckbits & -ncheckbits;
                ncheckbits ^= nbit;
                bitix nix = bitindex(nbit);

                if (nbit & pos.placement[side] & ~pos.frozen)
                {
                    // neighbor has an unfrozen friendly piece
                    ulong possibles = neighbors_of(nbit) & pos.placement[side^1];
                    while (possibles)
                    {
                        ulong pbit = possibles & -possibles;
                        possibles ^= pbit;
                        bitix pix = bitindex(pbit);

                        if (pos.pieces[nix] > pos.pieces[pix] + enemyoffset)
                        {
                            ulong tobits =  neighbors_of(nbit) & ~tbit & ~pbit & pos.bitBoards[Piece.EMPTY];
                            bool tobits_handled = false;
                            if (pos.strongest[side][nix] > pos.pieces[pix] + enemyoffset)
                            {
                                ulong pospushers = neighbors_of(nbit) & pos.placement[side];
                                while (pospushers)
                                {
                                    ulong push = pospushers & -pospushers;
                                    bitix pushix = bitindex(push);
                                    if (pos.pieces[pushix] > pos.pieces[pix] + enemyoffset
                                            && (pos.pieces[pushix] >= pos.strongest[side^1][pushix] + enemyoffset
                                                || (neighbors_of(push) & pos.placement[side] & ~nbit)))
                                    {
                                        break;
                                    }
                                    pospushers ^= push;
                                }
                                if (pospushers)
                                {
                                    if (tobits)
                                    {
                                         // There should only be one bit in tobits set
                                        assert (tobits == (tobits & -tobits));
                                        add_capture(pos.pieces[pix], pbit, 4, tbit, nbit, tobits);
                                        tobits_handled = true;
                                    }
                                    if (!(t_neighbors & ~nbit & pos.placement[side]))
                                    {
                                        add_capture(pos.pieces[pix], pbit, 4, tbit, nbit, tbit);
                                    }
                                }
                            }
                            if (!tobits_handled)
                            {
                                while (tobits)
                                {
                                    ulong tobit = tobits & -tobits;
                                    tobits ^= tobit;
                                    bitix toix = bitindex(tobit);

                                    if (pos.pieces[nix] >= (pos.strongest[side^1][toix] + enemyoffset)
                                            || (neighbors_of(tobit) & pos.placement[side] & ~nbit))
                                    {
                                        add_capture(pos.pieces[pix], pbit, 4, tbit, nbit, tobit);
                                        break;
                                    }
                                }
                            }

                            if ((t_neighbors & pos.bitBoards[Piece.EMPTY])
                                    && (t_neighbors & ~nbit & pos.placement[side]))
                            {
                                add_capture(pos.pieces[pix], pbit, 4, tbit, nbit, tbit);
                            }
                        }
                    }
                } else if (nbit & pos.bitBoards[Piece.EMPTY])
                {
                    // the neighbor is empty
                    ulong possibles = neighbors_of(nbit) & pos.placement[side^1];
                    while (possibles)
                    {
                        ulong pbit = possibles & -possibles;
                        possibles ^= pbit;
                        bitix pix = bitindex(pbit);

                        if ((side == pos.side) && (nbit == (1UL << pos.lastfrom))
                                && (pos.lastpiece > pos.pieces[pix] + enemyoffset))
                        {
                            // can pull piece closer to trap
                            ulong finishers = neighbors_of(nbit) & pos.placement[side] & ~pos.frozen;
                            while (finishers)
                            {
                                ulong fbit = finishers & -finishers;
                                finishers ^= fbit;
                                bitix fix = bitindex(fbit);

                                if (pos.pieces[fix] > pos.pieces[pix] + enemyoffset)
                                {
                                    // can finish trap
                                    add_capture(pos.pieces[pix], pbit, 3, tbit, pbit, nbit);
                                    break;
                                }
                            }
                        }

                        ulong pneighbors = neighbors_of(pbit) & pos.placement[side] & ~pos.frozen;
                        while (pneighbors)
                        {
                            ulong pnbit = pneighbors & -pneighbors;
                            pneighbors ^= pnbit;
                            bitix pnix = bitindex(pnbit);

                            if (pos.pieces[pnix] > pos.pieces[pix] + enemyoffset)
                            {
                                ulong p_neighbors = neighbors_of(pbit);
                                bool safe_push = pos.pieces[pnix] >= pos.strongest[side^1][pix] + enemyoffset
                                    || (p_neighbors & pos.placement[side] & ~pnbit);
                                if (!safe_push && (p_neighbors & TRAPS)
                                        && !(neighbors_of(p_neighbors & TRAPS) & pos.placement[side^1] & ~pbit))
                                {
                                    // after pushing pnbit may freeze but possibly the freezer will be trapped
                                    safe_push = true;
                                    ulong posfreezers = p_neighbors & pos.placement[side^1] & ~TRAPS;
                                    while (posfreezers)
                                    {
                                        ulong pfbit = posfreezers & -posfreezers;
                                        posfreezers ^= pfbit;
                                        bitix pfix = bitindex(pfbit);
                                        if (pos.pieces[pnix] < pos.pieces[pfix] + enemyoffset)
                                        {
                                            safe_push = false;
                                            break;
                                        }
                                    }
                                }
                                if (safe_push)
                                {
                                    // This piece won't be frozen and can finish trap
                                    add_capture(pos.pieces[pix], pbit, 4, tbit, pbit, nbit, true);
                                    break;
                                } else if (pos.strongest[side][nix] > pos.pieces[pix] + enemyoffset)
                                {
                                    // possibly another neighbor of nix can finish the trap
                                    bool finished = false;
                                    ulong finishers = neighbors_of(nbit) & pos.placement[side] & ~pos.frozen;
                                    while (finishers)
                                    {
                                        ulong fbit = finishers & -finishers;
                                        finishers ^= fbit;
                                        bitix fix = bitindex(fbit);

                                        if (!(neighbors_of(fbit) & pos.placement[side] & ~pnbit)
                                                && pos.pieces[fix] < pos.strongest[side^1][fix] + enemyoffset)
                                            continue;

                                        if (pos.pieces[fix] > pos.pieces[pix] + enemyoffset)
                                        {
                                            // can finish trap
                                            add_capture(pos.pieces[pix], pbit, 4, tbit, pbit, nbit, true);
                                            break;
                                        }
                                    }
                                    if (finished)
                                        break;
                                }
                            }
                        }
                    }

                    ulong enn = neighbors_of(nbit) & pos.bitBoards[Piece.EMPTY] & ~t_neighbors & neighbors_of(pos.placement[side^1]);
                    while (enn)
                    {
                        ulong ennbit = enn & -enn;
                        enn ^= ennbit;
                        bitix ennix = bitindex(ennbit);

                        ulong oneighbors = neighbors_of(ennbit) & pos.placement[side^1];
                        while (oneighbors)
                        {
                            ulong onbit = oneighbors & - oneighbors;
                            oneighbors ^= onbit;
                            bitix onix = bitindex(onbit);

                            if (pos.strongest[side][onix] > pos.pieces[onix] + enemyoffset)
                            {
                                ulong onn = neighbors_of(onbit) & pos.placement[side];
                                if (!(onbit & TRAPS)
                                        || popcount(onn) > 1)
                                {
                                    onn &= ~pos.frozen;
                                    while (onn)
                                    {
                                        ulong pusher = onn & -onn;
                                        onn ^= pusher;
                                        bitix pushix = bitindex(pusher);

                                        if (pos.pieces[pushix] > pos.pieces[onix] + enemyoffset
                                                && pos.pieces[pushix] >= pos.strongest[side^1][onix] + enemyoffset
                                                && pos.pieces[pushix] >= pos.strongest[side^1][ennix] + enemyoffset
                                                && pos.pieces[pushix] >= pos.strongest[side^1][nix] + enemyoffset)
                                        {
                                            add_capture(pos.pieces[onix], onbit, 6, tbit, onbit, ennbit, true);
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        } else {
            // no enemy pieces neighboring the trap and it's not empty so
            // it seems there must be a friendly piece sitting on the trap
            assert (tbit & pos.placement[side]);

            bitix tix = bitindex(tbit);
            ulong lastbit = 1UL << pos.lastfrom;
            if ((side == pos.side) && (t_neighbors & lastbit)
                    && (t_neighbors & pos.bitBoards[Piece.EMPTY]))
            {
                ulong possibles = neighbors_of(lastbit) & pos.placement[side^1];
                while (possibles)
                {
                    ulong pbit = possibles & -possibles;
                    possibles ^= pbit;
                    bitix pix = bitindex(pbit);

                    if ((pos.lastpiece > pos.pieces[pix] + enemyoffset)
                            && (pos.pieces[tix] > pos.pieces[pix] + enemyoffset)
                            && (neighbors_of(tbit) & pos.bitBoards[Piece.EMPTY]
                                & ~lastbit))
                    {
                        add_capture(pos.pieces[pix], pbit, 3, tbit, pbit, lastbit);
                    }
                }
            }
            int ft_pop = popcount(t_neighbors & pos.placement[side]);
            if (ft_pop < 3)
            {
                // see if something can be pushed toward the trap that the
                // trap piece can then pull onto the trap
                ulong possibles = neighbors_of(t_neighbors
                        & pos.bitBoards[Piece.EMPTY]) & pos.placement[side^1]
                    & neighbors_of(pos.placement[side] & ~pos.frozen
                            & ~pos.bitBoards[Piece.WRABBIT + (side * 6)]);
                while (possibles)
                {
                    ulong pbit = possibles & -possibles;
                    possibles ^= pbit;
                    bitix pix = bitindex(pbit);
                    if (pos.strongest[side][pix] > pos.pieces[pix] + enemyoffset
                            && pos.pieces[tix] > pos.pieces[pix] + enemyoffset)
                    {
                        ulong tobits = neighbors_of(pbit) & t_neighbors
                            & pos.bitBoards[Piece.EMPTY];
                        ulong pushers = neighbors_of(pbit) & pos.placement[side]
                            & ~pos.frozen & ~pos.bitBoards[Piece.WRABBIT + (side * 6)];
                        if (ft_pop == 1)
                            pushers &= ~t_neighbors;
                        while (pushers)
                        {
                            ulong atbit = pushers & -pushers;
                            pushers ^= atbit;
                            bitix atix = bitindex(atbit);
                            if (pos.pieces[atix] > pos.pieces[pix] + enemyoffset)
                            {
                                while (tobits)
                                {
                                    ulong tobit = tobits & -tobits;
                                    tobits ^= tobit;
                                    add_capture(pos.pieces[pix], pbit, 4, tbit, pbit, tobit, true);
                                }
                                break;
                            }
                        }
                    }
                }
            }
            if (ft_pop == 1)
            {
                ulong atbit = t_neighbors & pos.placement[side];
                bitix atix = bitindex(atbit);
                Piece at_piece = pos.pieces[atix];
                // the piece on the trap will be captured if the neighbor moves
                ulong at_neighbors = neighbors_of(atbit);

                ulong possibles = at_neighbors & pos.placement[side^1];
                while (possibles)
                {
                    ulong pbit = possibles & -possibles;
                    possibles ^= pbit;
                    bitix pix = bitindex(pbit);

                    if (at_piece > pos.pieces[pix] + enemyoffset)
                    {
                        bool can_finish = true;
                        if (at_piece < pos.strongest[side^1][pix] + enemyoffset
                                && !(neighbors_of(pbit) & pos.placement[side] & ~atbit))
                        {
                            can_finish = false;
                            ulong finishers = neighbors_of(neighbors_of(pbit) & t_neighbors
                                & pos.bitBoards[Piece.EMPTY]) & pos.placement[side] & ~tbit
                                & ~pos.bitBoards[Piece.WRABBIT + (side * 6)] & ~pos.frozen;
                            while (finishers)
                            {
                                ulong fbit = finishers & -finishers;
                                finishers ^= fbit;
                                Piece fpiece = pos.pieces[bitindex(fbit)];
                                if (fpiece > pos.pieces[pix] + enemyoffset)
                                {
                                    can_finish = true;
                                    break;
                                }
                            }
                        }
                        if (can_finish)
                        {
                            ulong ptobit = neighbors_of(pbit) & t_neighbors & pos.bitBoards[Piece.EMPTY];
                            if (ptobit)
                            {
                                add_capture(pos.pieces[pix], pbit, 4, tbit, pbit, ptobit, true);
                            }
                        }
                        ulong tobits = at_neighbors & pos.bitBoards[Piece.EMPTY];
                        while (tobits)
                        {
                            ulong tobit = tobits & -tobits;
                            tobits ^= tobit;
                            bitix toix = bitindex(tobit);

                            if (at_piece < pos.strongest[side^1][toix] + enemyoffset
                                && !(neighbors_of(tobit) & pos.placement[side] & ~atbit))
                            {
                                ulong finishers = neighbors_of(atbit) & pos.placement[side] & ~tbit
                                    & ~pos.bitBoards[Piece.WRABBIT + (side * 6)] & ~pos.frozen;
                                while (finishers)
                                {
                                    ulong fbit = finishers & -finishers;
                                    bitix fix = bitindex(fbit);

                                    if (pos.pieces[fix] > pos.pieces[pix] + enemyoffset
                                            && (pos.pieces[fix] >= pos.strongest[side^1][fix] + enemyoffset
                                                || (neighbors_of(fbit) & pos.placement[side] & ~atbit)))
                                        break;
                                    finishers ^= fbit;
                                }
                                if (!finishers)
                                    continue;
                            }
                            add_capture(pos.pieces[pix], pbit, 4, tbit, atbit, tobit);
                        }

                    }
                }
            }
            else if (ft_pop < 4)
            {
                Piece t_piece = pos.pieces[tix];
                ulong ft_neighbors = t_neighbors & pos.placement[side]
                    & ~pos.bitBoards[Piece.WRABBIT + (side * 6)];
                while (ft_neighbors)
                {
                    ulong atbit = ft_neighbors & -ft_neighbors;
                    ft_neighbors ^= atbit;
                    bitix atix = bitindex(atbit);
                    Piece at_piece = pos.pieces[atix];

                    ulong at_neighbors = neighbors_of(atbit);

                    ulong possibles = at_neighbors & pos.placement[side^1];
                    while (possibles)
                    {
                        ulong pbit = possibles & -possibles;
                        possibles ^= pbit;
                        bitix pix = bitindex(pbit);

                        if (at_piece > pos.pieces[pix] + enemyoffset
                                && t_piece > pos.pieces[pix] + enemyoffset)
                        {
                            ulong empties = at_neighbors & pos.bitBoards[Piece.EMPTY];
                            while (empties)
                            {
                                ulong tobit = empties & -empties;
                                empties ^= tobit;
                                add_capture(pos.pieces[pix], pbit, 4, tbit, atbit, tobit);
                            }
                            ulong ptobit = neighbors_of(pbit) & t_neighbors & pos.bitBoards[Piece.EMPTY];
                            if (ptobit)
                            {
                                add_capture(pos.pieces[pix], pbit, 4, tbit, pbit, ptobit, true);
                            }
                        }
                    }
                }
            }
        }
    }

    private void gen_1n(ulong tbit)
    {
        // One enemy piece neighboring the trap
        int enemyoffset = -6;
        int pieceoffset = 0;
        if (side == Side.BLACK)
        {
            enemyoffset = 6;
            pieceoffset = 6;
        }

        bitix tix = bitindex(tbit);
        ulong t_neighbors = neighbors_of(tbit);
        ulong pbit = t_neighbors & pos.placement[side^1];
        bitix pix = bitindex(pbit);
        ulong lastbit = 1UL << pos.lastfrom;
        if (tbit & pos.placement[side^1])
        {
            ulong pneighbors = neighbors_of(pbit);
            if ((side == pos.side) && (pneighbors & lastbit)
                    && (pos.lastpiece > pos.pieces[pix] + enemyoffset))
            {
                add_capture(pos.pieces[tix], tbit, 1, tbit, pbit, lastbit);
            }

            while (pneighbors)
            {
                ulong pnbit = pneighbors & -pneighbors;
                pneighbors ^= pnbit;
                bitix pnix = bitindex(pnbit);

                if (pnbit & pos.placement[side])
                {
                    if (pnbit & ~pos.frozen)
                    {
                        if (pos.pieces[pnix] > pos.pieces[pix] + enemyoffset)
                        {
                            ulong pushtos = neighbors_of(pbit) & pos.bitBoards[Piece.EMPTY];
                            while (pushtos)
                            {
                                ulong tobit = pushtos & -pushtos;
                                pushtos ^= tobit;

                                add_capture(pos.pieces[tix], tbit, 2, tbit, pbit, tobit, true);
                            }
                            ulong pulltos = neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY];
                            while (pulltos)
                            {
                                ulong tobit = pulltos & -pulltos;
                                pulltos ^= tobit;

                                add_capture(pos.pieces[tix], tbit, 2, tbit, pnbit, tobit);
                            }

                            ulong clear = neighbors_of(pbit) & pos.placement[side] & ~pnbit;
                            while (clear)
                            {
                                ulong cbit = clear & -clear;
                                clear ^= cbit;

                                ulong pobits = neighbors_of(cbit) & ~pbit;
                                ulong ebits = pobits & pos.bitBoards[Piece.EMPTY];
                                if (cbit & pos.bitBoards[Piece.WRABBIT + pieceoffset])
                                {
                                    ulong backward = (side == Side.WHITE) ? cbit >> 8 : cbit << 8;
                                    pobits &= ~backward;
                                }
                                if (cbit & ~pos.frozen)
                                {
                                    bitix cix = bitindex(cbit);
                                    bool canfreeze = popcount(neighbors_of(cbit) & pos.placement[side]) == 1
                                        && pos.pieces[cix] < pos.strongest[side^1][cix] + enemyoffset;
                                    while (pobits)
                                    {
                                        ulong pobit = pobits & -pobits;
                                        pobits ^= pobit;

                                        if (pobit & pos.bitBoards[Piece.EMPTY])
                                        {
                                            add_capture(pos.pieces[tix], tbit, 3, tbit, cbit, pobit);
                                        }
                                        else if (pobit & pos.placement[side] && !canfreeze)
                                        {
                                            ulong aways = neighbors_of(pobit) & pos.bitBoards[Piece.EMPTY];
                                            if (pobit & pos.bitBoards[Piece.WRABBIT + pieceoffset])
                                            {
                                                ulong backward = (side == Side.WHITE) ? pobit >> 8 : pobit << 8;
                                                aways &= ~backward;
                                            }
                                            while (aways)
                                            {
                                                ulong abit = aways & -aways;
                                                aways ^= abit;
                                                add_capture(pos.pieces[tix], tbit, 4, tbit, pobit, abit);
                                            }
                                        }
                                        else if (pobit & pos.placement[side^1])
                                        {
                                            bitix opix = bitindex(pobit);
                                            if (pos.pieces[cix] > pos.pieces[opix] + enemyoffset)
                                            {
                                                ulong tobits = neighbors_of(pobit)
                                                    & pos.bitBoards[Piece.EMPTY] & ~t_neighbors;
                                                while (tobits)
                                                {
                                                    ulong tobit = tobits & -tobits;
                                                    tobits ^= tobit;
                                                    add_capture(pos.pieces[tix], tbit, 4, tbit, pobit, tobit, true);
                                                }
                                            }
                                        }
                                    }
                                }
                                else if (ebits != (ebits & -ebits))
                                {
                                    // clear is frozen and has more than one empty space around it
                                    pobits &= ebits;
                                    if (pobits == (pobits & -pobits))
                                        ebits ^= pobits;
                                    while (ebits)
                                    {
                                        ulong empty = ebits & -ebits;
                                        ebits ^= empty;

                                        ulong forward = (side == Side.WHITE) ? empty << 8 : empty >> 8;
                                        ulong unfreezers = neighbors_of(empty) & pos.placement[side]
                                            & ~pos.frozen & ~(pos.bitBoards[Piece.WRABBIT + pieceoffset]
                                                    & forward);
                                        while (unfreezers)
                                        {
                                            ulong unbit = unfreezers & -unfreezers;
                                            unfreezers ^= unbit;
                                            add_capture(pos.pieces[tix], tbit, 4, tbit, unbit, empty);
                                        }
                                    }
                                }
                            }

                            bool pn_safe = false;
                            clear = neighbors_of(pnbit) & pos.placement[side];
                            if (pos.pieces[pnix] >= pos.strongest[side^1][pnix] + enemyoffset
                                    || (clear != (clear & -clear)))
                            {
                                pn_safe = true;
                                while (clear)
                                {
                                    ulong cbit = clear & -clear;
                                    clear ^= cbit;
                                    bitix cix = bitindex(cbit);

                                    ulong posouts = neighbors_of(cbit) & ~pnbit;
                                    if (cbit & pos.bitBoards[Piece.WRABBIT + pieceoffset])
                                    {
                                        ulong backward = (side == Side.WHITE) ? cbit >> 8 : cbit << 8;
                                        posouts &= ~backward;
                                    }
                                    while (posouts)
                                    {
                                        ulong pobit = posouts & -posouts;
                                        posouts ^= pobit;

                                        if (pobit & pos.bitBoards[Piece.EMPTY])
                                        {
                                            add_capture(pos.pieces[tix], tbit, 3, tbit, cbit, pobit);
                                        }
                                        else if (pobit & pos.placement[side])
                                        {
                                            ulong empties = neighbors_of(pobit) & pos.bitBoards[Piece.EMPTY];
                                            if (pobit & pos.bitBoards[Piece.WRABBIT + pieceoffset])
                                            {
                                                ulong backward = (side == Side.WHITE) ? pobit >> 8 : pobit << 8;
                                                empties &= ~backward;
                                            }
                                            while (empties)
                                            {
                                                ulong tobit = empties & -empties;
                                                empties ^= tobit;
                                                add_capture(pos.pieces[tix], tbit, 4, tbit, pobit, tobit);
                                            }
                                        } else {
                                            // pobit must be opponent peice
                                            assert (pobit & pos.placement[side^1]);
                                            bitix poix = bitindex(pobit);
                                            if (pos.pieces[cix] > pos.pieces[poix] + enemyoffset)
                                            {
                                                ulong tobits = neighbors_of(pobit)
                                                    & pos.bitBoards[Piece.EMPTY] & ~t_neighbors;
                                                if (pos.pieces[pnix] < pos.pieces[poix] + enemyoffset
                                                        && !(neighbors_of(pnbit) & pos.placement[side] & ~cbit))
                                                    tobits &= ~neighbors_of(pnbit);
                                                while (tobits)
                                                {
                                                    ulong tobit = tobits & -tobits;
                                                    tobits ^= tobit;
                                                    add_capture(pos.pieces[tix], tbit, 4, tbit, pobit, tobit, true);
                                                }
                                            }
                                        }
                                    }
                                }
                            }

                            // can we pull an opponent away from p so pn can push it
                            clear = neighbors_of(pbit) & pos.placement[side^1] & ~tbit;
                            while (clear)
                            {
                                ulong cbit = clear & -clear;
                                clear ^= cbit;
                                bitix cix = bitindex(cbit);

                                ulong c_neighbors = neighbors_of(cbit);
                                if ((c_neighbors & lastbit) && (lastbit & ~t_neighbors)
                                        && pos.lastpiece > pos.pieces[cix] + enemyoffset
                                        && ((lastbit & ~neighbors_of(pnbit))
                                                || pos.pieces[pnix] >= pos.pieces[cix] + enemyoffset
                                                || (neighbors_of(pnbit) & pos.placement[side])))
                                {
                                    add_capture(pos.pieces[tix], tbit, 3, tbit, cbit, lastbit);
                                }
                                ulong pullers = c_neighbors & ~t_neighbors & ~pos.frozen
                                    & pos.placement[side] & neighbors_of(pos.bitBoards[Piece.EMPTY])
                                    & ~pos.bitBoards[Piece.WRABBIT + pieceoffset];
                                if (!pn_safe)
                                    pullers &= ~neighbors_of(pnbit);
                                while (pullers)
                                {
                                    ulong pullbit = pullers & -pullers;
                                    pullers ^= pullbit;
                                    bitix pullix = bitindex(pullbit);
                                    if ((pullbit & neighbors_of(pnbit))
                                            && pos.pieces[pnix] < pos.pieces[cix] + enemyoffset
                                            && !(neighbors_of(pnbit) & pos.placement[side] & ~pullbit))
                                        continue;
                                    if (pos.pieces[pullix] > pos.pieces[cix] + enemyoffset)
                                    {
                                        ulong tobits = neighbors_of(pullbit) & pos.bitBoards[Piece.EMPTY];
                                        while (tobits)
                                        {
                                            ulong tobit = tobits & -tobits;
                                            tobits ^= tobit;
                                            add_capture(pos.pieces[tix], tbit, 4, tbit, pullbit, tobit);
                                        }
                                    }
                                }
                            }

                            // can we pull an opponent away from pn so it has space to pull
                            clear = neighbors_of(pnbit) & pos.placement[side^1] & ~pbit;
                            while (clear)
                            {
                                ulong cbit = clear & -clear;
                                clear ^= cbit;
                                bitix cix = bitindex(cbit);

                                ulong c_neighbors = neighbors_of(cbit);
                                if ((c_neighbors & lastbit)
                                        && pos.lastpiece > pos.pieces[cix] + enemyoffset)
                                {
                                    add_capture(pos.pieces[tix], tbit, 3, tbit, cbit, lastbit);
                                }
                                if ((cbit & TRAPS)
                                        && (neighbors_of(neighbors_of(cbit) & pos.placement[side^1])
                                            & lastbit))
                                {
                                    ulong holder = neighbors_of(cbit) & pos.placement[side^1];
                                    if (holder == (holder & -holder))
                                    {
                                        assert (neighbors_of(holder) & lastbit);
                                        Piece hpiece = pos.pieces[bitindex(holder)];
                                        if (pos.lastpiece > hpiece + enemyoffset)
                                        {
                                            add_capture(pos.pieces[tix], tbit, 3, tbit, holder, lastbit);
                                        }
                                    }
                                }
                                ulong pullers = c_neighbors & ~pnbit & ~pos.frozen
                                    & pos.placement[side] & neighbors_of(pos.bitBoards[Piece.EMPTY])
                                    & ~pos.bitBoards[Piece.WRABBIT + pieceoffset];
                                while (pullers)
                                {
                                    ulong pullbit = pullers & -pullers;
                                    pullers ^= pullbit;
                                    bitix pullix = bitindex(pullbit);
                                    if (pos.pieces[pullix] > pos.pieces[cix] + enemyoffset)
                                    {
                                        ulong tobits = neighbors_of(pullbit) & pos.bitBoards[Piece.EMPTY];
                                        while (tobits)
                                        {
                                            ulong tobit = tobits & -tobits;
                                            tobits ^= tobit;
                                            add_capture(pos.pieces[tix], tbit, 4, tbit, pullbit, tobit);
                                        }
                                    }
                                }
                            }
                        }

                        // can this piece move out of the way and have another piece do the push/pull
                        ulong finishers = neighbors_of(pnbit);
                        if ((finishers & pos.bitBoards[Piece.EMPTY])
                                && (finishers & pos.placement[side] & ~pos.frozen))
                        {
                            finishers &= pos.placement[side] & ~pos.frozen;
                            while (finishers)
                            {
                                ulong fbit = finishers & -finishers;
                                finishers ^= fbit;
                                bitix fix = bitindex(fbit);

                                if ((pos.pieces[fix] > pos.pieces[pix] + enemyoffset)
                                        && ((neighbors_of(fbit) & pos.placement[side] & ~pnbit)
                                            || ((fbit & ~TRAPS)
                                                && (pos.pieces[fix] >= pos.strongest[side^1][fix] + enemyoffset))))
                                {
                                    // finisher can push pix and won't be frozen or safe in pn moves away
                                    ulong tobits = neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY];
                                    if (pos.pieces[pnix] == Piece.WRABBIT + pieceoffset)
                                    {
                                        if (side == Side.WHITE)
                                        {
                                            tobits &= ~((pnbit & NOT_RANK_1) >> 8);
                                        } else {
                                            tobits &= ~((pnbit & NOT_RANK_8) << 8);
                                        }
                                    }

                                    bool real_finish = false;
                                    while (tobits)
                                    {
                                        ulong tobit = tobits & -tobits;
                                        tobits ^= tobit;

                                        if ((tobit & ~TRAPS)
                                                || (neighbors_of(pnbit) & pos.placement[side] & ~fbit)
                                                || (neighbors_of(tobit) & pos.placement[side] & ~pnbit & ~fbit)
                                                || (pos.pieces[fix] >= pos.strongest[side^1][pnix] + enemyoffset))
                                        {
                                            // pn square will be safe for finisher after pn piece moves away
                                            real_finish = true;
                                            add_capture(pos.pieces[tix], tbit, 4, tbit, pnbit, tobit);
                                        }
                                    }
                                    if (real_finish)
                                    {
                                        break;
                                    }
                                }
                            }
                        }
                    } else if (pos.pieces[pnix] > pos.pieces[pix] + enemyoffset)
                    {
                        assert(pnbit & pos.frozen);
                        // pn is frozen can we unfreeze in two steps or less
                        ulong pn_neighbors = neighbors_of(pnbit) & ~pbit;
                        while (pn_neighbors)
                        {
                            ulong pnnbit = pn_neighbors & -pn_neighbors;
                            pn_neighbors ^= pnnbit;

                            if (pnnbit & pos.bitBoards[Piece.EMPTY])
                            {
                                ulong pnn_neighbors = neighbors_of(pnnbit) & ~pos.placement[side^1] & ~pnbit;
                                while (pnn_neighbors)
                                {
                                    ulong pnnnbit = pnn_neighbors & -pnn_neighbors;
                                    pnn_neighbors ^= pnnnbit;
                                    bitix pnnnix = bitindex(pnnnbit);

                                    if ((pnnnbit & pos.bitBoards[Piece.EMPTY])
                                            && ((neighbors_of(pbit) & pos.bitBoards[Piece.EMPTY])
                                                || (neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY] & ~pnnbit)))
                                    {
                                        ulong unfreezers = neighbors_of(pnnnbit) & pos.placement[side] & ~pos.frozen;
                                        while (unfreezers)
                                        {
                                            ulong unbit = unfreezers & -unfreezers;
                                            unfreezers ^= unbit;
                                            bitix unix = bitindex(unbit);

                                            if ((pos.placement[side] & neighbors_of(pnnnbit) & ~unbit)
                                                    || ((pnnnbit & ~TRAPS)
                                                        && (pos.pieces[unix] >= pos.strongest[side^1][pnnnix] + enemyoffset)))
                                            {
                                                if (pos.pieces[unix] == Piece.WRABBIT + pieceoffset)
                                                {
                                                    // can it really make the two steps to pnn
                                                    ulong rsteps;
                                                    if (side == Side.WHITE)
                                                    {
                                                        rsteps = (unbit & ~B_FILE) << 2;
                                                        rsteps |= (unbit & ~G_FILE) >> 2;
                                                        rsteps |= (unbit & NOT_RANK_8 & NOT_A_FILE) << 9;
                                                        rsteps |= (unbit & NOT_RANK_8 & NOT_H_FILE) << 7;
                                                        rsteps |= (unbit & ~RANK_7) << 16;
                                                    } else {
                                                        rsteps = (unbit & ~B_FILE) << 2;
                                                        rsteps |= (unbit & ~G_FILE) >> 2;
                                                        rsteps |= (unbit & NOT_RANK_1 & NOT_A_FILE) >> 7;
                                                        rsteps |= (unbit & NOT_RANK_1 & NOT_H_FILE) >> 9;
                                                        rsteps |= (unbit & ~RANK_2) >> 16;
                                                    }
                                                    if (!(rsteps & pnnbit))
                                                    {
                                                        // rabbit can't get there.
                                                        continue;
                                                    }
                                                }
                                                add_capture(pos.pieces[tix], tbit, 4, tbit, unbit, pnnnbit);
                                            }
                                        }
                                    }
                                    else if (pnnnbit & pos.placement[side])
                                    {
                                        if (pos.pieces[pnnnix] == Piece.WRABBIT + pieceoffset)
                                        {
                                            ulong rsteps = neighbors_of(pnnnbit);
                                            if (side == Side.WHITE)
                                            {
                                                rsteps &= ~((pnnnbit & NOT_RANK_1) >> 8);
                                            } else {
                                                rsteps &= ~((pnnnbit & NOT_RANK_8) << 8);
                                            }
                                            if (!(rsteps & pnnbit))
                                            {
                                                continue;
                                            }
                                        }

                                        if (pnnnbit & pos.frozen)
                                        {
                                            if (!(neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY] & ~pnnbit)
                                                && !(neighbors_of(pbit) & (pos.bitBoards[Piece.EMPTY] | pnnnbit)))
                                                continue;
                                            // can we unfreeze in one step
                                            ulong unfreezers = neighbors_of(neighbors_of(pnnnbit) & pos.bitBoards[Piece.EMPTY])
                                                & pos.placement[side] & ~pos.frozen;
                                            while (unfreezers)
                                            {
                                                ulong unbit = unfreezers & -unfreezers;
                                                unfreezers ^= unbit;
                                                bitix unix = bitindex(unbit);

                                                ulong tobits = neighbors_of(unbit) & neighbors_of(pnnnbit) & pos.bitBoards[Piece.EMPTY];
                                                if (pos.pieces[unix] == Piece.WRABBIT + pieceoffset)
                                                {
                                                    ulong rsteps = neighbors_of(unbit);
                                                    if (side == Side.WHITE)
                                                    {
                                                        rsteps &= ~((unbit & NOT_RANK_1) >> 8);
                                                    } else {
                                                        rsteps &= ~((unbit & NOT_RANK_8) << 8);
                                                    }
                                                    tobits &= rsteps;
                                                }
                                                while (tobits)
                                                {
                                                    ulong tobit = tobits & -tobits;
                                                    tobits ^= tobit;
                                                    add_capture(pos.pieces[tix], tbit, 4, tbit, unbit, tobit);
                                                }
                                            }
                                        }
                                        else if ((neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY] & ~pnnbit)
                                                || (neighbors_of(pbit) & (pos.bitBoards[Piece.EMPTY] | pnnnbit)))
                                        {
                                            add_capture(pos.pieces[tix], tbit, 3, tbit, pnnnbit, pnnbit);
                                        } else {
                                            // can unfreeze pn (attacker) in one step but have no where to push or
                                            // pull pbit to. Can we move another piece away from pbit to create space?
                                            ulong clear = neighbors_of(pbit) & pos.placement[side] & ~pos.frozen
                                                & neighbors_of(pos.bitBoards[Piece.EMPTY]);
                                            if (clear & ~pos.bitBoards[Piece.WRABBIT + pieceoffset])
                                            {
                                                add_capture(pos.pieces[tix], tbit, 4, tbit, pnnnbit, pnnbit);
                                            } else {
                                                // any clear pieces must be rabbits
                                                while (clear)
                                                {
                                                    ulong cbit = clear & -clear;
                                                    clear ^= cbit;
                                                    ulong backward = (side == Side.WHITE) ? cbit >> 8 : cbit << 8;
                                                    if (neighbors_of(cbit) & pos.bitBoards[Piece.EMPTY] & ~backward)
                                                    {
                                                        add_capture(pos.pieces[tix], tbit, 4, tbit, pnnnbit, pnnbit);
                                                        break;
                                                    }
                                                }
                                            }
                                            clear = neighbors_of(pnnnbit) & neighbors_of(pnbit) & pos.placement[side^1];
                                            if (clear)
                                            {
                                                Piece pupiece = pos.pieces[bitindex(pnnnbit)];
                                                Piece cpiece = pos.pieces[bitindex(clear)];
                                                if (pupiece > cpiece + enemyoffset)
                                                {
                                                    add_capture(pos.pieces[tix], tbit, 4, tbit, pnnnbit, pnnbit);
                                                }
                                            }
                                        }
                                    }
                                }
                            } else {
                                // pnn must have enemy piece can we push it away or pull and unfreeze pn
                                ulong ofreezers = neighbors_of(pnbit) & pos.placement[side^1] & ~pnnbit;
                                while (ofreezers)
                                {
                                    ulong fbit = ofreezers & -ofreezers;
                                    bitix fix = bitindex(fbit);
                                    if (pos.pieces[pnix] < pos.pieces[fix] + enemyoffset)
                                        break;
                                    ofreezers ^= fbit;
                                }

                                bitix pnnix = bitindex(pnnbit);
                                if (!ofreezers && (neighbors_of(pnnbit) & (1UL << pos.lastfrom))
                                            && (pos.lastpiece > pos.pieces[pnnix] + enemyoffset))
                                {
                                    add_capture(pos.pieces[tix], tbit, 3, tbit,
                                            pnnbit, (1UL << pos.lastfrom));
                                }
                                if (!ofreezers || (neighbors_of(pnnbit) & pos.bitBoards[Piece.EMPTY]))
                                {
                                    bool can_push = false;
                                    ulong pushers = neighbors_of(pnnbit) & pos.placement[side] & ~pos.frozen;
                                    while (pushers)
                                    {
                                        ulong perbit = pushers & -pushers;
                                        pushers ^= perbit;
                                        bitix perix = bitindex(perbit);

                                        if (pos.pieces[perix] > pos.pieces[pnnix] + enemyoffset)
                                        {
                                            can_push = true;
                                            if (!ofreezers)
                                            {
                                                ulong pulltos = neighbors_of(perbit) & pos.bitBoards[Piece.EMPTY];
                                                while (pulltos)
                                                {
                                                    ulong tobit = pulltos & -pulltos;
                                                    pulltos ^= tobit;

                                                    add_capture(pos.pieces[tix], tbit, 4, tbit, perbit, tobit);
                                                }
                                            }
                                        }
                                    }
                                    if (can_push)
                                    {
                                        ulong pushtos = neighbors_of(pnnbit) & pos.bitBoards[Piece.EMPTY];
                                        if (popcount(neighbors_of(pbit) & pos.bitBoards[Piece.EMPTY]) == 1
                                                && !(neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY]))
                                            pushtos &= ~neighbors_of(pbit);
                                        while (pushtos)
                                        {
                                            ulong tobit = pushtos & -pushtos;
                                            pushtos ^= tobit;

                                            add_capture(pos.pieces[tix], tbit, 4, tbit, pnnbit, tobit, true);
                                        }
                                    }
                                }
                                if (!ofreezers && (pnnbit & TRAPS)
                                        && popcount(neighbors_of(pnnbit) & pos.placement[side^1]) == 1)
                                {
                                    ulong holder = neighbors_of(pnnbit) & pos.placement[side^1];
                                    bitix hix = bitindex(holder);

                                    if ((neighbors_of(holder) & (1UL << pos.lastfrom))
                                            && pos.lastpiece > pos.pieces[hix] + enemyoffset)
                                    {
                                        add_capture(pos.pieces[tix], tbit, 3, tbit,
                                                holder, (1UL << pos.lastfrom));
                                    }

                                    bool can_push = false;
                                    ulong pushers = neighbors_of(holder) & pos.placement[side] & ~pos.frozen
                                        & ~pos.bitBoards[Piece.WRABBIT + pieceoffset];
                                    while (pushers)
                                    {
                                        ulong pubit = pushers & -pushers;
                                        pushers ^= pubit;
                                        bitix puix = bitindex(pubit);

                                        if (pos.pieces[puix] > pos.pieces[hix] + enemyoffset)
                                        {
                                            can_push = true;
                                            ulong tobits = neighbors_of(pubit) & pos.bitBoards[Piece.EMPTY];
                                            while (tobits)
                                            {
                                                ulong tobit = tobits & -tobits;
                                                tobits ^= tobit;

                                                add_capture(pos.pieces[tix], tbit, 4, tbit, pubit, tobit);
                                            }
                                        }
                                    }
                                    if (can_push)
                                    {
                                        ulong tobits = neighbors_of(holder) & pos.bitBoards[Piece.EMPTY];
                                        if (pos.pieces[pnix] < pos.pieces[hix] + enemyoffset)
                                            tobits &= ~neighbors_of(pnbit);
                                        while (tobits)
                                        {
                                            ulong tobit = tobits & -tobits;
                                            tobits ^= tobit;
                                            add_capture(pos.pieces[tix], tbit, 4, tbit, holder, tobit, true);
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else if (pnbit & pos.bitBoards[Piece.EMPTY])
                {
                    // Can we get a piece here to push pbit in two steps or less
                    ulong pn_neighbors = neighbors_of(pnbit) & ~pos.placement[side^1];
                    while (pn_neighbors)
                    {
                        ulong pnnbit = pn_neighbors & -pn_neighbors;
                        pn_neighbors ^= pnnbit;
                        bitix pnnix = bitindex(pnnbit);

                        if (pnnbit & pos.bitBoards[Piece.EMPTY]
                                && (pos.strongest[side][pnnix] > pos.pieces[pix] + enemyoffset))
                        {
                            ulong pushers = neighbors_of(pnnbit) & pos.placement[side] & ~pos.frozen;
                            while (pushers)
                            {
                                ulong perbit = pushers & -pushers;
                                pushers ^= perbit;
                                bitix perix = bitindex(perbit);

                                if ((pos.pieces[perix] > pos.pieces[pix] + enemyoffset)
                                        && ((pos.pieces[perix] >= pos.strongest[side^1][pnix] + enemyoffset)
                                            || (pos.placement[side] & neighbors_of(pnbit)
                                                & ~(TRAPS & ~neighbors_of(pos.placement[side] & ~perbit))))
                                        && ((pos.placement[side] & neighbors_of(pnnbit) & ~perbit)
                                            || !((pnnbit & TRAPS)
                                                || (pos.pieces[perix] < pos.strongest[side^1][pnnix] + enemyoffset))))
                                {
                                    add_capture(pos.pieces[tix], tbit, 4, tbit, perbit, pnnbit);
                                }
                            }
                        } else if (pos.pieces[pnnix] > pos.pieces[pix] + enemyoffset)
                        {
                            // pnn must be a friendly piece that can push pix
                            if (pnnbit & pos.frozen)
                            {
                                if ((neighbors_of(pnbit) & pos.placement[side] & ~pnnbit)
                                        || pos.pieces[pnnix] >= pos.strongest[side^1][pnix] + enemyoffset)
                                {
                                    ulong unfreezers = neighbors_of(neighbors_of(pnnbit)
                                            & pos.bitBoards[Piece.EMPTY] & ~pnbit)
                                        & pos.placement[side] & ~pos.frozen;
                                    if (pos.pieces[pnnix] < pos.strongest[side^1][pnix] + enemyoffset)
                                        unfreezers &= ~neighbors_of(pnbit);
                                    while (unfreezers)
                                    {
                                        ulong unbit = unfreezers & -unfreezers;
                                        unfreezers ^= unbit;
                                        bitix unix = bitindex(unbit);

                                        ulong tobits = neighbors_of(unbit) & neighbors_of(pnnbit)
                                            & pos.bitBoards[Piece.EMPTY] & ~pnbit;
                                        if (pos.pieces[unix] == Piece.WRABBIT + pieceoffset)
                                        {
                                            ulong rsteps = neighbors_of(unbit);
                                            if (side == Side.WHITE)
                                            {
                                                rsteps &= ~((unbit & NOT_RANK_1) >> 8);
                                            } else {
                                                rsteps &= ~((unbit & NOT_RANK_8) << 8);
                                            }
                                            tobits &= rsteps;
                                        }
                                        while (tobits)
                                        {
                                            ulong tobit = tobits & -tobits;
                                            tobits ^= tobit;
                                            add_capture(pos.pieces[tix], tbit, 4, tbit, unbit, tobit);
                                        }
                                    }
                                }
                            }
                            else if (pos.pieces[pnnix] >= pos.strongest[side^1][pnix] + enemyoffset
                                    || (neighbors_of(pnbit) & pos.placement[side] & ~pnnbit))
                            {
                                add_capture(pos.pieces[tix], tbit, 3, tbit, pnnbit, pnbit);
                            } else {
                                // pnn is unfrozen but will freeze when moving to pn
                                bool pnn_first = false;
                                ulong pnb_neighbors = neighbors_of(pnbit);
                                ulong pnn_neighbors = neighbors_of(pnnbit);
                                ulong unfreezers = neighbors_of(pbit)
                                    & pnn_neighbors & pos.placement[side];
                                if ((pnb_neighbors | (neighbors_of(pbit) & ~pnbit))
                                        & pos.bitBoards[Piece.EMPTY])
                                {
                                    unfreezers |= (neighbors_of(pnb_neighbors
                                                & pos.bitBoards[Piece.EMPTY])
                                            & pos.placement[side])
                                        | (pnn_neighbors & pos.placement[side]);
                                }
                                unfreezers &= ~pos.frozen;
                                while (unfreezers)
                                {
                                    ulong unfbit = unfreezers & -unfreezers;
                                    unfreezers ^= unfbit;
                                    bitix unfix = bitindex(unfbit);
                                    ulong unf_neighbors = neighbors_of(unfbit);
                                    ulong tobits = unf_neighbors & pnb_neighbors & pos.bitBoards[Piece.EMPTY]
                                        & ~(TRAPS & ~neighbors_of(pos.placement[side] & ~unfbit));
                                    ulong backward = 0UL;
                                    if (unfbit & pos.bitBoards[Piece.WRABBIT + pieceoffset])
                                    {
                                        backward = (side == Side.WHITE) ? unfbit >> 8 : unfbit << 8;
                                        tobits &= ~backward;
                                    }
                                    if (tobits && ((unfbit & ~pnn_neighbors)
                                                || (pnn_neighbors & pos.placement[side] & ~unfbit)
                                                || ((pos.pieces[pnnix] >= pos.strongest[side^1][pnnix] + enemyoffset)
                                                    && (pnnbit & ~TRAPS))))
                                    {
                                        // unfreezer can move first
                                        while (tobits)
                                        {
                                            ulong tobit = tobits & -tobits;
                                            tobits ^= tobit;
                                            add_capture(pos.pieces[tix], tbit, 4, tbit, unfbit, tobit);
                                        }
                                    }
                                    else if ((tobits || (unf_neighbors & (pnnbit
                                                        | (TRAPS & pnb_neighbors & pos.bitBoards[Piece.EMPTY])) & ~backward))
                                            && ((unf_neighbors & pos.placement[side] & ~pnnbit)
                                                || ((unfbit & ~TRAPS)
                                                    && (pos.pieces[unfix] >= pos.strongest[side^1][unfix] + enemyoffset))))
                                    {
                                        pnn_first = true;
                                    }
                                }
                                if (pnn_first)
                                {
                                    add_capture(pos.pieces[tix], tbit, 4, tbit, pnnbit, pnbit);
                                }
                            }
                        }
                    }
                } else if ((pos.strongest[side][pnix] > pos.pieces[pnix] + enemyoffset)
                        && (pos.strongest[side][pnix] > pos.pieces[pix] + enemyoffset))
                {
                    // pn must be an enemy
                    ulong pushtos = neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY] & ~neighbors_of(tbit);
                    if (pushtos)
                    {
                        ulong pushers = neighbors_of(pnbit) & pos.placement[side] & ~pos.frozen;
                        while (pushers)
                        {
                            ulong perbit = pushers & -pushers;
                            pushers ^= perbit;
                            bitix perix = bitindex(perbit);

                            if ((pos.pieces[perix] > pos.pieces[pnix] + enemyoffset)
                                    && (pos.pieces[perix] > pos.pieces[pix] + enemyoffset))
                            {
                                if (!(neighbors_of(pnbit) & pos.placement[side] & ~perbit)
                                        && pos.pieces[perix] < pos.strongest[side^1][pnix] + enemyoffset)
                                {
                                    // pusher will freeze unless freezer is trapped by first step
                                    ulong freezers = neighbors_of(pnbit) & pos.placement[side^1];
                                    if (!(freezers & (TRAPS & ~neighbors_of(pos.placement[side^1] & ~pnbit))))
                                        continue;
                                    freezers &= ~(TRAPS & ~neighbors_of(pos.placement[side^1] & ~pnbit));
                                    while (freezers)
                                    {
                                        ulong fbit = freezers & -freezers;
                                        bitix fix = bitindex(fbit);
                                        if (pos.pieces[perix] < pos.pieces[fix] + enemyoffset)
                                            break;
                                        freezers ^= fbit;
                                    }
                                    if (freezers)
                                        continue;
                                }

                                // pusher can finish it
                                while (pushtos)
                                {
                                    ulong tobit = pushtos & -pushtos;
                                    pushtos ^= tobit;
                                    add_capture(pos.pieces[tix], tbit, 4, tbit, pnbit, tobit, true);
                                    pushers = 0UL;
                                }
                            }
                        }
                    }
                }
            }
        } else {
            // Trap is either empty or has a friendly on it
            int min_clear_steps = 0;
            int num_clears = 0;
            Step[24] clear_first_step;
            int[24] clear_length;

            if (tbit & pos.placement[side])
            {
                min_clear_steps = 4;
                ulong tneighbors = neighbors_of(tbit) & ~pbit;
                int friendlies = popcount(tneighbors & pos.placement[side]);
                bool canpull = pos.pieces[tix] > pos.pieces[pix] + enemyoffset;
                if (pos.pieces[tix] == Piece.WRABBIT)
                {
                    tneighbors ^= tbit >> 8;
                } else if (pos.pieces[tix] == Piece.BRABBIT)
                {
                    tneighbors ^= tbit << 8;
                }
                while (tneighbors)
                {
                    ulong tnbit = tneighbors & -tneighbors;
                    tneighbors ^= tnbit;

                    if (tnbit & pos.bitBoards[Piece.EMPTY])
                    {
                        min_clear_steps = 1;
                        clear_first_step[num_clears].set(tbit, tnbit);
                        clear_length[num_clears] = 1;
                        num_clears++;
                    } else if ((tnbit & pos.placement[side])
                            && (friendlies > 1))
                    {
                        // tn has to be friendly piece
                        ulong tn_neighbors = neighbors_of(tnbit) & ~tbit;
                        if (tnbit & pos.bitBoards[Piece.WRABBIT + pieceoffset])
                        {
                            tn_neighbors &= ~(side == Side.WHITE ? tnbit >> 8 : tnbit << 8);
                        }
                        while (tn_neighbors)
                        {
                            ulong tnnbit = tn_neighbors & -tn_neighbors;
                            tn_neighbors ^= tnnbit;

                            if (tnnbit & pos.bitBoards[Piece.EMPTY])
                            {
                                if (min_clear_steps > 2)
                                {
                                    min_clear_steps = 2;
                                }
                                bitix tnix = bitindex(tnbit);
                                if ((pos.pieces[tnix] == Piece.WRABBIT
                                            && tnnbit == tnbit >> 8)
                                        || (pos.pieces[tnix] == Piece.BRABBIT
                                                && tnnbit == tnbit << 8))
                                {
                                    continue;
                                }

                                clear_first_step[num_clears].set(tnbit, tnnbit);
                                clear_length[num_clears] = 2;
                                num_clears++;
                            } else if (canpull)
                            {
                                if (tnnbit & pos.placement[side])
                                {
                                    ulong tobits = neighbors_of(tnnbit) & pos.bitBoards[Piece.EMPTY];
                                    if (tnnbit & pos.bitBoards[Piece.WRABBIT + pieceoffset])
                                    {
                                        if (side == Side.WHITE)
                                        {
                                            tobits &= ~((tnnbit & NOT_RANK_1) >> 8);
                                        } else {
                                            tobits &= ~((tnnbit & NOT_RANK_8) << 8);
                                        }
                                    }
                                    while (tobits)
                                    {
                                        ulong tobit = tobits & -tobits;
                                        tobits ^= tobit;

                                        if (min_clear_steps > 3)
                                        {
                                            min_clear_steps = 3;
                                        }
                                        clear_first_step[num_clears].set(tnnbit, tobit);
                                        clear_length[num_clears] = 3;
                                        num_clears++;
                                    }
                                } else if (pos.pieces[bitindex(tnbit)] > pos.pieces[bitindex(tnnbit)] + enemyoffset)
                                {
                                    // tnn has to be enemy piece
                                    ulong tobits = neighbors_of(tnnbit) & pos.bitBoards[Piece.EMPTY]
                                        & ~neighbors_of(tbit);
                                    while (tobits)
                                    {
                                        ulong tobit = tobits & -tobits;
                                        tobits ^= tobit;

                                        if (min_clear_steps > 3)
                                        {
                                            min_clear_steps = 3;
                                        }
                                        clear_first_step[num_clears].set(tnnbit, tobit, true);
                                        clear_length[num_clears] = 3;
                                        num_clears++;
                                    }
                                }
                            }
                        }
                    }
                }

                if (min_clear_steps > 3)
                {
                    return;
                }

                if (canpull)
                {
                    for (int i=0; i < num_clears; i++)
                    {
                        add_capture(pos.pieces[pix], pbit, 1 + clear_length[i], tbit, &clear_first_step[i]);
                    }
                    return;
                }
            }

            if ((side == pos.side) && (lastbit & tbit)
                    && (pos.lastpiece > pos.pieces[pix] + enemyoffset))
            {
                // Can finish a pull onto the trap
                add_capture(pos.pieces[pix], pbit, 1, tbit, pbit, lastbit);
            }

            ulong pneighbors = neighbors_of(pbit);
            while (pneighbors)
            {
                ulong pnbit = pneighbors & -pneighbors;
                pneighbors ^= pnbit;
                bitix pnix = bitindex(pnbit);

                if (pnbit & pos.placement[side])
                {
                    if (pnbit & tbit)
                    {
                        if ((min_clear_steps == 1)
                                && (pos.strongest[side][tix] > pos.pieces[pix] + enemyoffset))
                        {
                            ulong pullers = neighbors_of(tbit) & pos.placement[side];
                            while (pullers)
                            {
                                ulong pullbit = pullers & -pullers;
                                pullers ^= pullbit;
                                bitix pullix = bitindex(pullbit);

                                if ((pos.pieces[pullix] > pos.pieces[pix] + enemyoffset)
                                        && ((pos.pieces[pullix] >= pos.strongest[side^1][pullix] + enemyoffset)
                                            || (neighbors_of(pullbit) & pos.placement[side] & ~tbit)))
                                {
                                    for (int i=0; i < num_clears; i++)
                                    {
                                        if (clear_length[i] == 1)
                                        {
                                            add_capture(pos.pieces[pix], pbit, 4, tbit, &clear_first_step[i]);
                                        }
                                    }
                                }
                            }
                        }
                    } else if (pnbit & pos.frozen
                            && pos.pieces[pnix] > pos.pieces[pix] + enemyoffset
                            && min_clear_steps < 2)
                    {
                        ulong aneighbors = neighbors_of(pnbit) & ~pbit;
                        while (aneighbors)
                        {
                            ulong anbit = aneighbors & -aneighbors;
                            aneighbors ^= anbit;
                            bitix anix = bitindex(anbit);

                            if (anbit & pos.bitBoards[Piece.EMPTY])
                            {
                                ulong unfreezers = neighbors_of(anbit) & pos.placement[side] & ~pnbit;
                                while (unfreezers)
                                {
                                    ulong ufbit = unfreezers & -unfreezers;
                                    unfreezers ^= ufbit;

                                    if (ufbit & pos.bitBoards[Piece.WRABBIT + pieceoffset])
                                    {
                                        ulong rabbitsteps = neighbors_of(ufbit);
                                        if (side == Side.WHITE)
                                        {
                                            rabbitsteps &= ~((ufbit & NOT_RANK_1) >> 8);
                                        } else {
                                            rabbitsteps &= ~((ufbit & NOT_RANK_8) << 8);
                                        }
                                        if (!(rabbitsteps & anbit))
                                        {
                                            continue;
                                        }
                                    }

                                    if (ufbit & pos.frozen
                                            && min_clear_steps == 0)
                                    {
                                        // can we unfreeze the unfreezer?
                                        ulong unfunfreezers = neighbors_of(neighbors_of(ufbit) & pos.bitBoards[Piece.EMPTY])
                                            & pos.placement[side] & ~pos.frozen;
                                        while (unfunfreezers)
                                        {
                                            ulong ufufbit = unfunfreezers & -unfunfreezers;
                                            unfunfreezers ^= ufufbit;

                                            ulong tobits = neighbors_of(ufbit) & neighbors_of(ufufbit) & pos.bitBoards[Piece.EMPTY];
                                            if (ufufbit & pos.bitBoards[Piece.WRABBIT + pieceoffset])
                                            {
                                                ulong rabbitsteps = neighbors_of(ufufbit);
                                                if (side == Side.WHITE)
                                                {
                                                    rabbitsteps &= ~((ufufbit & NOT_RANK_1) >> 8);
                                                } else {
                                                    rabbitsteps &= ~((ufufbit & NOT_RANK_8) << 8);
                                                }
                                                tobits &= rabbitsteps;
                                            }
                                            while (tobits)
                                            {
                                                ulong tobit = tobits & -tobits;
                                                tobits ^= tobit;
                                                add_capture(pos.pieces[pix], pbit, 4, tbit, ufufbit, tobit);
                                            }
                                        }
                                    } else if (ufbit & ~pos.frozen
                                            && min_clear_steps < 2)
                                    {
                                        if (min_clear_steps && (ufbit & ~tbit))
                                        {
                                            for (int i=0; i < num_clears; i++)
                                            {
                                                add_capture(pos.pieces[pix], pbit, 3 + clear_length[i], tbit, &clear_first_step[i]);
                                            }
                                        } else {
                                            add_capture(pos.pieces[pix], pbit, 3, tbit, ufbit, anbit);
                                        }
                                    }
                                }

                                ulong tobits = neighbors_of(anbit) & pos.bitBoards[Piece.EMPTY];
                                while (tobits)
                                {
                                    ulong tobit = tobits & -tobits;
                                    tobits ^= tobit;
                                    bitix toix = bitindex(tobit);

                                    unfreezers = neighbors_of(tobit) & pos.placement[side] & ~pos.frozen;
                                    while (unfreezers)
                                    {
                                        ulong unfbit = unfreezers & -unfreezers;
                                        unfreezers ^= unfbit;
                                        bitix unfix = bitindex(unfbit);

                                        if ((pos.pieces[unfix] == Piece.WRABBIT
                                                    && unfbit >> 8 == tobit)
                                                || (pos.pieces[unfix] == Piece.BRABBIT
                                                    && unfbit << 8 == tobit))
                                        {
                                            continue;
                                        }

                                        if (((pos.pieces[unfix] >= pos.strongest[side^1][toix] + enemyoffset)
                                                    && !(tobit & TRAPS))
                                                || (neighbors_of(tobit) & pos.placement[side] & ~unfbit))
                                        {
                                            if (unfbit & pos.bitBoards[Piece.WRABBIT + pieceoffset])
                                            {
                                                ulong backward = unfbit | tobit;
                                                backward = (side == Side.WHITE) ? backward >> 8 : backward << 8;
                                                if ((tobit | anbit) & backward)
                                                    continue;
                                            }
                                            if (min_clear_steps && (neighbors_of(unfbit) & tbit)
                                                    && !(neighbors_of(tbit) & pos.placement[side] & ~unfbit))
                                            {
                                                add_capture(pos.pieces[pix], pbit, 4, tbit, unfbit, tobit);
                                            }
                                            if (min_clear_steps)
                                            {
                                                for (int i=0; i < num_clears; i++)
                                                {
                                                    add_capture(pos.pieces[pix], pbit, 4 + clear_length[i], tbit, &clear_first_step[i]);
                                                }
                                            } else {
                                                add_capture(pos.pieces[pix], pbit, 4, tbit, unfbit, tobit);
                                            }
                                        }
                                    }
                                }
                            } else {
                                // an is enemy piece can we push out of the way or pull and unfreeze pn
                                ulong ofreezers = neighbors_of(pnbit) & pos.placement[side^1] & ~anbit;
                                while (ofreezers)
                                {
                                    ulong fbit = ofreezers & -ofreezers;
                                    bitix fix = bitindex(fbit);
                                    if (pos.pieces[pnix] < pos.pieces[fix] + enemyoffset)
                                        break;
                                    ofreezers ^= fbit;
                                }

                                if ((min_clear_steps == 0)
                                        && (pos.strongest[side][anix] > pos.pieces[anix] + enemyoffset))
                                {
                                    if (!ofreezers || (neighbors_of(anbit) & pos.bitBoards[Piece.EMPTY]))
                                    {
                                        bool did_push = false;
                                        ulong pushers = neighbors_of(anbit) & pos.placement[side] & ~pos.frozen;
                                        while (pushers)
                                        {
                                            ulong perbit = pushers & -pushers;
                                            pushers ^= perbit;
                                            bitix perix = bitindex(perbit);

                                            if (pos.pieces[perix] > pos.pieces[anix] + enemyoffset)
                                            {
                                                if (!did_push)
                                                {
                                                    ulong pushtos = neighbors_of(anbit) & pos.bitBoards[Piece.EMPTY];
                                                    while (pushtos)
                                                    {
                                                        ulong tobit = pushtos & -pushtos;
                                                        pushtos ^= tobit;

                                                        add_capture(pos.pieces[pix], pbit, 4, tbit, anbit, tobit, true);
                                                    }
                                                    did_push = true;
                                                }
                                                if (!ofreezers)
                                                {
                                                    ulong pulltos = neighbors_of(perbit) & pos.bitBoards[Piece.EMPTY];
                                                    while (pulltos)
                                                    {
                                                        ulong tobit = pulltos & -pulltos;
                                                        pulltos ^= tobit;

                                                        add_capture(pos.pieces[pix], pbit, 4, tbit, perbit, tobit);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                if (!ofreezers
                                        && (neighbors_of(anbit) & (1UL << pos.lastfrom))
                                        && (pos.lastpiece > pos.pieces[anix] + enemyoffset))
                                {
                                    add_capture(pos.pieces[pix], pbit, 3 + min_clear_steps,
                                            tbit, anbit, (1UL << pos.lastfrom));
                                }
                                if (!ofreezers
                                        && (anbit & TRAPS)
                                        && popcount(neighbors_of(anbit) & pos.placement[side^1]) == 1)
                                {
                                    ulong holder = neighbors_of(anbit) & pos.placement[side^1];
                                    Piece hpiece = pos.pieces[bitindex(holder)];
                                    if (neighbors_of(holder) & (1UL << pos.lastfrom))
                                    {
                                        if (pos.lastpiece > hpiece + enemyoffset)
                                        {
                                            add_capture(pos.pieces[pix], pbit, 3 + min_clear_steps,
                                                    tbit, holder, (1UL << pos.lastfrom));
                                        }
                                    }
                                    bool can_push = false;
                                    ulong unfreezers = neighbors_of(holder) & pos.placement[side] & ~pos.frozen
                                        & ~pos.bitBoards[Piece.WRABBIT + pieceoffset];
                                    while (unfreezers)
                                    {
                                        ulong unfbit = unfreezers & -unfreezers;
                                        unfreezers ^= unfbit;
                                        bitix unfix = bitindex(unfbit);

                                        if (pos.pieces[unfix] > hpiece + enemyoffset)
                                        {
                                            can_push = true;
                                            ulong tobits = neighbors_of(unfbit) & pos.bitBoards[Piece.EMPTY];
                                            while (tobits)
                                            {
                                                ulong tobit = tobits & -tobits;
                                                tobits ^= tobit;
                                                add_capture(pos.pieces[pix], pbit, 4 + min_clear_steps,
                                                        tbit, unfbit, tobit);
                                            }
                                        }
                                    }
                                    if (can_push)
                                    {
                                        ulong pushtos = neighbors_of(holder) & pos.bitBoards[Piece.EMPTY];
                                        if (pos.pieces[pnix] < hpiece + enemyoffset)
                                            pushtos &= ~neighbors_of(pnbit);
                                        while (pushtos)
                                        {
                                            ulong tobit = pushtos & -pushtos;
                                            pushtos ^= tobit;
                                            add_capture(pos.pieces[pix], pbit, 4 + min_clear_steps,
                                                    tbit, holder, tobit, true);
                                        }
                                    }
                                }
                            }
                        }
                    } else if ((pnbit & ~pos.frozen) && pos.pieces[pnix] > pos.pieces[pix] + enemyoffset)
                    {
                        // Can push onto trap
                        if (min_clear_steps)
                        {
                           for (int i=0; i < num_clears; i++)
                           {
                               add_capture(pos.pieces[pix], pbit, 2 + clear_length[i], tbit, &clear_first_step[i]);
                           }
                        } else {
                            add_capture(pos.pieces[pix], pbit, 2, tbit, pbit, tbit, true);
                        }
                    } else if ((min_clear_steps == 0)
                            && (neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY])
                            && (pos.strongest[side][pnix] > pos.pieces[pix] + enemyoffset))
                    {
                        // this piece is too weak but it has a neighbor that is strong enough
                        ulong potentialsteps = neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY];
                        if (pos.pieces[pnix] == Piece.WRABBIT + pieceoffset)
                        {
                            // piece in the way is a rabbit make sure it can really move
                            if (side == Side.WHITE)
                            {
                                potentialsteps &= ~((pnbit & NOT_RANK_1) >> 8);
                            } else {
                                potentialsteps &= ~((pnbit & NOT_RANK_8) << 8);
                            }
                            if (!potentialsteps)
                            {
                                continue;
                            }
                        }

                        ulong finishers = neighbors_of(pnbit) & pos.placement[side];
                        while (finishers)
                        {
                            ulong fbit = finishers & -finishers;
                            finishers ^= fbit;
                            bitix fix = bitindex(fbit);

                            if ((pos.pieces[fix] > pos.pieces[pix] + enemyoffset)
                                    && ((pos.pieces[fix] >= pos.strongest[side^1][fix] + enemyoffset
                                            && !(fbit & TRAPS))
                                        || (neighbors_of(fbit) & pos.placement[side] & ~pnbit)))
                            {
                                // finisher can push the enemy piece and won't
                                // be frozen when the neighbor moves out of the way.
                                bool real_finish = false;
                                while (potentialsteps)
                                {
                                    ulong tobit = potentialsteps & -potentialsteps;
                                    potentialsteps ^= tobit;
                                    if ((tobit & ~TRAPS)
                                            || (pos.pieces[fix] >= pos.strongest[side^1][pnix] + enemyoffset)
                                            || (neighbors_of(tobit) & pos.placement[side] & ~pnbit))
                                    {
                                        // finisher won't be frozen once moving into the neighbor square
                                        real_finish = true;
                                        add_capture(pos.pieces[pix], pbit, 4, tbit, pnbit, tobit);
                                    }
                                }
                                if (real_finish)
                                {
                                    break; // we found a finisher no need for more
                                }
                            }
                        }
                    }
                } else if (pnbit & pos.bitBoards[Piece.EMPTY])
                {
                    ulong attackers = neighbors_of(pnbit) & pos.placement[side];
                    while (attackers)
                    {
                        ulong abit = attackers & -attackers;
                        attackers ^= abit;
                        bitix aix = bitindex(abit);

                        if (pos.pieces[aix] > pos.pieces[pix] + enemyoffset)
                        {
                            if (abit & ~pos.frozen)
                            {
                                if (((pnbit & TRAPS) || pos.pieces[aix] < pos.strongest[side^1][pnix] + enemyoffset)
                                        && !(neighbors_of(pnbit) & pos.placement[side] & ~abit))
                                {
                                    // intermediate square isn't safe can we bring in support?
                                    if (min_clear_steps)
                                    {
                                        if ((t_neighbors & neighbors_of(pnbit) & (pos.bitBoards[Piece.EMPTY] | abit))
                                                && (min_clear_steps == 1
                                                    || (abit & t_neighbors)))
                                        {
                                            if (tbit & pos.bitBoards[Piece.WRABBIT + pieceoffset])
                                            {
                                                ulong backward = (side == Side.WHITE) ? tbit >> 8 : tbit << 8;
                                                if (backward & (t_neighbors & neighbors_of(pnbit)
                                                            & (pos.bitBoards[Piece.EMPTY] | abit)))
                                                    continue;
                                            }
                                            add_capture(pos.pieces[pix], pbit, 4, tbit, abit, pnbit);
                                        }
                                        continue;
                                    }

                                    bool ab_first = false;
                                    ulong supporters = neighbors_of(neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY])
                                        & pos.placement[side] & ~pos.frozen;
                                    while (supporters)
                                    {
                                        ulong sbit = supporters & -supporters;
                                        supporters ^= sbit;

                                        ulong tobits = neighbors_of(sbit) & neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY];
                                        if (pos.bitBoards[Piece.WRABBIT + pieceoffset] & sbit)
                                        {
                                            ulong backward = (side == Side.WHITE) ? sbit >> 8 : sbit << 8;
                                            tobits &= ~backward;
                                        }
                                        if ((sbit & neighbors_of(abit))
                                                && !(neighbors_of(abit) & pos.placement[side] & ~sbit)
                                                && ((abit & TRAPS)
                                                    || pos.pieces[aix] < pos.strongest[side^1][aix] + enemyoffset))
                                        {
                                            bitix six = bitindex(sbit);
                                            if (tobits && (neighbors_of(sbit) & pos.placement[side] & ~abit
                                                        || ((sbit & ~TRAPS)
                                                            && pos.pieces[six] >= pos.strongest[side^1][six] + enemyoffset)))
                                            {
                                                ab_first = true;
                                            }
                                            continue;
                                        }
                                        if (tobits & (TRAPS & ~neighbors_of(pos.placement[side] & ~sbit)))
                                        {
                                            tobits &= ~(TRAPS & ~neighbors_of(pos.placement[side] & ~sbit));
                                            ab_first = true;
                                        }
                                        while (tobits)
                                        {
                                            ulong tobit = tobits & -tobits;
                                            tobits ^= tobit;

                                            add_capture(pos.pieces[pix], pbit, 4, tbit, sbit, tobit);
                                        }
                                    }
                                    if (ab_first && (pnbit & ~(TRAPS & ~neighbors_of(pos.placement[side] & ~abit))))
                                    {
                                        add_capture(pos.pieces[pix], pbit, 4, tbit, abit, pnbit);
                                    }
                                    // how about a piece neighboring the attacker
                                    if (pnbit & ~TRAPS)
                                    {
                                        supporters = neighbors_of(abit) & pos.placement[side];
                                        while (supporters)
                                        {
                                            ulong sbit = supporters & -supporters;
                                            supporters ^= sbit;
                                            bitix six = bitindex(sbit);

                                            if (!(neighbors_of(sbit) & pos.placement[side] & ~abit)
                                                    && (pos.pieces[six] < pos.strongest[side^1][six] + enemyoffset))
                                                continue;
                                            if (pos.pieces[six] == Piece.WRABBIT + pieceoffset)
                                            {
                                                ulong backward = (side == Side.WHITE) ? sbit >> 8 : sbit << 8;
                                                if (backward == abit)
                                                    continue;
                                            }
                                            add_capture(pos.pieces[pix], pbit, 4, tbit, abit, pnbit);
                                            break;
                                        }
                                    }

                                    // maybe the freezing piece is on a trap and we can capture it.
                                    ulong trap_freezer = neighbors_of(pnbit) & pos.placement[side^1] & TRAPS;
                                    ulong holder = neighbors_of(trap_freezer) & pos.placement[side^1];
                                    if (trap_freezer && popcount(holder) == 1 && (neighbors_of(abit) & holder))
                                    {
                                        Piece hpiece = pos.pieces[bitindex(holder)];
                                        ulong ofreezers = neighbors_of(pnbit) & pos.placement[side^1] & ~trap_freezer
                                            & ~pos.bitBoards[Piece.WRABBIT + pieceoffset - enemyoffset]
                                            & ~pos.bitBoards[Piece.WCAT + pieceoffset - enemyoffset];
                                        while (ofreezers)
                                        {
                                            ulong ofbit = ofreezers & -ofreezers;
                                            Piece ofpiece = pos.pieces[bitindex(ofbit)];
                                            if (pos.pieces[aix] < ofpiece + enemyoffset)
                                                break;
                                            ofreezers ^= ofbit;
                                        }
                                        if (!ofreezers && pos.pieces[aix] > hpiece + enemyoffset)
                                        {
                                            add_capture(pos.pieces[pix], pbit, 4, tbit, abit, pnbit);
                                        }
                                    }
                                } else {
                                    switch (min_clear_steps)
                                    {
                                        case 0:
                                            add_capture(pos.pieces[pix], pbit, 3, tbit, abit, pnbit);
                                            break;
                                        case 1:
                                            if (!(abit & t_neighbors)
                                                    || (neighbors_of(abit) & pos.placement[side] & ~tbit)
                                                    || pos.pieces[aix] >= pos.strongest[side^1][aix] + enemyoffset)
                                            {
                                                for (int i=0; i < num_clears; i++)
                                                {
                                                    add_capture(pos.pieces[pix], pbit, 3 + clear_length[i], tbit, &clear_first_step[i]);
                                                }
                                            }
                                            else if (t_neighbors & pos.placement[side] & ~abit)
                                            {
                                                add_capture(pos.pieces[pix], pbit, 4, tbit, abit, pnbit);
                                            }
                                            break;
                                        case 2:
                                            if (abit & t_neighbors)
                                            {
                                                for (int i=0; i < num_clears; i++)
                                                {
                                                    if (clear_first_step[i].frombit == abit
                                                            && clear_first_step[i].tobit == pnbit)
                                                    {
                                                        add_capture(pos.pieces[pix], pbit, 4, tbit, &clear_first_step[i]);
                                                        break;
                                                    }
                                                }
                                            }
                                            break;
                                        default:
                                    }
                                    if (!(t_neighbors & pos.placement[side] & ~abit))
                                    {
                                        add_capture(pos.pieces[pix], pbit, 3, tbit, abit, pnbit);
                                    }
                                }
                            }
                            else if (!(((pnbit & TRAPS)
                                        || (pos.pieces[aix] < pos.strongest[side^1][pnix] + enemyoffset))
                                    && !(neighbors_of(pnbit) & pos.placement[side] & ~abit))
                                    && (min_clear_steps == 0 || (popcount(t_neighbors & pos.placement[side]) == 1
                                            && (t_neighbors & pos.placement[side]
                                                & neighbors_of(neighbors_of(abit) & pos.bitBoards[Piece.EMPTY])
                                                & ~pos.frozen))))
                            {
                                // attacker is frozen, intermediate space is safe
                                ulong supporters = neighbors_of(neighbors_of(abit) & pos.bitBoards[Piece.EMPTY] & ~pnbit)
                                    & pos.placement[side] & ~pos.frozen & ~abit;
                                if ((pnbit & TRAPS
                                            || pos.pieces[aix] < pos.strongest[side^1][pnix] + enemyoffset)
                                        && popcount(neighbors_of(pnbit) & pos.placement[side] & ~abit) == 1)
                                    supporters &= ~neighbors_of(pnbit);
                                if (min_clear_steps)
                                    supporters &= t_neighbors;
                                while (supporters)
                                {
                                    ulong sbit = supporters & -supporters;
                                    supporters ^= sbit;
                                    bitix six = bitindex(sbit);

                                    ulong tobits = neighbors_of(sbit) & neighbors_of(abit)
                                        & pos.bitBoards[Piece.EMPTY] & ~pnbit;
                                    if (pos.pieces[six] == Piece.WRABBIT + pieceoffset)
                                    {
                                        ulong rabbitsteps = neighbors_of(sbit);
                                        if (side == Side.WHITE)
                                        {
                                            rabbitsteps &= ~((sbit & NOT_RANK_1) >> 8);
                                        } else {
                                            rabbitsteps &= ~((sbit & NOT_RANK_8) << 8);
                                        }
                                        tobits &= rabbitsteps;
                                    }
                                    while (tobits)
                                    {
                                        ulong tobit = tobits & -tobits;
                                        tobits ^= tobit;

                                        int cap_length = 4;
                                        if ((tobit & tbit) && !(t_neighbors & pos.bitBoards[Piece.EMPTY]))
                                            cap_length = 5;
                                        add_capture(pos.pieces[pix], pbit, cap_length, tbit, sbit, tobit);
                                    }
                                }
                            }
                        }
                    }

                    if (min_clear_steps == 0)
                    {
                        attackers = neighbors_of(neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY])
                            & pos.placement[side] & ~pos.frozen;
                        while (attackers)
                        {
                            ulong abit = attackers & -attackers;
                            attackers ^= abit;
                            bitix aix = bitindex(abit);

                            if ((pos.pieces[aix] > pos.pieces[pix] + enemyoffset)
                                    && (((pos.pieces[aix] >= pos.strongest[side^1][pnix] + enemyoffset)
                                            && (pnbit & ~TRAPS))
                                        || (neighbors_of(pnbit) & pos.placement[side])))
                            {
                                ulong safety = neighbors_of(pnbit) & neighbors_of(abit) & pos.placement[side]
                                        & (TRAPS & ~neighbors_of(pos.placement[side] & ~abit));
                                if (safety && ~(neighbors_of(pnbit) & pos.placement[side] & ~safety)
                                        && pos.pieces[aix] < pos.strongest[side^1][pnix] + enemyoffset)
                                    continue;

                                ulong tobits = neighbors_of(abit) & neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY];
                                while (tobits)
                                {
                                    ulong tobit = tobits & -tobits;
                                    tobits ^= tobit;
                                    bitix toix = bitindex(tobit);
                                    if (((pos.pieces[aix] >= pos.strongest[side^1][toix] + enemyoffset)
                                            && !(tobit & TRAPS))
                                        || (neighbors_of(tobit) & pos.placement[side] & ~abit))
                                    {
                                        add_capture(pos.pieces[pix], pbit, 4, tbit, abit, tobit);
                                    }
                                }
                            }
                        }
                    }
                } else if ((neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY])
                        && (pos.strongest[side][pnix] > pos.pieces[pnix] + enemyoffset)
                        && (pos.strongest[side][pnix] > pos.pieces[pix]+ enemyoffset)
                        && (min_clear_steps == 0))
                {
                    // pnbit occupied by enemy piece
                    ulong attackers = neighbors_of(pnbit) & pos.placement[side] & ~pos.frozen;
                    while (attackers)
                    {
                        ulong abit = attackers & -attackers;
                        attackers ^= abit;
                        bitix aix = bitindex(abit);

                        if ((pos.pieces[aix] > pos.pieces[pnix] + enemyoffset)
                                && (pos.pieces[aix] > pos.pieces[pix] + enemyoffset))
                        {
                            if (!(neighbors_of(pnbit) & pos.placement[side] & ~abit)
                                    && pos.pieces[aix] < pos.strongest[side^1][pnix] + enemyoffset)
                            {
                                // attacker will freeze unless freezer is trapped by first step
                                ulong freezers = neighbors_of(pnbit) & pos.placement[side^1];
                                if (!(freezers & (TRAPS & ~neighbors_of(pos.placement[side^1] & ~pnbit))))
                                    continue;
                                freezers &= ~(TRAPS & ~neighbors_of(pos.placement[side^1] & ~pnbit));
                                while (freezers)
                                {
                                    ulong fbit = freezers & -freezers;
                                    bitix fix = bitindex(fbit);
                                    if (pos.pieces[aix] < pos.pieces[fix] + enemyoffset)
                                        break;
                                    freezers ^= fbit;
                                }
                                if (freezers)
                                    continue;
                            }

                            // attacker can finish it
                            ulong tobits = neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY] & ~neighbors_of(tbit);
                            while (tobits)
                            {
                                ulong tobit = tobits & -tobits;
                                tobits ^= tobit;
                                add_capture(pos.pieces[pix], pbit, 4, tbit, pnbit, tobit, true);
                                attackers = 0UL;
                            }
                        }
                    }
                }
            }
        }
    }

    private void gen_2n(ulong tbit)
    {
        int enemyoffset = -6;
        int pieceoffset = 0;
        if (side == Side.BLACK)
        {
            enemyoffset = 6;
            pieceoffset = 6;
        }
        ulong[2] pbit;
        pbit[0] = neighbors_of(tbit) & pos.placement[side^1];
        pbit[1] = pbit[0] & -pbit[0];
        pbit[0] ^= pbit[1];
        bitix[2] pix;
        pix[0] = bitindex(pbit[0]);
        pix[1] = bitindex(pbit[1]);
        ulong[2] neighbors;
        neighbors[0] = neighbors_of(pbit[0]);
        neighbors[1] = neighbors_of(pbit[1]);

        assert (popcount(pbit[0]) == 1);
        assert (popcount(pbit[1]) == 1);

        if (side == pos.side)
        {
            if ((neighbors[0] & (1UL << pos.lastfrom))
                    && (pos.lastpiece > pos.pieces[pix[0]] + enemyoffset)
                    && (pos.strongest[side][pix[1]] > pos.pieces[pix[1]] + enemyoffset))
                gen_2n_pull(tbit, pbit[0], pbit[1]);
            if ((neighbors[1] & (1UL << pos.lastfrom))
                    && (pos.lastpiece > pos.pieces[pix[1]] + enemyoffset)
                    && (pos.strongest[side][pix[0]] > pos.pieces[pix[0]] + enemyoffset))
                gen_2n_pull(tbit, pbit[1], pbit[0]);
        }

        if ((pos.strongest[side][pix[0]] > pos.pieces[pix[0]] + enemyoffset)
                && (pos.strongest[side][pix[1]] > pos.pieces[pix[1]] + enemyoffset)
                && ((neighbors[0] & pos.placement[side] & ~pos.frozen)
                    || (neighbors[1] & pos.placement[side] & ~pos.frozen)))
        {
            ulong[2] attackers;
            for (int i=0; i < 2; i++)
            {
                ulong ppiece = pos.pieces[pix[i]] + enemyoffset;
                attackers[i] = 0;
                ulong posattackers = neighbors[i] & pos.placement[side]
                    & ~pos.bitBoards[Piece.WRABBIT + pieceoffset];
                while (posattackers)
                {
                    ulong pabit = posattackers & -posattackers;
                    posattackers ^= pabit;
                    bitix paix = bitindex(pabit);
                    if (pos.pieces[paix] > ppiece)
                    {
                        attackers[i] |= pabit;
                    }
                }
                if (!attackers[i])
                    return;
            }
            if (tbit & pos.placement[side] & ~(attackers[0] | attackers[1]))
                return;

            gen_2n_1p(tbit, pbit[0], pbit[1], attackers[0], attackers[1]);
            gen_2n_1p(tbit, pbit[1], pbit[0], attackers[1], attackers[0]);
        }
    }

    private void gen_2n_1p(ulong tbit, ulong p1bit, ulong p2bit,
            ulong p1attackers, ulong p2attackers)
    {
        int enemyoffset = -6;
        int pieceoffset = 0;
        if (side == Side.BLACK)
        {
            enemyoffset = 6;
            pieceoffset = 6;
        }
        bitix p1ix = bitindex(p1bit);
        bitix p2ix = bitindex(p2bit);
        Piece p1piece = pos.pieces[p1ix];
        Piece p2piece = pos.pieces[p2ix];
        ulong p1neighbors = neighbors_of(p1bit);
        ulong p2neighbors = neighbors_of(p2bit);

        p1attackers &= ~pos.frozen;
        if (tbit & p1attackers & ~p2attackers)
            p1attackers = tbit;
        if (p2attackers == (p2attackers & -p2attackers))
            p1attackers &= ~p2attackers;
        // is the only unfrozen p1 attacker also the only p2 attacker
        if (!p1attackers
                || ((p1attackers == (p1attackers & -p1attackers))
                    && !(p2attackers & ~p1attackers)))
            return;

        if (p1attackers == (p1attackers & -p1attackers))
            p2attackers &= ~p1attackers;
        ulong p2rattackers = p2attackers & (~pos.frozen | p1neighbors);
        ulong p2pushto = p2neighbors & pos.bitBoards[Piece.EMPTY] & ~tbit;
        ulong p2pullto = neighbors_of(p2rattackers) & pos.bitBoards[Piece.EMPTY];

        if (((tbit & pos.bitBoards[Piece.EMPTY]) && p2rattackers)
                || ((tbit & p2attackers) && (neighbors_of(tbit) & pos.bitBoards[Piece.EMPTY]))
                || ((tbit & p1attackers) && ((p2rattackers | (p1neighbors & p2attackers)) & ~tbit)))
        {
            ulong pushtos = p1neighbors & pos.bitBoards[Piece.EMPTY] & ~tbit;
            while (pushtos)
            {
                ulong tobit = pushtos & -pushtos;
                pushtos ^= tobit;
                add_capture(p2piece, p2bit, 4, tbit, p1bit, tobit, true);
            }
        }
        else if ((tbit & pos.placement[side^1])
                && p2rattackers && (p2pushto || p2pullto
                    || ((p2neighbors & p1attackers)
                        && (p2rattackers & ~p1neighbors))))
        {
            Piece tpiece = pos.pieces[bitindex(tbit)];
            ulong pushtos = p1neighbors & pos.bitBoards[Piece.EMPTY];
            if (popcount(p2pushto | p2pullto) == 1)
                pushtos &= ~p2pushto;
            while (pushtos)
            {
                ulong tobit = pushtos & -pushtos;
                pushtos ^= tobit;
                add_capture(tpiece, tbit, 4, tbit, p1bit, tobit, true);
            }
        }
        p2pullto = neighbors_of(p2attackers & ~pos.frozen) & pos.bitBoards[Piece.EMPTY];
        if ((tbit & pos.bitBoards[Piece.EMPTY])     // trap is empty
                && ((!(p1neighbors & pos.bitBoards[Piece.EMPTY] & ~tbit) // no empty space by p1
                        && p2rattackers
                        && ((p2pushto | p2pullto)   // p2 to square or p1 attacker can open space
                            || ((p2neighbors & p1attackers)
                                && (p2rattackers & ~p1attackers & ~pos.frozen)))) // p2 attacker after space is open
                    || ((p1attackers & ~p2neighbors) // none of the unfrozen p2 attackers can push or pull
                        && (neighbors_of(p2attackers & p1neighbors)
                            & pos.bitBoards[Piece.EMPTY])
                        && !(p2pushto || p2pullto))
                    || (!(p2rattackers & ~pos.frozen) // no unfrozen p2 attacker until p1 is pushed away
                        && (p2attackers & p1neighbors)
                        && (p2pushto
                            || (neighbors_of(p2attackers & p1neighbors)
                                & pos.bitBoards[Piece.EMPTY])))
                    || ((p2rattackers & ~p1neighbors) // no place to put p2 until p1 is out of the way
                        && (p2neighbors & p1attackers)
                        && !p2pushto && !p2pullto)))
        {
            add_capture(p1piece, p1bit, 4, tbit, p1bit, tbit, true);
        }
        p2rattackers = p2attackers & ~pos.frozen;
        if ((p2attackers & p1neighbors)
                && p1piece > p2piece)
        {
            // check to see if any p2attackers unfreeze
            ulong posattackers = p2attackers & p1neighbors;
            while (posattackers)
            {
                ulong pabit = posattackers & -posattackers;
                posattackers ^= pabit;
                Piece papiece = cast(Piece)(pos.pieces[bitindex(pabit)]);

                ulong posfreezers = neighbors_of(pabit) & pos.placement[side^1] & ~p1bit
                    & ~pos.bitBoards[Piece.WRABBIT + pieceoffset - enemyoffset]
                    & ~pos.bitBoards[Piece.WCAT + pieceoffset - enemyoffset];
                while (posfreezers)
                {
                    ulong pfbit = posfreezers & -posfreezers;
                    bitix pfix = bitindex(pfbit);
                    if (papiece < pos.pieces[pfix] + enemyoffset)
                        break;
                    posfreezers ^= pfbit;
                }
                if (!posfreezers)
                    p2rattackers |= pabit;
            }
        }
        ulong p2to = p2neighbors & pos.bitBoards[Piece.EMPTY];
        if (!(p2to || (neighbors_of(p2attackers) & (pos.bitBoards[Piece.EMPTY] | p1bit))))
            return;
        if ((tbit & p1attackers)
                && (neighbors_of(tbit) & pos.bitBoards[Piece.EMPTY])
                && (!(p2to || (neighbors_of(p2rattackers & ~tbit) & pos.bitBoards[Piece.EMPTY]))
                    || !(p2rattackers & ~pos.frozen))
                && ((neighbors_of(p2rattackers & ~tbit) & p1bit)
                    || (neighbors_of(p2attackers & ~tbit) & neighbors_of(tbit)
                        & pos.bitBoards[Piece.EMPTY])))
        {
            ulong tobit = neighbors_of(tbit) & pos.bitBoards[Piece.EMPTY];
            assert (popcount(tobit) == 1);
            if (p2to || (neighbors_of(p2rattackers & ~tbit)
                        & (pos.bitBoards[Piece.EMPTY] | p1bit) & ~tobit)
                || (neighbors_of(tobit) & (p2attackers & ~tbit)
                    & neighbors_of((pos.bitBoards[Piece.EMPTY] | p1bit)
                        & ~tobit)))
            {
                add_capture(p1piece, p1bit, 4, tbit, tbit, tobit);
            }
        }
        if (!(tbit & p1attackers & ~p2attackers))
        {
            p1attackers &= ~tbit;
            Piece tpiece;
            ulong capbit;
            if ((tbit & p2attackers) || (tbit & pos.bitBoards[Piece.EMPTY]))
            {
                tpiece = p2piece;
                capbit = p2bit;
            } else {
                assert (tbit & pos.placement[side^1]);
                tpiece = pos.pieces[bitindex(tbit)];
                capbit = tbit;
            }
            while (p1attackers)
            {
                ulong abit = p1attackers & -p1attackers;
                p1attackers ^= abit;

                if (!(p2to | (neighbors_of(p2attackers & ~abit) & (pos.bitBoards[Piece.EMPTY] | p1bit))))
                    continue;

                ulong pulls = neighbors_of(abit) & pos.bitBoards[Piece.EMPTY];
                if (!(p2rattackers & ~abit) || (!(p2to
                                || (neighbors_of(p2rattackers & ~abit)
                                    & (pos.bitBoards[Piece.EMPTY] | p1bit)))))
                {
                    pulls &= neighbors_of(p2attackers & ~abit);
                }
                while (pulls)
                {
                    ulong pbit = pulls & -pulls;
                    pulls ^= pbit;
                    if (!(p2to & ~pbit) && !((neighbors_of(neighbors_of(pbit) & p2attackers & ~abit)
                                    & (pos.bitBoards[Piece.EMPTY] | p1bit) & ~pbit)
                                || (neighbors_of(p2rattackers & ~abit)
                                    & (pos.bitBoards[Piece.EMPTY] | p1bit) & ~pbit)))
                        continue;
                    add_capture(tpiece, capbit, 4, tbit, abit, pbit);
                }
            }
        }
    }

    private void gen_2n_pull(ulong tbit, ulong p1bit, ulong p2bit)
    {
        ulong p1tobit = 1UL << pos.lastfrom;
        Side side = pos.side;
        int enemyoffset = -6;
        int pieceoffset = 0;
        if (side == Side.BLACK)
        {
            enemyoffset = 6;
            pieceoffset = 6;
        }
        ulong p1ix = bitindex(p1bit);
        ulong p2ix = bitindex(p2bit);
        Piece p1piece = pos.pieces[p1ix];
        Piece p2piece = pos.pieces[p2ix];
        ulong p1neighbors = neighbors_of(p1bit);
        ulong p2neighbors = neighbors_of(p2bit);

        ulong attackers = 0;
        ulong posattackers = p2neighbors & pos.placement[side] & (~pos.frozen | p1neighbors);
        if (tbit & pos.placement[side])
            posattackers = tbit;
        while (posattackers)
        {
            ulong abit = posattackers & -posattackers;
            posattackers ^= abit;
            Piece apiece = pos.pieces[bitindex(abit)];
            if (abit & pos.frozen)
            {
                ulong freezers = neighbors_of(abit) & pos.placement[side^1] & ~p1bit & ~p2bit
                    & ~pos.bitBoards[Piece.WRABBIT + pieceoffset - enemyoffset]
                    & ~pos.bitBoards[Piece.WCAT + pieceoffset - enemyoffset];
                while (freezers)
                {
                    ulong fbit = freezers & -freezers;
                    Piece fpiece = pos.pieces[bitindex(fbit)];
                    if (apiece < fpiece + enemyoffset)
                        break;
                    freezers ^= fbit;
                }
                if (freezers)
                {
                    continue;
                }
            }
            if (apiece > p2piece + enemyoffset)
                attackers |= abit;
        }
        if (!attackers)
            return;

        ulong postos = neighbors_of(attackers);
        if (attackers != tbit)
            postos |= neighbors_of(p2bit);
        if (!(postos & (pos.bitBoards[Piece.EMPTY] | p1bit) & ~p1tobit))
            return;
        if (tbit == p1tobit)
        {
            add_capture(p1piece, p1bit, 3, tbit, p1bit, p1tobit);
        }
        else if (tbit & pos.placement[side^1])
        {
            add_capture(pos.pieces[bitindex(tbit)], tbit, 3, tbit, p1bit, p1tobit);
        }
        else
        {
            add_capture(p2piece, p2bit, 3, tbit, p1bit, p1tobit);
        }
    }

    int find_captures(Position p, Side s)
    {
        pos = p;
        side = s;
        num_captures = 0;

        ulong trapbits = TRAPS;
        while (trapbits)
        {
            ulong tbit = trapbits & -trapbits;
            trapbits ^= tbit;

            switch (popcount(neighbors_of(tbit) & pos.placement[side^1]))
            {
                case 0:
                    gen_0n(tbit);
                    break;
                case 1:
                    gen_1n(tbit);
                    break;
                case 2:
                    gen_2n(tbit);
                    break;
                default:
                    break;
            }
        }

        for (int i=1; i < num_captures; i++)
        {
            CaptureInfo value = captures[i];
            int j = i-1;
            while (j >= 0 && (captures[j].victim < value.victim
                                    || (captures[j].victim == value.victim
                                            && captures[j].length > value.length)))
            {
                captures[j+1] = captures[j];
                j--;
            }
            captures[j+1] = value;
        }

        return num_captures;
    }
}

