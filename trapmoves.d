
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

    void add_capture(Piece piece, ulong vbit, int steps, ulong tbit, ulong frombit, ulong tobit, bool ispush=false)
    in
    {
        assert (tbit & TRAPS, "trap_bit not a trap");
        assert (popcount(tbit) == 1, "more than one trap in trap_bit");
    }
    body
    {
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
        captures[num_captures].victim = piece;
        captures[num_captures].victim_bit = vbit;
        captures[num_captures].length = steps;
        captures[num_captures].trap_bit = tbit;
        captures[num_captures].first_step = *step;
        num_captures++;
    }

    private void gen_0n(Position pos, ulong tbit, Side side, bool findall)
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
                                        if (!findall)
                                            return;
                                        tobits_handled = true;
                                    }
                                    if (!(t_neighbors & ~nbit & pos.placement[side]))
                                    {
                                        add_capture(pos.pieces[pix], pbit, 4, tbit, nbit, tbit);
                                        if (!findall)
                                            return;
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
                                        if (!findall)
                                            return;
                                        break;
                                    }
                                }
                            }

                            if ((t_neighbors & pos.bitBoards[Piece.EMPTY])
                                    && (t_neighbors & ~nbit & pos.placement[side]))
                            {
                                add_capture(pos.pieces[pix], pbit, 4, tbit, nbit, tbit);
                                if (!findall)
                                    return;
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
                                    if (!findall)
                                        return;
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
                                    if (!findall)
                                        return;
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

                                        if (pos.pieces[fix] > pos.pieces[pix] + enemyoffset)
                                        {
                                            // can finish trap
                                            add_capture(pos.pieces[pix], pbit, 4, tbit, pbit, nbit, true);
                                            if (!findall)
                                                return;
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
                                            if (!findall)
                                                return;
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
                            && (pos.pieces[tix] > pos.pieces[pix] + enemyoffset))
                    {
                        add_capture(pos.pieces[pix], pbit, 3, tbit, pbit, lastbit);
                        if (!findall)
                            return;
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
                                    if (!findall)
                                        return;
                                }
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
                // do we have someplace safe to move to?
                ulong pempties = at_neighbors & pos.bitBoards[Piece.EMPTY];
                ulong empties = 0;
                while (pempties)
                {
                    ulong empty = pempties & -pempties;
                    pempties ^= empty;
                    bitix eix = bitindex(empty);
                    if (at_piece >= pos.strongest[side^1][eix] + enemyoffset)
                        empties |= empty;
                }

                ulong possibles = at_neighbors & pos.placement[side^1];
                while (possibles)
                {
                    ulong pbit = possibles & -possibles;
                    possibles ^= pbit;
                    bitix pix = bitindex(pbit);

                    if (at_piece > pos.pieces[pix] + enemyoffset)
                    {
                        ulong tobits = empties;
                        while (tobits)
                        {
                            ulong tobit = tobits & -tobits;
                            tobits ^= tobit;
                            add_capture(pos.pieces[pix], pbit, 4, tbit, atbit, tobit);
                            if (!findall)
                                return;
                        }
                        ulong ptobit = neighbors_of(pbit) & t_neighbors & pos.bitBoards[Piece.EMPTY];
                        if (ptobit)
                        {
                            add_capture(pos.pieces[pix], pbit, 4, tbit, pbit, ptobit, true);
                            if (!findall)
                                return;
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
                                if (!findall)
                                    return;
                            }
                            ulong ptobit = neighbors_of(pbit) & t_neighbors & pos.bitBoards[Piece.EMPTY];
                            if (ptobit)
                            {
                                add_capture(pos.pieces[pix], pbit, 4, tbit, pbit, ptobit, true);
                                if (!findall)
                                    return;
                            }
                        }
                    }
                }
            }
        }
    }

    private void gen_1n(Position pos, ulong tbit, Side side, bool findall)
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
                if (!findall)
                    return;
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
                                if (!findall)
                                    return;
                            }
                            ulong pulltos = neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY];
                            while (pulltos)
                            {
                                ulong tobit = pulltos & -pulltos;
                                pulltos ^= tobit;

                                add_capture(pos.pieces[tix], tbit, 2, tbit, pnbit, tobit);
                                if (!findall)
                                    return;
                            }

                            ulong clear = neighbors_of(pbit) & pos.placement[side];
                            while (clear)
                            {
                                ulong cbit = clear & -clear;
                                clear ^= cbit;

                                ulong pobits = neighbors_of(cbit);
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
                                        && pos.pieces[cix] < pos.strongest[side^1][cix];
                                    while (pobits)
                                    {
                                        ulong pobit = pobits & -pobits;
                                        pobits ^= pobit;

                                        if (pobit & pos.bitBoards[Piece.EMPTY])
                                        {
                                            add_capture(pos.pieces[tix], tbit, 3, tbit, cbit, pobit);
                                            if (!findall)
                                                return;
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
                                                if (!findall)
                                                    return;
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
                                                    if (!findall)
                                                        return;
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
                                    ulong forward = (side == Side.WHITE) ? cbit << 8 : cbit >> 8;
                                    while (ebits)
                                    {
                                        ulong empty = ebits & -ebits;
                                        ebits ^= empty;

                                        ulong unfreezers = neighbors_of(empty) & pos.placement[side]
                                            & ~pos.frozen & ~(pos.bitBoards[Piece.WRABBIT + pieceoffset]
                                                    & neighbors_of(forward));
                                        while (unfreezers)
                                        {
                                            ulong unbit = unfreezers & -unfreezers;
                                            unfreezers ^= unbit;
                                            add_capture(pos.pieces[tix], tbit, 4, tbit, unbit, empty);
                                            if (!findall)
                                                return;
                                        }
                                    }
                                }
                            }

                            clear = neighbors_of(pnbit) & pos.placement[side];
                            if (pos.pieces[pnix] >= pos.strongest[side^1][pnix] + enemyoffset
                                    || (clear != (clear & -clear)))
                            {
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
                                            if (!findall)
                                                return;
                                        }
                                        else if (pobit & pos.placement[side])
                                        {
                                            ulong empties = neighbors_of(pobit) & pos.bitBoards[Piece.EMPTY];
                                            while (empties)
                                            {
                                                ulong tobit = empties & -empties;
                                                empties ^= tobit;
                                                add_capture(pos.pieces[tix], tbit, 4, tbit, pobit, tobit);
                                                if (!findall)
                                                    return;
                                            }
                                        } else {
                                            // pobit must be opponent peice
                                            assert (pobit & pos.placement[side^1]);
                                            bitix poix = bitindex(pobit);
                                            if (pos.pieces[cix] > pos.pieces[poix] + enemyoffset)
                                            {
                                                ulong tobits = neighbors_of(pobit)
                                                    & pos.bitBoards[Piece.EMPTY] & ~t_neighbors;
                                                while (tobits)
                                                {
                                                    ulong tobit = tobits & -tobits;
                                                    tobits ^= tobit;
                                                    add_capture(pos.pieces[tix], tbit, 4, tbit, pobit, tobit, true);
                                                    if (!findall)
                                                        return;
                                                }
                                            }
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
                                            if (!findall)
                                                return;
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
                        // pn is frozen can we unfreeze in two steps or less
                        ulong pn_neighbors = neighbors_of(pnbit) & ~pbit;
                        while (pn_neighbors)
                        {
                            ulong pnnbit = pn_neighbors & -pn_neighbors;
                            pn_neighbors ^= pnnbit;

                            if (pnnbit & pos.bitBoards[Piece.EMPTY])
                            {
                                ulong pnn_neighbors = neighbors_of(pnnbit) & ~pos.placement[side^1];
                                while (pnn_neighbors)
                                {
                                    ulong pnnnbit = pnn_neighbors & -pnn_neighbors;
                                    pnn_neighbors ^= pnnnbit;
                                    bitix pnnnix = bitindex(pnnnbit);

                                    if (pnnnbit & pos.bitBoards[Piece.EMPTY])
                                    {
                                        ulong unfreezers = neighbors_of(pnnnbit) & pos.placement[side] & ~pos.frozen;
                                        while (unfreezers)
                                        {
                                            ulong unbit = unfreezers & -unfreezers;
                                            unfreezers ^= unbit;
                                            bitix unix = bitindex(unbit);

                                            if ((pos.placement[side] & neighbors_of(pnnnbit) & ~unbit)
                                                    || !((pnnnbit & TRAPS)
                                                        || (pos.pieces[unix] >= pos.strongest[side^1][pnnnix] + enemyoffset)))
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
                                                if (!findall)
                                                    return;
                                            }
                                        }
                                    } else {
                                        // pnnn must have a friendly piece on it

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
                                            // can we unfreeze in one step
                                            ulong unfreezers = neighbors_of(neighbors_of(pnnbit) & pos.bitBoards[Piece.EMPTY])
                                                & pos.placement[side] & ~pos.frozen;
                                            while (unfreezers)
                                            {
                                                ulong unbit = unfreezers & -unfreezers;
                                                unfreezers ^= unbit;
                                                bitix unix = bitindex(unbit);

                                                ulong tobits = neighbors_of(unbit) & neighbors_of(pnnbit) & pos.bitBoards[Piece.EMPTY];
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
                                                    if (!findall)
                                                        return;
                                                }
                                            }
                                        } else {
                                            add_capture(pos.pieces[tix], tbit, 3, tbit, pnnnbit, pnnbit);
                                            if (!findall)
                                                return;
                                        }
                                    }
                                }
                            } else {
                                // pnn must have enemy piece can we push it away
                                bitix pnnix = bitindex(pnnbit);

                                ulong pushtos = neighbors_of(pnnbit) & pos.bitBoards[Piece.EMPTY];
                                if (pushtos
                                        && (pos.strongest[side][pnnix] > pos.pieces[pnnix] + enemyoffset))
                                {
                                    // we have a spot to push it to and a piece that might be able to push it
                                    ulong pushers = neighbors_of(pnnbit) & pos.placement[side] & ~pos.frozen;
                                    while (pushers)
                                    {
                                        ulong perbit = pushers & -pushers;
                                        pushers ^= perbit;
                                        bitix perix = bitindex(perbit);

                                        if (pos.pieces[perix] > pos.pieces[pnnix] + enemyoffset)
                                        {
                                            while (pushtos)
                                            {
                                                ulong tobit = pushtos & -pushtos;
                                                pushtos ^= tobit;
                                                add_capture(pos.pieces[tix], tbit, 4, tbit, pnnbit, tobit, true);
                                                if (!findall)
                                                    return;
                                            }
                                            pushers = 0UL; // got a real pusher don't look for more
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
                                            || (pos.placement[side] & neighbors_of(pnbit)))
                                        && ((pos.placement[side] & neighbors_of(pnnbit) & ~perbit)
                                            || !((pnnbit & TRAPS)
                                                || (pos.pieces[perix] < pos.strongest[side^1][pnnix] + enemyoffset))))
                                {
                                    add_capture(pos.pieces[tix], tbit, 4, tbit, perbit, pnnbit);
                                    if (!findall)
                                        return;
                                }
                            }
                        } else if (pos.pieces[pnnix] > pos.pieces[pix] + enemyoffset)
                        {
                            // pnn must be a friendly piece that can push pix
                            if (pnnbit & pos.frozen)
                            {
                                ulong unfreezers = neighbors_of(neighbors_of(pnnbit)
                                        & pos.bitBoards[Piece.EMPTY] & ~pnbit)
                                    & pos.placement[side] & ~pos.frozen;
                                while (unfreezers)
                                {
                                    ulong unbit = unfreezers & -unfreezers;
                                    unfreezers ^= unbit;
                                    bitix unix = bitindex(unbit);

                                    ulong tobits = neighbors_of(unbit) & neighbors_of(pnnbit) & pos.bitBoards[Piece.EMPTY];
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
                                        if (!findall)
                                            return;
                                    }
                                }
                            }
                            else if (pos.pieces[pnnix] >= pos.strongest[side^1][pnix] + enemyoffset
                                    || (neighbors_of(pnbit) & pos.placement[side] & ~pnnbit))
                            {
                                add_capture(pos.pieces[tix], tbit, 3, tbit, pnnbit, pnbit);
                                if (!findall)
                                    return;
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
                                    && (pos.pieces[perix] > pos.pieces[pix] + enemyoffset)
                                    && ((pos.pieces[perix] >= pos.strongest[side^1][pnix] + enemyoffset)
                                        || (neighbors_of(pnbit) & pos.placement[side] & ~perbit)))
                            {
                                // pusher can finish it
                                while (pushtos)
                                {
                                    ulong tobit = pushtos & -pushtos;
                                    pushtos ^= tobit;
                                    add_capture(pos.pieces[tix], tbit, 4, tbit, pnbit, tobit, true);
                                    if (!findall)
                                        return;
                                    pushers = 0UL;
                                }
                            }
                        }
                    }
                }
            }
        } else
        {
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
                                    ulong tobits = neighbors_of(tnnbit) & pos.bitBoards[Piece.EMPTY];
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
                        if (!findall)
                            return;
                    }
                    return;
                }
            }

            if ((side == pos.side) && (lastbit & tbit)
                    && (pos.lastpiece > pos.pieces[pix] + enemyoffset))
            {
                // Can finish a pull onto the trap
                add_capture(pos.pieces[pix], pbit, 1, tbit, pbit, lastbit);
                if (!findall)
                    return;
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
                                            if (!findall)
                                                return;
                                        }
                                    }
                                }
                            }
                        }
                    } else if (pnbit & pos.frozen
                            && pos.pieces[pnix] > pos.pieces[pix] + enemyoffset
                            && min_clear_steps < 2)
                    {
                        ulong aneighbors = neighbors_of(pnbit);
                        while (aneighbors)
                        {
                            ulong anbit = aneighbors & -aneighbors;
                            aneighbors ^= anbit;
                            bitix anix = bitindex(anbit);

                            if (anbit & pos.bitBoards[Piece.EMPTY])
                            {
                                ulong unfreezers = neighbors_of(anbit) & pos.placement[side];
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
                                                if (!findall)
                                                    return;
                                            }
                                        }
                                    } else if (min_clear_steps < 2)
                                    {
                                        if (min_clear_steps)
                                        {
                                            for (int i=0; i < num_clears; i++)
                                            {
                                                add_capture(pos.pieces[pix], pbit, 3 + clear_length[i], tbit, &clear_first_step[i]);

                                                if (!findall)
                                                    return;
                                            }
                                        } else {
                                            add_capture(pos.pieces[pix], pbit, 3, tbit, ufbit, anbit);
                                            if (!findall)
                                                return;
                                        }
                                    }
                                }

                                if (min_clear_steps == 0)
                                {
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

                                            if ((pos.pieces[unfix] >= pos.strongest[side^1][toix] + enemyoffset)
                                                    || (neighbors_of(tobit) & pos.placement[side] & ~unfbit))
                                            {
                                                add_capture(pos.pieces[pix], pbit, 4, tbit, unfbit, tobit);
                                                if (!findall)
                                                    return;
                                            }
                                        }
                                    }
                                }
                            } else if ((min_clear_steps == 0)
                                    && (pos.strongest[side][anix] > pos.pieces[anix] + enemyoffset)
                                    && (neighbors_of(anbit) & pos.bitBoards[Piece.EMPTY]))
                            {
                                // an is enemy piece can we push out of the way
                                ulong pushers = neighbors_of(anbit) & pos.placement[side] & ~pos.frozen;
                                while (pushers)
                                {
                                    ulong perbit = pushers & -pushers;
                                    pushers ^= perbit;
                                    bitix perix = bitindex(perbit);

                                    if (pos.pieces[perix] > pos.pieces[anix] + enemyoffset)
                                    {
                                        ulong pushtos = neighbors_of(anbit) & pos.bitBoards[Piece.EMPTY];
                                        while (pushtos)
                                        {
                                            ulong tobit = pushtos & -pushtos;
                                            pushtos ^= tobit;

                                            add_capture(pos.pieces[pix], pbit, 4, tbit, anbit, tobit, true);
                                            if (!findall)
                                                return;
                                        }
                                        break;
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
                               if (!findall)
                                   return;
                           }
                        } else {
                            add_capture(pos.pieces[pix], pbit, 2, tbit, pbit, tbit, true);
                            if (!findall)
                                return;
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
                                            || (neighbors_of(tobit) & pos.placement[side]))
                                    {
                                        // finisher won't be frozen once moving into the neighbor square
                                        real_finish = true;
                                        add_capture(pos.pieces[pix], pbit, 4, tbit, pnbit, tobit);
                                        if (!findall)
                                            return;
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
                                if (((pnbit & TRAPS)
                                            || (pos.pieces[aix] < pos.strongest[side^1][pnix] + enemyoffset))
                                        && !(neighbors_of(pnbit) & pos.placement[side] & ~abit))
                                {
                                    if (min_clear_steps)
                                        continue;

                                    // intermediate square isn't safe can we bring in support?
                                    ulong supporters = neighbors_of(neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY])
                                        & pos.placement[side] & ~pos.frozen;
                                    while (supporters)
                                    {
                                        ulong sbit = supporters & -supporters;
                                        supporters ^= sbit;

                                        ulong tobits = neighbors_of(sbit) & neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY];
                                        if (pos.bitBoards[Piece.WRABBIT + pieceoffset] & sbit)
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

                                            add_capture(pos.pieces[pix], pbit, 4, tbit, sbit, tobit);
                                            if (!findall)
                                                return;
                                        }
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
                                } else {
                                    switch (min_clear_steps)
                                    {
                                        case 0:
                                            add_capture(pos.pieces[pix], pbit, 3, tbit, abit, pnbit);
                                            if (!findall)
                                                return;
                                            break;
                                        case 1:
                                            for (int i=0; i < num_clears; i++)
                                            {
                                                add_capture(pos.pieces[pix], pbit, 3 + clear_length[i], tbit, &clear_first_step[i]);
                                                if (!findall)
                                                    return;
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
                                                        if (!findall)
                                                            return;
                                                        break;
                                                    }
                                                }
                                            }
                                            break;
                                        default:
                                    }
                                }
                            }
                            else if (!(((pnbit & TRAPS)
                                        || (pos.pieces[aix] < pos.strongest[side^1][pnix] + enemyoffset))
                                    && !(neighbors_of(pnbit) & pos.placement[side] & ~abit))
                                    && (min_clear_steps == 0))
                            {
                                // attacker is frozen, intermediate space is safe
                                ulong supporters = neighbors_of(neighbors_of(abit) & pos.bitBoards[Piece.EMPTY] & ~pnbit)
                                    & pos.placement[side] & ~pos.frozen & ~abit;
                                if ((pnbit & TRAPS
                                            || pos.pieces[aix] < pos.strongest[side^1][pnix] + enemyoffset)
                                        && popcount(neighbors_of(pnbit) & pos.placement[side] & ~abit) == 1)
                                    supporters &= ~neighbors_of(pnbit);
                                while (supporters)
                                {
                                    ulong sbit = supporters & -supporters;
                                    supporters ^= sbit;
                                    bitix six = bitindex(sbit);

                                    ulong tobits = neighbors_of(sbit) & neighbors_of(abit) & pos.bitBoards[Piece.EMPTY];
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
                                        if (!findall)
                                            return;
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
                                        if (!findall)
                                            return;
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
                                && (pos.pieces[aix] > pos.pieces[pix] + enemyoffset)
                                && ((pos.pieces[aix] >= pos.strongest[side^1][pnix] + enemyoffset)
                                    || (neighbors_of(pnbit) & pos.placement[side] & ~abit)))
                        {
                            // attacker is strong enough to push both pieces
                            // and won't be frozen after first push
                            ulong tobits = neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY] & ~neighbors_of(tbit);
                            while (tobits)
                            {
                                ulong tobit = tobits & -tobits;
                                tobits ^= tobit;

                                add_capture(pos.pieces[pix], pbit, 4, tbit, pnbit, tobit, true);
                                if (!findall)
                                    return;
                            }
                        }
                    }
                }
            }
        }
    }

    private void gen_2n(Position pos, ulong tbit, Side side, bool findall)
    {
        int enemyoffset = -6;
        int pieceoffset = 0;
        if (side == Side.BLACK)
        {
            enemyoffset = 6;
            pieceoffset = 6;
        }

        ulong p2bit = neighbors_of(tbit) & pos.placement[side^1];
        ulong p1bit = p2bit & -p2bit;
        p2bit ^= p1bit;
        bitix p1ix = bitindex(p1bit);
        bitix p2ix = bitindex(p2bit);

        ulong p1neighbors = neighbors_of(p1bit);
        ulong p2neighbors = neighbors_of(p2bit);

        if ((pos.strongest[side][p1ix] > pos.pieces[p1ix] + enemyoffset)
                && (pos.strongest[side][p2ix] > pos.pieces[p2ix] + enemyoffset)
                && ((p1neighbors & pos.placement[side] & ~pos.frozen)
                    || (p2neighbors & pos.placement[side] & ~pos.frozen)))
        {
            ulong t_neighbors = neighbors_of(tbit);
            ulong p2pushers = 0;
            ulong pospushers = p2neighbors & pos.placement[side] & ~pos.frozen;
            while (pospushers)
            {
                ulong pushbit = pospushers & -pospushers;
                pospushers ^= pushbit;
                bitix pushix = bitindex(pushbit);

                if (pos.pieces[pushix] > pos.pieces[p2ix] + enemyoffset)
                {
                    p2pushers |= pushbit;
                }
            }

            ulong p1pushers = 0;
            pospushers = p1neighbors & pos.placement[side] & ~pos.frozen;
            while (pospushers)
            {
                ulong pushbit = pospushers & -pospushers;
                pospushers ^= pushbit;
                bitix pushix = bitindex(pushbit);

                if (pos.pieces[pushix] > pos.pieces[p1ix] + enemyoffset)
                {
                    p1pushers |= pushbit;
                }
            }

            // remove pushers that have to be used for the other piece
            if (popcount(p1pushers) == 1 && (p1pushers & p2pushers))
                p2pushers ^= p1pushers;
            if (popcount(p2pushers) == 1 && (p2pushers & p1pushers))
                p1pushers ^= p2pushers;

            ulong p1frozen = 0;
            pospushers = p1neighbors & neighbors_of(neighbors_of(p2pushers)
                    & (pos.bitBoards[Piece.EMPTY] | p2bit))
                & pos.placement[side] & pos.frozen;
            while (pospushers)
            {
                ulong pushbit = pospushers & -pospushers;
                pospushers ^= pushbit;
                bitix pushix = bitindex(pushbit);
                if (pos.pieces[pushix] > pos.pieces[p1ix] + enemyoffset)
                {
                    p1frozen |= pushbit;
                }
            }
            if (!p1pushers && !p1frozen)
                return;
            ulong p2frozen = 0;
            pospushers = p2neighbors & neighbors_of(neighbors_of(p1pushers)
                    & (pos.bitBoards[Piece.EMPTY] | p1bit))
                & pos.placement[side] & pos.frozen;
            while (pospushers)
            {
                ulong pushbit = pospushers & -pospushers;
                pospushers ^= pushbit;
                bitix pushix = bitindex(pushbit);
                if (pos.pieces[pushix] > pos.pieces[p2ix] + enemyoffset)
                {
                    p2frozen |= pushbit;
                }
            }
            if (!p2pushers && !p2frozen)
                return;

            if (tbit & pos.bitBoards[Piece.EMPTY])
            {
                ulong p1n_empties = p1neighbors & pos.bitBoards[Piece.EMPTY] & ~tbit;
                ulong p2n_empties = p2neighbors & pos.bitBoards[Piece.EMPTY] & ~tbit;
                if (p1pushers && p2n_empties && (p2pushers || (p2frozen & p1neighbors)))
                {
                    add_capture(pos.pieces[p1ix], p1bit, 4, tbit, p1bit, tbit, true);
                    if (!findall)
                        return;
                }
                if (p2pushers && p1n_empties && (p1pushers || (p1frozen & p2neighbors)))
                {
                    add_capture(pos.pieces[p2ix], p2bit, 4, tbit, p2bit, tbit, true);
                    if (!findall)
                        return;
                }

                if ((p1frozen & p2neighbors) && p2pushers && p2n_empties)
                {
                    while (p2n_empties)
                    {
                        ulong tobit = p2n_empties & -p2n_empties;
                        p2n_empties ^= tobit;
                        add_capture(pos.pieces[p1ix], p1bit, 4, tbit, p2bit, tobit, true);
                        if (!findall)
                            return;
                    }
                }
                if ((p2frozen & p1neighbors) && p1pushers && p1n_empties)
                {
                    while (p1n_empties)
                    {
                        ulong tobit = p1n_empties & -p1n_empties;
                        p1n_empties ^= tobit;
                        add_capture(pos.pieces[p2ix], p2bit, 4, tbit, p1bit, tobit, true);
                        if (!findall)
                            return;
                    }
                }

                ulong pulls = neighbors_of(p2pushers) & pos.bitBoards[Piece.EMPTY];
                if (!p1pushers)
                    pulls &= neighbors_of(p1frozen);
                while (pulls)
                {
                    ulong pull = pulls & -pulls;
                    pulls ^= pull;
                    ulong pushers = neighbors_of(pull) & p2pushers;
                    while (pushers)
                    {
                        ulong pusher = pushers & -pushers;
                        pushers ^= pusher;
                        add_capture(pos.pieces[p1ix], p1bit, 4, tbit, pusher, pull);
                        if (!findall)
                            return;
                    }
                }
                pulls = neighbors_of(p1pushers) & pos.bitBoards[Piece.EMPTY];
                if (!p2pushers)
                    pulls &= neighbors_of(p2frozen);
                while (pulls)
                {
                    ulong pull = pulls & -pulls;
                    pulls ^= pull;
                    ulong pushers = neighbors_of(pull) & p1pushers;
                    while (pushers)
                    {
                        ulong pusher = pushers & -pushers;
                        pushers ^= pusher;
                        add_capture(pos.pieces[p2ix], p2bit, 4, tbit, pusher, pull);
                        if (!findall)
                            return;
                    }
                }
            }
            else if (tbit & pos.placement[side])
            {
                if (p2pushers & tbit)
                {
                    if (p2pushers || (p2frozen & neighbors_of(p1bit)))
                    {
                        ulong p2tobits = p2neighbors & pos.bitBoards[Piece.EMPTY];
                        while (p2tobits)
                        {
                            ulong tobit = p2tobits & -p2tobits;
                            p2tobits ^= tobit;
                            add_capture(pos.pieces[p1ix], p1bit, 4, tbit, p2bit, tobit, true);
                            if (!findall)
                                return;
                        }
                    }

                    ulong pullers = p1pushers & ~tbit
                        & neighbors_of(pos.bitBoards[Piece.EMPTY]);
                    while (pullers)
                    {
                        ulong pbit = pullers & -pullers;
                        pullers ^= pbit;
                        ulong pulltos = neighbors_of(pbit)
                            & pos.bitBoards[Piece.EMPTY];
                        while (pulltos)
                        {
                            ulong tobit = pulltos & -pulltos;
                            pulltos ^= tobit;
                            add_capture(pos.pieces[p2ix], p2bit, 4, tbit, pbit, tobit);
                            if (!findall)
                                return;
                        }
                    }

                    ulong empty_tn = t_neighbors & pos.bitBoards[Piece.EMPTY];
                    if (empty_tn)
                    {
                        ulong p1freezers = 0;
                        if (!p1pushers && p1frozen)
                        {
                            bitix p1frix = bitindex(p1frozen);
                            p1freezers = neighbors_of(p1frozen) & pos.placement[side^1]
                                & ~p1bit & ~p2bit;
                            while (p1freezers)
                            {
                                ulong p1f = p1freezers & -p1freezers;
                                bitix p1fix = bitindex(p1f);
                                if (pos.pieces[p1frix] < pos.pieces[p1fix] + enemyoffset)
                                    break;
                                p1freezers ^= p1f;
                            }
                        }
                        if (!p1freezers)
                        {
                            while (empty_tn)
                            {
                                ulong tobit = empty_tn & -empty_tn;
                                empty_tn ^= tobit;
                                add_capture(pos.pieces[p2ix], p2bit, 4, tbit, tbit, tobit);
                            }
                        } else {
                            empty_tn &= neighbors_of(p1frozen);
                            if (empty_tn)
                            {
                                add_capture(pos.pieces[p2ix], p2bit, 4, tbit, tbit, empty_tn);
                                if (!findall)
                                    return;
                            }
                        }
                    }
                }
                if (p1pushers & tbit)
                {
                    if (p2pushers || (p2frozen & neighbors_of(p1bit)))
                    {
                        ulong p1tobits = p1neighbors & pos.bitBoards[Piece.EMPTY];
                        while (p1tobits)
                        {
                            ulong tobit = p1tobits & -p1tobits;
                            p1tobits ^= tobit;
                            add_capture(pos.pieces[p2ix], p2bit, 4, tbit, p1bit, tobit, true);
                            if (!findall)
                                return;
                        }
                    }

                    ulong pullers = p2pushers & ~tbit
                        & neighbors_of(pos.bitBoards[Piece.EMPTY]);
                    while (pullers)
                    {
                        ulong pbit = pullers & -pullers;
                        pullers ^= pbit;
                        ulong pulltos = neighbors_of(pbit)
                            & pos.bitBoards[Piece.EMPTY];
                        while (pulltos)
                        {
                            ulong tobit = pulltos & -pulltos;
                            pulltos ^= tobit;
                            add_capture(pos.pieces[p1ix], p1bit, 4, tbit, pbit, tobit);
                            if (!findall)
                                return;
                        }
                    }

                    ulong empty_tn = t_neighbors & pos.bitBoards[Piece.EMPTY];
                    if (empty_tn)
                    {
                        ulong p2freezers = 0;
                        if (!p2pushers && p2frozen)
                        {
                            bitix p2frix = bitindex(p2frozen);
                            p2freezers = neighbors_of(p2frozen) & pos.placement[side^1]
                                & ~p1bit & ~p2bit;
                            while (p2freezers)
                            {
                                ulong p2f = p2freezers & -p2freezers;
                                bitix p2fix = bitindex(p2f);
                                if (pos.pieces[p2frix] < pos.pieces[p2fix] + enemyoffset)
                                    break;
                                p2freezers ^= p2f;
                            }
                        }
                        if (!p2freezers)
                        {
                            while (empty_tn)
                            {
                                ulong tobit = empty_tn & -empty_tn;
                                empty_tn ^= tobit;
                                add_capture(pos.pieces[p1ix], p1bit, 4, tbit, tbit, tobit);
                                if (!findall)
                                    return;
                            }
                        } else {
                            empty_tn &= neighbors_of(p2frozen);
                            if (empty_tn)
                            {
                                add_capture(pos.pieces[p1ix], p1bit, 4, tbit, tbit, empty_tn);
                                if (!findall)
                                    return;
                            }
                        }
                    }
                }
            } else {
                ulong p1tobits = p1neighbors & pos.bitBoards[Piece.EMPTY];
                ulong p2tobits = p2neighbors & pos.bitBoards[Piece.EMPTY];

                if (p1tobits & p2tobits)
                {
                    if (!(p1tobits & ~p2tobits))
                    {
                        p2tobits &= ~p1tobits;
                    }
                    if (!(p2tobits & ~p1tobits))
                    {
                        p1tobits &= ~p2tobits;
                    }
                }

                ulong p1pulls = neighbors_of(p1pushers) & pos.bitBoards[Piece.EMPTY];
                ulong p2pulls = neighbors_of(p2pushers) & pos.bitBoards[Piece.EMPTY];
                if (popcount(p1pulls) == 1 && (p1pulls & p2pulls))
                    p2pulls ^= p1pulls;
                if (popcount(p2pulls) == 1 && (p2pulls & p1pulls))
                    p1pulls ^= p2pulls;
                if (!(p1tobits || p1pulls) || !(p2tobits || p2pulls))
                    return;

                bitix tix = bitindex(tbit);

                if (p1pushers && (p2pushers || (p2frozen & neighbors_of(p1bit))))
                {
                    while (p1tobits)
                    {
                        ulong tobit = p1tobits & -p1tobits;
                        p1tobits ^= tobit;
                        add_capture(pos.pieces[tix], tbit, 4, tbit, p1bit, tobit, true);
                        if (!findall)
                            return;
                    }
                }
                if (p2pushers && (p1pushers || (p1frozen & neighbors_of(p2bit))))
                {
                    while (p2tobits)
                    {
                        ulong tobit = p2tobits & -p2tobits;
                        p2tobits ^= tobit;
                        add_capture(pos.pieces[tix], tbit, 4, tbit, p2bit, tobit, true);
                        if (!findall)
                            return;
                    }
                }

                p1pushers &= neighbors_of(p1pulls);
                p2pushers &= neighbors_of(p2pulls);
                if (popcount(p1pushers) == 1 && (p1pushers & p2pushers))
                    p2pushers ^= p1pushers;
                if (popcount(p2pushers) == 1 && (p2pushers & p1pushers))
                    p1pushers ^= p2pushers;
                if (!p1pushers || !p2pushers)
                    return;
                while (p1pushers)
                {
                    ulong pbit = p1pushers & -p1pushers;
                    p1pushers ^= pbit;
                    while (p1pulls)
                    {
                        ulong tobit = p1pulls & -p1pulls;
                        p1pulls ^= tobit;
                        add_capture(pos.pieces[tix], tbit, 4, tbit, pbit, tobit);
                        if (!findall)
                            return;
                    }
                }
                while (p2pushers)
                {
                    ulong pbit = p2pushers & -p2pushers;
                    p2pushers ^= pbit;
                    while (p2pulls)
                    {
                        ulong tobit = p2pulls & -p2pulls;
                        p2pulls ^= tobit;
                        add_capture(pos.pieces[tix], tbit, 4, tbit, pbit, tobit);
                        if (!findall)
                            return;
                    }
                }
            }
        }
    }

    int find_captures(Position pos, Side side, bool findall=true)
    {
        num_captures = 0;

        ulong trapbits = TRAPS;
        while (trapbits)
        {
            ulong tbit = trapbits & -trapbits;
            trapbits ^= tbit;

            switch (popcount(neighbors_of(tbit) & pos.placement[side^1]))
            {
                case 0:
                    gen_0n(pos, tbit, side, findall);
                    break;
                case 1:
                    gen_1n(pos, tbit, side, findall);
                    break;
                case 2:
                    gen_2n(pos, tbit, side, findall);
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
