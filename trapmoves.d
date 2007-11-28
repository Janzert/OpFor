
import std.stdio;

import position;

class TrapGenerator
{
    static const int MAX_CAPTURES = 50;

    int num_captures;
    Piece[MAX_CAPTURES] piece_captured;
    int[MAX_CAPTURES] capture_steps;
    Step[MAX_CAPTURES] first_step;

    void add_capture(Piece piece, int steps, ulong frombit, ulong tobit, bool ispush=false)
    {
        piece_captured[num_captures] = piece;
        capture_steps[num_captures] = steps;
        first_step[num_captures].set(frombit, tobit, ispush);
        num_captures++;
    }

    void add_capture(Piece piece, int steps, Step* step)
    {
        piece_captured[num_captures] = piece;
        capture_steps[num_captures] = steps;
        first_step[num_captures] = *step;
        num_captures++;
    }

    private void gen_0n(Position pos, ulong tbit)
    {
        // There are no enemy pieces neighboring the trap
        int enemyoffset = -6;
        if (pos.side == Side.BLACK)
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

                if (nbit & pos.placement[pos.side] & ~pos.frozen)
                {
                    // neighbor has an unfrozen friendly piece
                    ulong possibles = neighbors_of(nbit) & pos.placement[pos.side^1];
                    while (possibles)
                    {
                        ulong pbit = possibles & -possibles;
                        possibles ^= pbit;
                        bitix pix = bitindex(pbit);

                        if (pos.pieces[nix] > pos.pieces[pix] + enemyoffset)
                        {
                            ulong tobits =  neighbors_of(nbit) & ~tbit & ~pbit & pos.bitBoards[Piece.EMPTY];
                            if (tobits & (pos.strongest[pos.side][nix] > pos.pieces[pix] + enemyoffset))
                            {
                                ulong tobit = tobits & -tobits; // XXX: There should only be one bit in tobits set
                                add_capture(pos.pieces[pix], 4, nbit, tobit);
                            } else {
                                while (tobits)
                                {
                                    ulong tobit = tobits & -tobits;
                                    tobits ^= tobit;
                                    bitix toix = bitindex(tobit);

                                    if (pos.pieces[nix] >= (pos.strongest[pos.side^1][toix] + enemyoffset))
                                    {
                                        add_capture(pos.pieces[pix], 4, nbit, tobit);
                                        break;
                                    }
                                }
                            }

                            if ((t_neighbors & pos.bitBoards[Piece.EMPTY])
                                    && (t_neighbors & ~nbit & pos.placement[pos.side]))
                            {
                                add_capture(pos.pieces[pix], 4, nbit, tbit);
                            }
                        }
                    }
                } else if (nbit & pos.bitBoards[Piece.EMPTY])
                {
                    // the neighbor is empty
                    ulong possibles = neighbors_of(nbit) & pos.placement[pos.side^1];
                    while (possibles)
                    {
                        ulong pbit = possibles & -possibles;
                        possibles ^= pbit;
                        bitix pix = bitindex(pbit);

                        if ((nbit & pos.lastfrom) 
                                && (pos.lastpiece > pos.pieces[pix] + enemyoffset))
                        {
                            // can pull piece closer to trap
                            ulong finishers = neighbors_of(nbit) & pos.placement[pos.side] & ~pos.frozen;
                            while (finishers)
                            {
                                ulong fbit = finishers & -finishers;
                                finishers ^= fbit;
                                bitix fix = bitindex(fbit);

                                if (pos.pieces[fix] > pos.pieces[pix] + enemyoffset)
                                {
                                    // can finish trap
                                    add_capture(pos.pieces[pix], 3, pbit, nbit);
                                    break;
                                }
                            }
                        }

                        ulong pneighbors = neighbors_of(pbit) & pos.placement[pos.side] & ~pos.frozen;
                        while (pneighbors)
                        {
                            ulong pnbit = pneighbors & -pneighbors;
                            pneighbors ^= pnbit;
                            bitix pnix = bitindex(pnbit);

                            if (pos.pieces[pnix] > pos.pieces[pix] + enemyoffset)
                            {
                                if (pos.pieces[pnix] >= pos.strongest[pos.side^1][pix] + enemyoffset)
                                {
                                    // This piece won't be frozen and can finish trap
                                    add_capture(pos.pieces[pix], 4, pbit, nbit, true);
                                    break;
                                } else if (pos.strongest[pos.side][nix] > pos.pieces[pix] + enemyoffset)
                                {
                                    // possibly another neighbor of nix can finish the trap
                                    bool finished = false;
                                    ulong finishers = neighbors_of(nbit) & pos.placement[pos.side] & ~pos.frozen;
                                    while (finishers)
                                    {
                                        ulong fbit = finishers & -finishers;
                                        finishers ^= fbit;
                                        bitix fix = bitindex(fbit);

                                        if (pos.pieces[fix] > pos.pieces[pix] + enemyoffset)
                                        {
                                            // can finish trap
                                            add_capture(pos.pieces[pix], 4, pbit, nbit, true);
                                            break;
                                        }
                                    }
                                    if (finished)
                                        break;
                                }
                            }
                        }
                    }
                }
            }
        } else {
            // no enemy pieces neighboring the trap and it's not empty so
            // it seems there must be a friendly piece sitting on the trap
            assert (tbit & pos.placement[pos.side]);
            
            bitix tix = bitindex(tbit);
            ulong lastbit = 1UL << pos.lastfrom;
            if ((t_neighbors & lastbit)
                    && (t_neighbors & pos.bitBoards[Piece.EMPTY]))
            {
                ulong possibles = neighbors_of(lastbit) & pos.placement[pos.side^1];
                while (possibles)
                {
                    ulong pbit = possibles & -possibles;
                    possibles ^= pbit;
                    bitix pix = bitindex(pbit);

                    if ((pos.lastpiece > pos.pieces[pix] + enemyoffset)
                            && (pos.pieces[tix] > pos.pieces[pix] + enemyoffset))
                    {
                        add_capture(pos.pieces[pix], 3, pbit, lastbit);
                    }
                }
            }
        }
    }

    private void gen_1n(Position pos, ulong tbit)
    {
        // One enemy piece neighboring the trap
        int enemyoffset = -6;
        int pieceoffset = 0;
        if (pos.side == Side.BLACK)
        {
            enemyoffset = 6;
            pieceoffset = 6;
        }

        bitix tix = bitindex(tbit);
        ulong t_neighbors = neighbors_of(tbit);
        ulong pbit = t_neighbors & pos.placement[pos.side^1];
        bitix pix = bitindex(pbit);
        ulong lastbit = 1UL << pos.lastfrom;
        if (tbit & pos.placement[pos.side^1])
        {
            ulong pneighbors = neighbors_of(pbit);
            if ((pneighbors & lastbit)
                    && (pos.lastfrom > pos.pieces[pix] + enemyoffset))
            {
                add_capture(pos.pieces[tix], 1, pbit, lastbit);
            }

            while (pneighbors)
            {
                ulong pnbit = pneighbors & -pneighbors;
                pneighbors ^= pnbit;
                bitix pnix = bitindex(pnbit);

                if (pnbit & pos.placement[pos.side])
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

                                add_capture(pos.pieces[tix], 2, pbit, tobit, true);
                            }

                            ulong pulltos = neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY];
                            while (pulltos)
                            {
                                ulong tobit = pulltos & -pulltos;
                                pulltos ^= tobit;

                                add_capture(pos.pieces[tix], 2, pnbit, tobit);
                            }
                        }

                        // can this piece move out of the way and have another piece do the push/pull
                        ulong finishers = neighbors_of(pnbit);
                        if ((finishers & pos.bitBoards[Piece.EMPTY])
                                && (finishers & pos.placement[pos.side] & ~pos.frozen))
                        {
                            finishers &= pos.placement[pos.side] & ~pos.frozen;
                            while (finishers)
                            {
                                ulong fbit = finishers & -finishers;
                                finishers ^= fbit;
                                bitix fix = bitindex(fbit);

                                if ((pos.pieces[fix] > pos.pieces[pix] + enemyoffset)
                                        && ((neighbors_of(fbit) & pos.placement[pos.side] & ~pnbit)
                                            || ((fbit & ~TRAPS)
                                                && (pos.pieces[fix] >= pos.strongest[pos.side^1][fix] + enemyoffset))))
                                {
                                    // finisher can push pix and won't be frozen or safe in pn moves away
                                    ulong tobits = neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY];
                                    if (pos.pieces[pnix] == Piece.WRABBIT + pieceoffset)
                                    {
                                        tobits &= ~((pnbit & NOT_RANK_1) >> 8);
                                    } else {
                                        tobits &= ~((pnbit & NOT_RANK_8) << 8);
                                    }
                                    
                                    bool real_finish = false;
                                    while (tobits)
                                    {
                                        ulong tobit = tobits & -tobits;
                                        tobits ^= tobit;

                                        if ((tobit & ~TRAPS)
                                                || (neighbors_of(pnbit) & pos.placement[pos.side] & ~fbit)
                                                || (neighbors_of(tobit) & pos.placement[pos.side] & ~pnbit & ~fbit)
                                                || (pos.pieces[fix] >= pos.strongest[pos.side^1][pnbit] + enemyoffset))
                                        {
                                            // pn square will be safe for finisher after pn piece moves away
                                            real_finish = true;
                                            add_capture(pos.pieces[tix], 4, pnbit, tobit);
                                        }
                                    }
                                    if (real_finish)
                                    {
                                        break;
                                    }
                                }
                            }
                        }
                    } else {
                        // pn is frozen can we unfreeze in two steps or less
                        ulong pn_neighbors = neighbors_of(pnbit) & ~pbit;
                        while (pn_neighbors)
                        {
                            ulong pnnbit = pn_neighbors & -pn_neighbors;
                            pn_neighbors ^= pnnbit;

                            if (pnnbit & pos.bitBoards[Piece.EMPTY])
                            {
                                ulong pnn_neighbors = neighbors_of(pnnbit) & ~pos.placement[pos.side^1];
                                while (pnn_neighbors)
                                {
                                    ulong pnnnbit = pnn_neighbors & -pnn_neighbors;
                                    pnn_neighbors ^= pnnnbit;
                                    bitix pnnnix = bitindex(pnnnbit);

                                    if (pnnnbit & pos.bitBoards[Piece.EMPTY])
                                    {
                                        ulong unfreezers = neighbors_of(pnnnbit) & pos.placement[pos.side] & ~pos.frozen;
                                        while (unfreezers)
                                        {
                                            ulong unbit = unfreezers & -unfreezers;
                                            unfreezers ^= unbit;
                                            bitix unix = bitindex(unbit);

                                            if ((pos.placement[pos.side] & neighbors_of(pnnnbit) & ~unbit)
                                                    || !((pnnnbit & TRAPS)
                                                        || (pos.pieces[unix] >= pos.strongest[pos.side^1][pnnnix] + enemyoffset)))
                                            {
                                                if (pos.pieces[unix] == Piece.WRABBIT + pieceoffset)
                                                {
                                                    // can it really make the two steps to pnn
                                                    ulong rsteps;
                                                    if (pos.side == Side.WHITE)
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
                                                add_capture(pos.pieces[tix], 4, unbit, pnnnbit);
                                            }
                                        }
                                    } else {
                                        // pnnn must have a friendly piece on it
                                        
                                        if (pos.pieces[pnnnix] == Piece.WRABBIT + pieceoffset)
                                        {
                                            ulong rsteps = neighbors_of(pnnnbit);
                                            if (pos.side == Side.WHITE)
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
                                                & pos.placement[pos.side] & ~pos.frozen;
                                            while (unfreezers)
                                            {
                                                ulong unbit = unfreezers & -unfreezers;
                                                unfreezers ^= unbit;
                                                bitix unix = bitindex(unbit);

                                                ulong tobit = neighbors_of(unbit) & neighbors_of(pnnbit);
                                                if (pos.pieces[unix] == Piece.WRABBIT + pieceoffset)
                                                {
                                                    ulong rsteps = neighbors_of(unbit);
                                                    if (pos.side == Side.WHITE)
                                                    {
                                                        rsteps &= ~((unbit & NOT_RANK_1) >> 8);
                                                    } else {
                                                        rsteps &= ~((unbit & NOT_RANK_8) << 8);
                                                    }
                                                    if (!(rsteps & tobit))
                                                    {
                                                        continue;
                                                    }
                                                }
                                                add_capture(pos.pieces[tix], 4, unbit, tobit);
                                            }
                                        } else {
                                            add_capture(pos.pieces[tix], 3, pnnnbit, pnnbit);
                                        }
                                    }
                                }
                            } else {
                                // pnn must have enemy piece can we push it away
                                bitix pnnix = bitindex(pnnbit);

                                ulong pushtos = neighbors_of(pnnbit) & pos.bitBoards[Piece.EMPTY];
                                if (pushtos
                                        && (pos.strongest[pos.side][pnnix] > pos.pieces[pnnix] + enemyoffset))
                                {
                                    // we have a spot to push it to and a piece that might be able to push it
                                    ulong pushers = neighbors_of(pnnbit) & pos.placement[pos.side] & ~pos.frozen;
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
                                                add_capture(pos.pieces[tix], 4, pnnbit, tobit, true);
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
                    ulong pn_neighbors = neighbors_of(pnbit) & ~pos.placement[pos.side^1];
                    while (pn_neighbors)
                    {
                        ulong pnnbit = pn_neighbors & -pn_neighbors;
                        pn_neighbors ^= pnnbit;
                        bitix pnnix = bitindex(pnnbit);

                        if (pnnbit & pos.bitBoards[Piece.EMPTY]
                                && (pos.strongest[pos.side][pnnix] > pos.pieces[pix] + enemyoffset))
                        {
                            ulong pushers = neighbors_of(pnnbit) & pos.placement[pos.side] & ~pos.frozen;
                            while (pushers)
                            {
                                ulong perbit = pushers & -pushers;
                                pushers ^= perbit;
                                bitix perix = bitindex(perbit);

                                if ((pos.pieces[perix] > pos.pieces[pix] + enemyoffset)
                                        && ((pos.pieces[perix] >= pos.strongest[pos.side^1][pnix] + enemyoffset)
                                            || (pos.placement[pos.side] & neighbors_of(pnbit)))
                                        && ((pos.placement[pos.side] & neighbors_of(pnnbit) & ~perbit)
                                            || !((perbit & TRAPS)
                                                || (pos.pieces[perix] >= pos.strongest[pos.side^1][pnnix] + enemyoffset))))
                                {
                                    add_capture(pos.pieces[tix], 4, perbit, pnnbit);
                                }
                            }
                        } else if (pos.pieces[pnnix] > pos.pieces[pix] + enemyoffset)
                        {
                            // pnn must be a friendly piece that can push pix
                            if (pnnbit & pos.frozen)
                            {
                                ulong unfreezers = neighbors_of(neighbors_of(pnnbit) & pos.bitBoards[Piece.EMPTY])
                                    & pos.placement[pos.side] & ~pos.frozen;
                                while (unfreezers)
                                {
                                    ulong unbit = unfreezers & -unfreezers;
                                    unfreezers ^= unbit;
                                    bitix unix = bitindex(unbit);

                                    ulong tobit = neighbors_of(unbit) & neighbors_of(pnnbit);
                                    if (pos.pieces[unix] == Piece.WRABBIT + pieceoffset)
                                    {
                                        ulong rsteps = neighbors_of(unbit);
                                        if (pos.side == Side.WHITE)
                                        {
                                            rsteps &= ~((unbit & NOT_RANK_1) >> 8);
                                        } else {
                                            rsteps &= ~((unbit & NOT_RANK_8) << 8);
                                        }
                                        if (!(rsteps & tobit))
                                        {
                                            continue;
                                        }
                                    }
                                    add_capture(pos.pieces[tix], 4, unbit, tobit);
                                }
                            } else {
                                add_capture(pos.pieces[tix], 3, pnnbit, pnbit);
                            }
                        }
                    }
                } else if ((pos.strongest[pos.side][pnix] > pos.pieces[pnix] + enemyoffset)
                        && (pos.strongest[pos.side][pnix] > pos.pieces[pix] + enemyoffset))
                {
                    // pn must be an enemy
                    ulong pushtos = neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY] & ~neighbors_of(tbit);
                    if (pushtos)
                    {
                        ulong pushers = neighbors_of(pnbit) & pos.placement[pos.side] & ~pos.frozen;
                        while (pushers)
                        {
                            ulong perbit = pushers & -pushers;
                            pushers ^= perbit;
                            bitix perix = bitindex(perbit);

                            if ((pos.pieces[perix] > pos.pieces[pnix] + enemyoffset)
                                    && (pos.pieces[perix] > pos.pieces[pix] + enemyoffset)
                                    && ((pos.pieces[perix] >= pos.strongest[pos.side^1][pnix] + enemyoffset)
                                        || (neighbors_of(pnix) & pos.placement[pos.side] & ~perbit)))
                            {
                                // pusher can finish it
                                while (pushtos)
                                {
                                    ulong tobit = pushtos & -pushtos;
                                    pushtos ^= tobit;
                                    add_capture(pos.pieces[tix], 4, pnbit, tobit, true);
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
            Step[(MAX_CAPTURES/4)+1] clear_first_step;
            int[(MAX_CAPTURES/4)+1] clear_length;

            if (tbit & pos.placement[pos.side])
            {
                min_clear_steps = 4;
                ulong tneighbors = neighbors_of(tbit) & ~pbit;
                int friendlies = popcount(tneighbors & pos.placement[pos.side]);
                bool canpull = pos.pieces[tix] > pos.pieces[pix] + enemyoffset;
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
                    } else if ((tnbit & pos.placement[pos.side])
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
                                clear_first_step[num_clears].set(tnbit, tnnbit);
                                clear_length[num_clears] = 2;
                                num_clears++;
                            } else if (canpull)
                            {
                                if (tnnbit & pos.placement[pos.side])
                                {
                                    ulong tobits = neighbors_of(tnnbit) & pos.bitBoards[Piece.EMPTY];
                                    if (tnnbit & pos.bitBoards[Piece.WRABBIT + pieceoffset])
                                    {
                                        if (pos.side == Side.WHITE)
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
                        add_capture(pos.pieces[pix], 1 + clear_length[i], &clear_first_step[i]);
                    }
                    return;
                }
            }

            if ((lastbit & tbit)
                    && (pos.lastpiece > pos.pieces[pix] + enemyoffset))
            {
                // Can finish a pull onto the trap
                add_capture(pos.pieces[pix], 1, pbit, lastbit);
            }

            ulong pneighbors = neighbors_of(pbit);
            while (pneighbors)
            {
                ulong pnbit = pneighbors & -pneighbors;
                pneighbors ^= pnbit;
                bitix pnix = bitindex(pnbit);

                if (pnbit & pos.placement[pos.side])
                {
                    if (pnbit & tbit)
                    {
                        if ((min_clear_steps == 1)
                                && (pos.strongest[pos.side][tix] > pos.pieces[pix] + enemyoffset))
                        {
                            ulong pullers = neighbors_of(tbit) & pos.placement[pos.side];
                            while (pullers)
                            {
                                ulong pullbit = pullers & -pullers;
                                pullers ^= pullbit;
                                bitix pullix = bitindex(pullbit);

                                if ((pos.pieces[pullix] > pos.pieces[pix] + enemyoffset)
                                        && ((pos.pieces[pullix] >= pos.strongest[pos.side^1][pullix] + enemyoffset)
                                            || (neighbors_of(pullbit) & pos.placement[pos.side] & ~tbit)))
                                {
                                    for (int i=0; i < num_clears; i++)
                                    {
                                        if (clear_length[i] == 1)
                                        {
                                            add_capture(pos.pieces[pix], 4, &clear_first_step[i]);
                                        }
                                    }
                                    break;
                                }
                            }
                        }
                    } else if (pnbit & pos.frozen)
                    {
                        ulong aneighbors = neighbors_of(pnbit);
                        while (aneighbors)
                        {
                            ulong anbit = aneighbors & -aneighbors;
                            aneighbors ^= anbit;
                            bitix anix = bitindex(anbit);

                            if (anbit & pos.bitBoards[Piece.EMPTY])
                            {
                                ulong unfreezers = neighbors_of(anbit) & pos.placement[pos.side];
                                while (unfreezers)
                                {
                                    ulong ufbit = unfreezers & -unfreezers;
                                    unfreezers ^= ufbit;

                                    if (ufbit & pos.bitBoards[Piece.WRABBIT + pieceoffset])
                                    {
                                        ulong rabbitsteps = neighbors_of(ufbit);
                                        if (pos.side == Side.WHITE)
                                        {
                                            rabbitsteps &= ~((ufbit & NOT_RANK_1) >> 8);
                                        } else {
                                            rabbitsteps &= ~((ufbit & NOT_RANK_8) << 8);
                                        }
                                        if (!(rabbitsteps & neighbors_of(pnbit)))
                                        {
                                            continue;
                                        }
                                    }

                                    if (ufbit & pos.frozen)
                                    {
                                        // can we unfreeze the unfreezer?
                                        if (min_clear_steps)
                                            continue;

                                        ulong unfunfreezers = neighbors_of(neighbors_of(ufbit) & pos.bitBoards[Piece.EMPTY])
                                            & pos.placement[pos.side] & ~pos.frozen;
                                        while (unfunfreezers)
                                        {
                                            ulong ufufbit = unfunfreezers & -unfunfreezers;
                                            unfunfreezers ^= ufufbit;

                                            if (ufufbit & pos.bitBoards[Piece.WRABBIT + pieceoffset])
                                            {
                                                ulong rabbitsteps = neighbors_of(ufufbit);
                                                if (pos.side == Side.WHITE)
                                                {
                                                    rabbitsteps &= ~((ufufbit & NOT_RANK_1) >> 8);
                                                } else {
                                                    rabbitsteps &= ~((ufufbit & NOT_RANK_8) << 8);
                                                }
                                                if (!(rabbitsteps & neighbors_of(ufbit)))
                                                {
                                                    continue;
                                                }
                                            }
                                            add_capture(pos.pieces[pix], 4, ufufbit, anbit);
                                        }
                                    } else if (min_clear_steps < 2)
                                    {
                                        ulong tobit = neighbors_of(ufbit) & neighbors_of(pnbit);
                                        if (min_clear_steps)
                                        {
                                            for (int i=0; i < num_clears; i++)
                                            {
                                                add_capture(pos.pieces[pix], 3 + clear_length[i], &clear_first_step[i]);
                                            }
                                        } else {
                                            add_capture(pos.pieces[pix], 3, ufbit, tobit);
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

                                        unfreezers = neighbors_of(tobit) & pos.placement[pos.side] & ~pos.frozen;
                                        while (unfreezers)
                                        {
                                            ulong unfbit = unfreezers & -unfreezers;
                                            unfreezers ^= unfbit;
                                            bitix unfix = bitindex(unfbit);

                                            if ((pos.pieces[unfix] > pos.strongest[pos.side^1][tobit] + enemyoffset)
                                                    || (neighbors_of(tobit) & pos.placement[pos.side] & ~unfbit))
                                            {
                                                add_capture(pos.pieces[pix], 4, unfbit, tobit);
                                            }
                                        }
                                    }
                                }
                            } else if ((min_clear_steps == 0)
                                    && (pos.strongest[pos.side][anix] > pos.pieces[anix] + enemyoffset)
                                    && (neighbors_of(anbit) & pos.bitBoards[Piece.EMPTY]))
                            {
                                // an is enemy piece can we push out of the way
                                ulong pushers = neighbors_of(anbit) & pos.placement[pos.side] & ~pos.frozen;
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

                                            add_capture(pos.pieces[pix], 4, anbit, tobit, true);
                                        }
                                        break;
                                    }
                                }
                            }
                        }
                    } else if (pos.pieces[pnix] > pos.pieces[pix] + enemyoffset)
                    {
                        // Can push onto trap
                        if (min_clear_steps)
                        {
                           for (int i=0; i < num_clears; i++)
                            {
                                add_capture(pos.pieces[pix], 2 + clear_length[i], &clear_first_step[i]);
                            }
                        } else { 
                            add_capture(pos.pieces[pix], 2, pbit, tbit, true);
                        }
                    } else if ((min_clear_steps == 0)
                            && (neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY])
                            && (pos.strongest[pos.side][pnix] > pos.pieces[pix] + enemyoffset))
                    {
                        // this piece is too weak but it has a neighbor that is strong enough
                        ulong potentialsteps = neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY];
                        if (pos.pieces[pnix] == Piece.WRABBIT + pieceoffset)
                        {
                            // piece in the way is a rabbit make sure it can really move
                            if (pos.side == Side.WHITE)
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

                        ulong finishers = neighbors_of(pnbit) & pos.placement[pos.side];
                        while (finishers)
                        {
                            ulong fbit = finishers & -finishers;
                            finishers ^= fbit;
                            bitix fix = bitindex(fbit);

                            if ((pos.pieces[fix] > pos.pieces[pix] + enemyoffset)
                                    && ((pos.pieces[fix] >= pos.strongest[pos.side^1][fix] + enemyoffset)
                                        || (neighbors_of(fbit) & pos.placement[pos.side] & ~pnbit)))
                            {
                                // finisher can push the enemy piece and won't
                                // be frozen when the neighbor moves out of the way.
                                bool real_finish = false;
                                while (potentialsteps)
                                {
                                    ulong tobit = potentialsteps & -potentialsteps;
                                    potentialsteps ^= tobit;
                                    if ((tobit & ~TRAPS) 
                                            || (pos.pieces[fix] >= pos.strongest[pos.side^1][pnix] + enemyoffset)
                                            || (neighbors_of(tobit) & pos.placement[pos.side]))
                                    {
                                        // finisher won't be frozen once moving into the neighbor square
                                        real_finish = true;
                                        add_capture(pos.pieces[pix], 4, pnbit, tobit);
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
                    ulong attackers = neighbors_of(pnbit) & pos.placement[pos.side];
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
                                            || (pos.pieces[aix] < pos.strongest[pos.side^1][pnix] + enemyoffset))
                                        && !(neighbors_of(pnbit) & pos.placement[pos.side] & ~abit))
                                {
                                    if (min_clear_steps)
                                        continue;

                                    // intermediate square isn't safe can we bring in support?
                                    ulong supporters = neighbors_of(neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY])
                                        & pos.placement[pos.side] & ~pos.frozen;
                                    while (supporters)
                                    {
                                        ulong sbit = supporters & -supporters;
                                        supporters ^= sbit;
                                        bitix six = bitindex(sbit);

                                        ulong tobit = neighbors_of(sbit) & neighbors_of(pnbit);
                                        if (pos.pieces[six] == Piece.WRABBIT + pieceoffset)
                                        {
                                            if (pos.side == Side.WHITE)
                                            {
                                                if (tobit & ~((sbit & NOT_RANK_1) >> 8))
                                                {
                                                    add_capture(pos.pieces[pix], 4, sbit, tobit);
                                                }
                                            } else {
                                                if (tobit & ~((sbit & NOT_RANK_8) << 8))
                                                {
                                                    add_capture(pos.pieces[pix], 4, sbit, tobit);
                                                }
                                            }
                                        } else {
                                            add_capture(pos.pieces[pix], 4, sbit, tobit);
                                        }
                                    }
                                } else {
                                    switch (min_clear_steps)
                                    {
                                        case 0:
                                            add_capture(pos.pieces[pix], 3, abit, pnbit);
                                            break;
                                        case 1:
                                            for (int i=0; i < num_clears; i++)
                                            {
                                                add_capture(pos.pieces[pix], 3 + clear_length[i], &clear_first_step[i]);
                                            }
                                            break;
                                        default:
                                    }
                                }
                            } else if (!(((pnbit & TRAPS)
                                        || (pos.pieces[aix] < pos.strongest[pos.side^1][pnix] + enemyoffset))
                                    && !(neighbors_of(pnbit) & pos.placement[pos.side] & ~abit))
                                    && (min_clear_steps == 0))
                            {
                                // attacker is frozen, intermediate space is safe
                                ulong supporters = neighbors_of(neighbors_of(abit) & pos.bitBoards[Piece.EMPTY])
                                    & pos.placement[pos.side] & ~pos.frozen & ~abit;
                                while (supporters)
                                {
                                    ulong sbit = supporters & -supporters;
                                    supporters ^= sbit;
                                    bitix six = bitindex(sbit);

                                    ulong tobit = neighbors_of(sbit) & neighbors_of(abit);
                                    if (pos.pieces[six] == Piece.WRABBIT + pieceoffset)
                                    {
                                        if (pos.side == Side.WHITE)
                                        {
                                            if (tobit & ~((sbit & NOT_RANK_1) >> 8))
                                            {
                                                add_capture(pos.pieces[pix], 4, sbit, tobit);
                                            }
                                        } else {
                                            if (tobit & ~((sbit & NOT_RANK_8) << 8))
                                            {
                                                add_capture(pos.pieces[pix], 4, sbit, tobit);
                                            }
                                        }
                                    } else {
                                        add_capture(pos.pieces[pix], 4, sbit, tobit);
                                    }
                                }
                            }
                        }
                    }

                    if (min_clear_steps == 0)
                    {
                        attackers = neighbors_of(neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY])
                            & pos.placement[pos.side] & ~pos.frozen;
                        while (attackers)
                        {
                            ulong abit = attackers & -attackers;
                            attackers ^= abit;
                            bitix aix = bitindex(abit);

                            if ((pos.pieces[aix] > pos.pieces[pix] + enemyoffset)
                                    && ((pos.pieces[aix] >= pos.strongest[pos.side^1][pnix] + enemyoffset)
                                        || (neighbors_of(pnbit) & pos.placement[pos.side])))
                            {
                                ulong tobits = neighbors_of(abit) & neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY];
                                while (tobits)
                                {
                                    ulong tobit = tobits & -tobits;
                                    tobits ^= tobit;
                                    bitix toix = bitindex(tobit);
                                    if (((pos.pieces[aix] >= pos.strongest[pos.side^1][toix] + enemyoffset)
                                            && !(tobit & TRAPS))
                                        || (neighbors_of(tobit) & pos.placement[pos.side] & ~abit))
                                    {
                                        add_capture(pos.pieces[pix], 4, abit, tobit);
                                    }
                                }
                            }
                        }
                    }
                } else if ((neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY])
                        && (pos.strongest[pos.side][pnix] > pos.pieces[pnix] + enemyoffset)
                        && (pos.strongest[pos.side][pnix] > pos.pieces[pix]+ enemyoffset)
                        && (min_clear_steps == 0))
                {
                    // pnbit occupied by enemy piece
                    ulong attackers = neighbors_of(pnbit) & pos.placement[pos.side] & ~pos.frozen;
                    while (attackers)
                    {
                        ulong abit = attackers & -attackers;
                        attackers ^= abit;
                        bitix aix = bitindex(abit);

                        if ((pos.pieces[aix] > pos.pieces[pnix] + enemyoffset)
                                && (pos.pieces[aix] > pos.pieces[pix] + enemyoffset)
                                && ((pos.pieces[aix] >= pos.strongest[pos.side^1][pnix] + enemyoffset)
                                    || (neighbors_of(pnbit) & pos.placement[pos.side] & ~abit)))
                        {
                            // attacker is strong enough to push both pieces
                            // and won't be frozen after first push
                            ulong tobits = neighbors_of(pnbit) & pos.bitBoards[Piece.EMPTY] & ~neighbors_of(tbit);
                            while (tobits)
                            {
                                ulong tobit = tobits & -tobits;
                                tobits ^= tobit;

                                add_capture(pos.pieces[pix], 4, pnbit, tobit, true);
                            }
                        }
                    }
                }
            }
        }
    }

    private void gen_2n(Position pos, ulong tbit)
    {
        if (tbit & pos.bitBoards[Piece.EMPTY])
        {
            int enemyoffset = -6;
            int pieceoffset = 0;
            if (pos.side == Side.BLACK)
            {
                enemyoffset = 6;
                pieceoffset = 6;
            }

            ulong p2bit = neighbors_of(tbit) & pos.placement[pos.side^1];
            ulong p1bit = p2bit & -p2bit;
            p2bit ^= p1bit;
            bitix p1ix = bitindex(p1bit);
            bitix p2ix = bitindex(p2bit);

            ulong p1neighbors = neighbors_of(p1bit);
            ulong p2neighbors = neighbors_of(p2bit);

            if ((pos.strongest[pos.side][p1ix] >= pos.pieces[p1ix] + enemyoffset)
                    && (pos.strongest[pos.side][p2ix] >= pos.pieces[p2ix] + enemyoffset)
                    && (p1neighbors & pos.placement[pos.side]
                        & ~pos.frozen & ~(p2neighbors & pos.placement[pos.side])))
            {
                ulong exclusive = p1neighbors & p2neighbors & pos.placement[pos.side];

                ulong p2pushers = 0;
                ulong pospushers = p2neighbors & pos.placement[pos.side] & ~pos.frozen;
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
                pospushers = p1neighbors & pos.placement[pos.side] & ~pos.frozen;
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

                if (exclusive)
                {
                    if (!(p1pushers & ~exclusive))
                    {
                        if (!(p2pushers & ~exclusive))
                        {
                            return;
                        }
                        p2pushers &= ~exclusive;
                    } else if (!(p2pushers & ~exclusive))
                    {
                        p1pushers &= ~exclusive;
                    }
                }

                if (p2neighbors & pos.bitBoards[Piece.EMPTY])
                {
                    add_capture(pos.pieces[p1ix], 4, p1bit, tbit, true);
                }

                if (p1neighbors & pos.bitBoards[Piece.EMPTY])
                {
                    add_capture(pos.pieces[p2ix], 4, p2bit, tbit, true);
                }
            }
        }
    }

    void get_moves(Position pos)
    {
        num_captures = 0;

        ulong trapbits = TRAPS;
        while (trapbits)
        {
            ulong tbit = trapbits & -trapbits;
            trapbits ^= tbit;

            switch (popcount(neighbors_of(tbit) & pos.placement[pos.side^1]))
            {
                case 0:
                    gen_0n(pos, tbit);
                    break;
                case 1:
                    gen_1n(pos, tbit);
                    break;
                case 2:
                    gen_2n(pos, tbit);
                    break;
                default:
                    break;
            }
        }
    }
}
