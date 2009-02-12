
import std.stdio;

import position;

class GoalSearch
{
    Position start;

    uint[2] goals_found;
    bitix[8][2] rabbit_location;
    uint[8][2] goal_depth;
    uint[64] board_depth;

    Side cur_side;
    ulong goal_line;

    void set_start(Position pos)
    {
        if (start !is null)
        {
            Position.free(start);
        }
        start = pos.dup;
    }

    void clear_start()
    {
        if (start !is null)
        {
            Position.free(start);
        }
    }

    private ulong expand_forward(ulong bits)
    {
        ulong expanded;
        expanded = (bits & NOT_A_FILE) << 1;
        expanded |= (bits & NOT_H_FILE) >> 1;
        expanded |= ((bits << 8) >> (cur_side << 4))
            | (((bits & RANK_8) >> 8) << ((cur_side^1) << 5));
        //expanded |= (cur_side == Side.WHITE) ?
        //            (bits & NOT_RANK_8) << 8 : (bits & NOT_RANK_1) >> 8;

        return bits | expanded;
    }

    int find_unassisted(ulong rbit, int max_depth, ulong bad_neighbors)
    {
        ulong friend_neighbors = neighbors_of(start.placement[cur_side] ^ rbit);
        ulong good_squares = start.bitBoards[Piece.EMPTY] & ~((TRAPS | bad_neighbors) & ~friend_neighbors);

        int depth;
        ulong movement = expand_forward(rbit) & good_squares;
        for (depth = 1; depth <= max_depth; depth++)
        {
            if (movement & goal_line)
                break;
            ulong next = expand_forward(movement) & good_squares;
            if (next == movement)
            {
                depth = max_depth+1;
                break;
            }
            movement = next;
        }
        return depth;
    }

    void find_goals(int search_depth)
    {
        for (Side s=Side.WHITE; s <= Side.BLACK; s++)
        {
            cur_side = s;
            goal_line = RANK_8;
            uint piece_offset = 0;
            uint enemy_offset = 6;
            if (s == Side.BLACK)
            {
                goal_line = RANK_1;
                piece_offset = 6;
                enemy_offset = 0;
            }
            ulong friend_neighbors = neighbors_of(start.placement[cur_side]);
            ulong bad_neighbors = neighbors_of(start.placement[cur_side ^1] ^ start.bitBoards[Piece.WRABBIT+enemy_offset]);
            ulong good_squares = start.bitBoards[Piece.EMPTY] & ~((TRAPS | bad_neighbors) & ~friend_neighbors);

            ulong possible_squares = goal_line & start.bitBoards[Piece.EMPTY];
            ulong npossible = possible_squares | (neighbors_of(possible_squares) & good_squares);
            int pdepth = 1;
            while (pdepth < search_depth && possible_squares != npossible)
            {
                possible_squares = npossible;
                npossible = possible_squares | (neighbors_of(possible_squares) & good_squares);
                pdepth++;
            }
            possible_squares |= neighbors_of(possible_squares) & ~start.frozen;

            goals_found[s] = 0;
            ulong rabbits = start.bitBoards[Piece.WRABBIT+piece_offset];
            while (rabbits)
            {
                bitix rix = bitindex(rabbits); // using msbindex for white helps partially sort the goals
                ulong rbit = 1UL << rix;
                rabbits ^= rbit;

                int gdepth;
                if (rbit & possible_squares)
                {
                    gdepth = find_unassisted(rbit, search_depth, bad_neighbors);
                } else {
                    gdepth = search_depth + 1;
                }
                board_depth[rix] = gdepth;
                if (gdepth <= search_depth)
                {
                    uint cur_goal = (goals_found[s] == 0) ? 0 : 1;
                    goals_found[s]++;
                    rabbit_location[s][cur_goal] = rix;
                    goal_depth[s][cur_goal] = gdepth;
                    //while (cur_goal > 0 
                    if (cur_goal > 0
                            && goal_depth[s][cur_goal] < goal_depth[s][cur_goal-1])
                    {
                        rix = rabbit_location[s][cur_goal];
                        rabbit_location[s][cur_goal] = rabbit_location[s][cur_goal-1];
                        rabbit_location[s][cur_goal-1] = rix;

                        gdepth = goal_depth[s][cur_goal];
                        goal_depth[s][cur_goal] = goal_depth[s][cur_goal-1];
                        goal_depth[s][cur_goal-1] = gdepth;
                        //cur_goal--;
                    }
                }
            }
        }
    }
}

class GoalSearchDT
{
    const static int NOT_FOUND = 5;
    Position start;

    int[2] shortest;
    ulong goal_squares;

    void set_start(Position pos)
    {
        if (start !is null)
        {
            Position.free(start);
        }
        start = pos.dup;
        shortest[Side.WHITE] = shortest[Side.BLACK] = NOT_FOUND;
        goal_squares = 0;
    }

    void clear_start()
    {
        if (start !is null)
        {
            Position.free(start);
        }
        start = null;
        shortest[Side.WHITE] = shortest[Side.BLACK] = NOT_FOUND;
        goal_squares = 0;
    }

    private ulong backward(ulong bits, Side side)
    {
        return side ? bits << 8 : bits >> 8;
    }

    private ulong forward(ulong bits, Side side)
    {
        return side ? bits >> 8 : bits << 8;
    }

    private int opponent_goal(ulong gbit, Side side)
    {
        ulong gneighbors = neighbors_of(gbit);
        ulong side_friendlies;
        ulong gsides;
        Piece myrabbit;
        Piece erabbit;
        int enemyoffset;
        if (gbit & RANK_8)
        {
            myrabbit = Piece.WRABBIT;
            erabbit = Piece.BRABBIT;
            enemyoffset = 6;
            gsides = gneighbors & RANK_8;
            side_friendlies = gsides
                & start.placement[Side.WHITE]
                & ~start.frozen;
        } else {
            myrabbit = Piece.BRABBIT;
            erabbit = Piece.WRABBIT;
            enemyoffset = -6;
            gsides = gneighbors & RANK_1;
            side_friendlies = gsides
                & start.placement[Side.BLACK]
                & ~start.frozen;
        }

        int shortest_goal = NOT_FOUND;
        bitix gix = bitindex(gbit);
        ulong back_bit = backward(gbit, side);
        ulong bneighbors = neighbors_of(back_bit);
        ulong side_empties = gsides
            & start.bitBoards[Piece.EMPTY]
            & (neighbors_of(start.placement[side]
                    & ~start.bitBoards[myrabbit]
                    & ~start.frozen)
                    | (1UL << start.lastfrom));
        while (side_empties)
        {
            ulong se_bit = side_empties & -side_empties;
            side_empties ^= se_bit;
            bitix seix = bitindex(se_bit);
            if ((start.lastfrom == seix)
                    && ((start.lastpiece + enemyoffset)
                        > start.pieces[gix]))
            {
                if ((back_bit & start.bitBoards[myrabbit])
                        && ((back_bit & ~start.frozen)
                            || !(bneighbors & start.placement[side^1]
                                & ~start.bitBoards[erabbit] & ~gbit)))
                    return 2;
                if ((back_bit & start.bitBoards[myrabbit])
                        && (neighbors_of(bneighbors
                                & start.bitBoards[Piece.EMPTY])
                            & start.placement[side] & ~start.frozen))
                    return 3;
                ulong bn_rabbits = bneighbors & start.bitBoards[myrabbit];
                if (bn_rabbits & ~start.frozen)
                {
                    if (!(bneighbors & start.placement[side^1]
                                & ~start.bitBoards[erabbit]
                                & ~gbit)
                            || popcount(bneighbors
                                & start.placement[side]) > 1)
                        return 3;
                }
            }
            if (back_bit & start.bitBoards[myrabbit])
            {
                if ((start.strongest[side][seix] + enemyoffset
                            > start.pieces[gix])
                        && (start.strongest[side][seix] + enemyoffset
                            >= start.strongest[side^1][seix]))
                {
                    ulong pullers = neighbors_of(se_bit)
                        & start.placement[side] & ~start.frozen;
                    while (pullers)
                    {
                        ulong pbit = pullers & -pullers;
                        pullers ^= pbit;
                        bitix pix = bitindex(pbit);
                        if ((start.pieces[pix] + enemyoffset
                                    <= start.pieces[gix])
                                || (start.pieces[pix] + enemyoffset
                                    < start.strongest[side^1][seix]))
                            continue;
                        if (back_bit & ~start.frozen
                                || (neighbors_of(se_bit)
                                    & start.bitBoards[Piece.EMPTY]
                                    & bneighbors))
                        {
                            shortest_goal = 4;
                            break;
                        }
                    }
                }
            }
        }

        // Check that unfrozen friendlies to the side of the opponent on the
        // goal square exist
        if (!side_friendlies)
            return shortest_goal;

        // check that some friendly neighbor of the goal square is stronger
        // than it. It's a fast check so can give an early exit.
        if (start.pieces[gix] >= start.strongest[side][gix] + enemyoffset)
            return shortest_goal;

        bool has_sempty = cast(bool)(gsides & start.bitBoards[Piece.EMPTY]);
        ulong pullers = 0;
        while (side_friendlies)
        {
            ulong sfbit = side_friendlies & -side_friendlies;
            side_friendlies ^= sfbit;
            bitix sfix = bitindex(sfbit);

            // Is this piece stronger than the goal square piece
            if (start.pieces[sfix] + enemyoffset <= start.pieces[gix])
                continue;

            if ((backward(sfbit, side)
                        & start.bitBoards[myrabbit])
                    && (back_bit
                        & start.bitBoards[Piece.EMPTY])
                    && (start.pieces[sfix] + enemyoffset
                        >= start.strongest[side^1][sfix]))
            {
                shortest_goal = 4;
            } else if (has_sempty
                    && (back_bit & start.bitBoards[myrabbit])
                    && ((back_bit & ~start.frozen)
                        || !(bneighbors & ~gbit
                            & start.placement[side^1]
                            & ~start.bitBoards[erabbit])))
            {
                shortest_goal = 4;
            }
            ulong empty_neighbors = neighbors_of(sfbit)
                & start.bitBoards[Piece.EMPTY];
            // Is there some place for us to move so we can pull the piece
            // off the goal square
            if (!empty_neighbors)
            {
                if ((back_bit & start.bitBoards[myrabbit] & ~start.frozen)
                        && (start.pieces[sfix] + enemyoffset
                                >= start.strongest[side^1][sfix]))
                {
                    ulong fn = neighbors_of(sfbit) & start.placement[side]
                        & neighbors_of(start.bitBoards[Piece.EMPTY]);
                    if ((fn & ~start.bitBoards[myrabbit])
                            || (neighbors_of(fn) & ~backward(fn, side)
                                & start.bitBoards[Piece.EMPTY]))
                        shortest_goal = 4;
                }
                continue;
            }

            pullers |= sfbit;
        }
        // Can the piece occupying the goal square be pulled off
        if (!pullers)
        {
            return shortest_goal;
        }

        // check for a rabbit on the square back from the goal square
        if (back_bit & start.bitBoards[myrabbit])
        {
            // it's unfrozen
            if (back_bit & ~start.frozen)
                return 3;
            ulong empty_neighbors = bneighbors & start.bitBoards[Piece.EMPTY];
            // it can be unfrozen by the puller
            if (empty_neighbors & neighbors_of(pullers))
                return 3;
            // there is another piece that can come unfreeze it
            if (neighbors_of(empty_neighbors) & ~start.frozen
                    & start.placement[side])
                return 4;
        }
        else if ((back_bit & start.bitBoards[Piece.EMPTY])
                 && (bneighbors
                     & start.bitBoards[myrabbit]
                     & ~start.frozen)
                 && (!(bneighbors & start.placement[side^1]
                         & ~start.bitBoards[erabbit])
                     || (bneighbors & start.bitBoards[Piece.EMPTY]
                         & neighbors_of(pullers))
                     || popcount(bneighbors & start.placement[side]) > 1))
        {
            return 4;
        }

        return shortest_goal;
    }

    private int friendly_goal(ulong gbit, Side side)
    {
        const static ulong dist2 = 0x0010387C38100000UL;

        bitix gix = bitindex(gbit);
        ulong gneighbors = neighbors_of(gbit);
        int enemyoffset;
        Piece myrabbit;
        Piece erabbit;
        ulong back_bit;
        ulong goal_rank;
        ulong rabbit_mask;
        if (side == Side.WHITE)
        {
            myrabbit = Piece.WRABBIT;
            erabbit = Piece.BRABBIT;
            enemyoffset = 6;
            goal_rank = RANK_8;
            back_bit = gbit >> 8;
            rabbit_mask = dist2 << (gix-44);
        } else {
            myrabbit = Piece.BRABBIT;
            erabbit = Piece.WRABBIT;
            enemyoffset = -6;
            goal_rank = RANK_1;
            back_bit = gbit << 8;
            rabbit_mask = dist2 >> (28-gix);
        }

        // check that there isn't an enemy piece blocking any access
        if (back_bit & start.placement[side^1])
            return NOT_FOUND;

        // check that there is a rabbit within range
        if (!(rabbit_mask & start.bitBoards[myrabbit]))
            return NOT_FOUND;

        ulong side_neighbors = gneighbors & goal_rank;

        ulong bneighbors = neighbors_of(back_bit);
        ulong empty_sides = side_neighbors & start.bitBoards[Piece.EMPTY];
        if (empty_sides)
        {
            if (back_bit & start.bitBoards[myrabbit])
            {
                // Will the rabbit still be unfrozen after moving out of the way
                if ((bneighbors & start.placement[side] & ~gbit)
                        || !(bneighbors & start.placement[side^1]
                            & ~start.bitBoards[erabbit]))
                    return 2;

                // get any empty side spaces that lead to an empty space next
                // to the rabbit
                ulong freeze_check = neighbors_of(neighbors_of(empty_sides)
                        & bneighbors & start.bitBoards[Piece.EMPTY])
                    & empty_sides;
                while (freeze_check)
                {
                    ulong cbit = freeze_check & -freeze_check;
                    freeze_check ^= cbit;
                    bitix cix = bitindex(cbit);

                    if (start.pieces[cix] <= start.pieces[gix] + enemyoffset)
                        return 3;
                }

                ulong unfreezers = neighbors_of(bneighbors
                        & start.bitBoards[Piece.EMPTY]) & start.placement[side]
                    & ~back_bit;
                if (unfreezers & ~start.frozen)
                    return 3;

                // if the unfreezers are all frozen check to see if another
                // piece can unfreeze them
                if (neighbors_of(unfreezers)
                        & start.bitBoards[Piece.EMPTY] & ~bneighbors
                        & (neighbors_of(start.placement[side]
                                & ~start.bitBoards[myrabbit] & ~start.frozen)
                            | neighbors_of(start.bitBoards[myrabbit]
                                & ~start.frozen
                                & ~neighbors_of(forward(unfreezers, side)))))
                {
                    return 4;
                }

                ulong pushsq = neighbors_of(bneighbors
                        & start.placement[side^1]) & empty_sides;
                while (pushsq)
                {
                    ulong pbit = pushsq & -pushsq;
                    pushsq ^= pbit;
                    bitix pix = bitindex(pbit);
                    if (start.pieces[gix] + enemyoffset >= start.strongest[side^1][pix])
                    {
                        ulong pn = neighbors_of(pbit) & bneighbors & ~gbit;
                        if (!(neighbors_of(pn) & start.bitBoards[Piece.EMPTY]
                                    & ~pbit))
                        {
                            if ((neighbors_of(pbit)
                                        & start.bitBoards[Piece.EMPTY])
                                    && !(bneighbors & start.placement[side^1]
                                        & ~start.bitBoards[erabbit]
                                        & ~pn)
                                    && (start.pieces[gix] + enemyoffset >
                                        start.strongest[side^1][pix]))
                            {
                                return 4;
                            }
                            continue;
                        }
                        bitix pnix = bitindex(pn);
                        if (start.pieces[gix] + enemyoffset
                                > start.pieces[pnix])
                        {
                            return 4;
                        }
                    }
                }

                ulong unfsq = neighbors_of(bneighbors &
                        start.bitBoards[Piece.EMPTY])
                    & start.bitBoards[Piece.EMPTY]
                    & neighbors_of(start.placement[side] & ~start.frozen);
                if (unfsq & ~(TRAPS
                            | neighbors_of(start.placement[side^1]
                                & ~start.placement[side])))
                    return 4;
                while (unfsq)
                {
                    ulong unfsqb = unfsq & -unfsq;
                    unfsq ^= unfsqb;

                    ulong unfsq_neighbors = neighbors_of(unfsqb);
                    if (popcount(unfsq_neighbors & start.placement[side]) > 1)
                        return 4;
                    if (unfsqb & TRAPS)
                        continue;
                    bitix unfsqix = bitindex(unfsqb);
                    if (start.strongest[side][unfsqix] + enemyoffset
                            >= start.strongest[side^1][unfsqix])
                        return 4;
                }
                ulong push_to = start.bitBoards[Piece.EMPTY];
                if (popcount(empty_sides) < 2)
                    push_to &= ~empty_sides;
                ulong obn = bneighbors & start.placement[side^1]
                    & neighbors_of(start.placement[side]
                            & ~start.bitBoards[myrabbit]);
                bool can_pull = popcount(bneighbors & start.placement[side^1]
                        & ~start.bitBoards[erabbit]) < 2;
                if (!can_pull && !push_to)
                    return NOT_FOUND;
                while (obn)
                {
                    ulong obit = obn & -obn;
                    obn ^= obit;
                    bitix oix = bitindex(obit);
                    if (!(start.pieces[oix] < start.strongest[side][oix]
                                + enemyoffset))
                        continue;
                    ulong pushers = neighbors_of(obit) & start.placement[side]
                        & ~start.frozen;
                    while (pushers)
                    {
                        ulong pbit = pushers & -pushers;
                        pushers ^= pbit;
                        bitix pix = bitindex(pbit);
                        if (start.pieces[pix] + enemyoffset
                                <= start.pieces[oix])
                            continue;
                        if ((push_to & neighbors_of(obit))
                                || (can_pull && (neighbors_of(pbit)
                                        & start.bitBoards[Piece.EMPTY])))
                            return 4;
                    }
                }
                return NOT_FOUND;
            }
            else if (back_bit & start.placement[side])
            {
                if (!(bneighbors & start.bitBoards[Piece.EMPTY]))
                    return NOT_FOUND;

                ulong prabbits = bneighbors & start.bitBoards[myrabbit];
                while (prabbits)
                {
                    ulong rbit = prabbits & -prabbits;
                    prabbits ^= rbit;

                    ulong rn = neighbors_of(rbit);
                    if ((rn & start.placement[side] & ~back_bit)
                            || ((rbit & ~TRAPS) && !(rn
                                    & start.placement[side^1]
                                & ~start.bitBoards[erabbit])))
                        return 4;
                }
                return NOT_FOUND;
            } else { // back_bit is empty
                assert (back_bit & start.bitBoards[Piece.EMPTY]);
                ulong bn_rabbits = bneighbors & start.bitBoards[myrabbit];
                ulong fbn = bneighbors & start.placement[side] & ~gbit;
                int fbn_pop = popcount(fbn);
                if (bn_rabbits & ~start.frozen)
                {
                    if (!(bneighbors & start.placement[side^1]
                                & ~start.bitBoards[erabbit])
                            || fbn_pop > 1)
                        return 3;
                    // one neighbor is the goal, one is the rabbit,
                    // one is the freezing piece so there can only be one empty
                    ulong bn_empty = bneighbors & start.bitBoards[Piece.EMPTY];
                    if ((bn_empty & ~(TRAPS &
                                    ~neighbors_of(start.placement[side])))
                            && (gbit & ~start.frozen))
                    {
                        return 4;
                    }
                    if (bn_empty & neighbors_of(empty_sides))
                    {
                        return 4;
                    }
                    ulong unfreezers = (neighbors_of(bn_empty)
                            | neighbors_of(bn_rabbits))
                        & start.placement[side]
                        & ~start.frozen;
                    if (!unfreezers)
                        return NOT_FOUND;
                    // if there is an unfreezer that is not a current neighbor
                    // of the rabbit we can goal for sure
                    ulong rneighbors = neighbors_of(bn_rabbits);
                    if (unfreezers & ~rneighbors)
                    {
                        return 4;
                    }
                    // otherwise we have to check that one of them won't freeze
                    // when the other moves and that the unfreezer won't be
                    // trapped
                    if ((bn_empty & neighbors_of(unfreezers))
                            && !(rneighbors & start.placement[side^1]
                                & ~start.bitBoards[erabbit]))
                        return 4;

                    if (unfreezers & neighbors_of(start.placement[side]
                                & ~bn_rabbits))
                        return 4;
                    unfreezers &= ~TRAPS;
                    while (unfreezers)
                    {
                        ulong unfb = unfreezers & -unfreezers;
                        bitix unix = bitindex(unfb);
                        if (start.strongest[side^1][unix]
                                <= start.pieces[unix] + enemyoffset)
                            return 4;
                        unfreezers ^= unfb;
                    }
                }
                bool safe_bb = !(bneighbors & start.placement[side^1]
                        & ~start.bitBoards[erabbit]);
                if (bn_rabbits && (safe_bb || fbn_pop > 1))
                {
                    if (neighbors_of(neighbors_of(bn_rabbits & start.frozen)
                            & start.bitBoards[Piece.EMPTY])
                            & start.placement[side] & ~start.frozen
                            & ~bneighbors)
                        return 4;

                    if (safe_bb && (fbn & ~bn_rabbits & ~start.frozen
                                & neighbors_of(neighbors_of(bn_rabbits)
                                    & start.bitBoards[Piece.EMPTY]
                                    & ~back_bit)))
                    {
                        return 4;
                    }

                    if (safe_bb && (gbit & ~start.frozen) && (fbn & ~bn_rabbits
                                & neighbors_of(neighbors_of(bn_rabbits)
                                    & start.bitBoards[Piece.EMPTY]
                                    & ~back_bit)
                                & neighbors_of(empty_sides)))
                    {
                        return 4;
                    }
                }
                if (safe_bb || fbn)
                {
                    ulong pempties = bneighbors & start.bitBoards[Piece.EMPTY]
                        & neighbors_of(start.bitBoards[myrabbit]
                                & ~start.frozen);
                    if (pempties & ~(TRAPS
                                | neighbors_of(start.placement[side^1]
                                    & ~start.bitBoards[erabbit])))
                        return 4;
                    while (pempties)
                    {
                        ulong pebit = pempties & -pempties;
                        pempties ^= pebit;
                        if (popcount(neighbors_of(pebit)
                                    & start.placement[side]) > 1)
                            return 4;
                    }
                }
                return NOT_FOUND;
            }
        } else {
            // check that there is an unfrozen rabbit that can make it to us
            ulong bn_rabbits = (bneighbors | back_bit)
                & start.bitBoards[myrabbit] & ~start.frozen;
            if (!bn_rabbits)
                return NOT_FOUND;

            // make sure another piece isn't in the way
            if (!(back_bit & (start.bitBoards[myrabbit]
                        | start.bitBoards[Piece.EMPTY])))
                return NOT_FOUND;

            int shortest_goal = NOT_FOUND;
            ulong side_to = neighbors_of(side_neighbors & start.placement[side])
                & start.bitBoards[Piece.EMPTY];
            if (side_to && ((side_to & bneighbors)
                        || !(bneighbors & start.placement[side^1]
                            & ~start.bitBoards[erabbit])
                        || (popcount((bneighbors | back_bit)
                                & start.placement[side]) > 2)))
            {
                if (back_bit & start.bitBoards[myrabbit])
                    return 3;
                shortest_goal = 4;
            }

            int bside_pop = popcount(bneighbors & start.placement[side]);
            ulong side_check = side_neighbors & start.placement[side^1];
            while (side_check)
            {
                ulong sideb = side_check & -side_check;
                side_check ^= sideb;
                bitix sideix = bitindex(sideb);

                ulong sideb_neighbors = neighbors_of(sideb);
                ulong in_pull = 0;
                if (start.lastpiece != Piece.EMPTY
                        && ((1UL << start.lastfrom) & sideb_neighbors)
                        && start.lastpiece + enemyoffset
                        > start.pieces[sideix])
                {
                    in_pull = 1UL << start.lastfrom;
                }

                if (!in_pull && start.strongest[side][sideix] + enemyoffset
                        <= start.pieces[sideix])
                    continue;
                ulong sideb_empties = sideb_neighbors
                    & start.bitBoards[Piece.EMPTY];
                ulong sideb_friendlies = sideb_neighbors
                    & start.placement[side]
                    & ~gbit & ~start.frozen
                    & neighbors_of(start.bitBoards[Piece.EMPTY]);
                if (!in_pull && !sideb_empties && !sideb_friendlies)
                    continue;

                bool gstronger = start.pieces[gix] + enemyoffset
                    > start.pieces[sideix];
                if ((in_pull | sideb_empties | sideb_friendlies) & goal_rank)
                {
                    if (back_bit & start.bitBoards[myrabbit])
                    {
                        if (((sideb_empties & goal_rank) && gstronger)
                                || (in_pull & goal_rank))
                        {
                            if (bside_pop > 1
                                    || !(bneighbors & start.placement[side^1]
                                        & ~start.bitBoards[erabbit]))
                            {
                                return 3;
                            }
                            if ((sideb_empties & bneighbors)
                                    || (neighbors_of(bneighbors
                                            & start.bitBoards[Piece.EMPTY])
                                        & start.placement[side]
                                        & ~start.frozen
                                        & ~back_bit))
                            {
                                shortest_goal = 4;
                            }
                        } else {
                            ulong sfg = sideb_friendlies & goal_rank;
                            bitix sfgix = bitindex(sfg);
                            if (sfg && (gstronger
                                        || (start.pieces[sfgix] + enemyoffset
                                            > start.pieces[sideix]))
                                    && (!(bneighbors & start.placement[side^1]
                                        & ~start.bitBoards[erabbit])
                                        || (bneighbors
                                            & start.placement[side]
                                            & ~gbit)))
                            {
                                shortest_goal = 4;
                            }
                        }
                    }
                    else if ((((sideb_empties & goal_rank)
                            && gstronger)
                                || (in_pull & goal_rank))
                            && (bside_pop > 2
                                || !(bneighbors & start.placement[side^1]
                                    & ~start.bitBoards[erabbit])))
                    {
                        shortest_goal = 4;
                    }
                }
                sideb_empties &= ~goal_rank;
                sideb_friendlies &= ~goal_rank;
                if (back_bit & start.bitBoards[myrabbit])
                {
                    if ((sideb_empties && gstronger)
                            || (in_pull & ~goal_rank))
                    {
                        if (((sideb & start.bitBoards[erabbit])
                                && (bside_pop > 1
                                    || !(bneighbors & start.placement[side^1]
                                        & ~start.bitBoards[erabbit])))
                                || popcount(bneighbors
                                    & start.placement[side]) > 1)
                            return 3;
                        if (neighbors_of(bneighbors
                                    & start.bitBoards[Piece.EMPTY]
                                    & ~sideb_empties)
                                & start.placement[side] & ~start.frozen
                                & ~back_bit)
                        {
                            shortest_goal = 4;
                            continue;
                        }

                    }
                    else if (sideb_friendlies
                            && (bside_pop > 2
                                || ((sideb & start.bitBoards[erabbit])
                                    && !(bneighbors & start.placement[side^1]
                                        & ~start.bitBoards[erabbit])))
                            && (!(sideb_friendlies & start.bitBoards[myrabbit])
                                || (neighbors_of(sideb_friendlies)
                                & start.bitBoards[Piece.EMPTY]
                                & ~backward(sideb_friendlies, side))))
                    {
                        if (gstronger)
                        {
                            shortest_goal = 4;
                            continue;
                        }
                        bitix sfix = bitindex(sideb_friendlies);
                        if (start.pieces[sfix] + enemyoffset
                                > start.pieces[sideix])
                        {
                            shortest_goal = 4;
                            continue;
                        }
                    }
                }
                else if (sideb_empties && gstronger && (bside_pop > 2
                            || ((sideb & start.bitBoards[erabbit])
                                && !(bneighbors & start.placement[side^1]
                                    & ~start.bitBoards[erabbit]))))
                {
                    shortest_goal = 4;
                }
                else if ((sideb_friendlies & start.bitBoards[myrabbit])
                        && gstronger && (!((bneighbors | sideb)
                                & start.placement[side^1]
                                & ~start.bitBoards[erabbit])
                            || popcount(bneighbors & start.placement[side]) > 2))
                {
                    shortest_goal = 4;
                }
            }
            if (shortest_goal != NOT_FOUND)
                return shortest_goal;
            if (back_bit & start.bitBoards[myrabbit])
            {
                ulong side_friendlies = side_neighbors & start.placement[side];
                if (neighbors_of(neighbors_of(side_friendlies)
                            & start.placement[side])
                        & start.bitBoards[Piece.EMPTY]
                        && (back_bit & ~neighbors_of(start.placement[side^1]
                                & ~start.bitBoards[erabbit])
                            || popcount(bneighbors & start.placement[side])
                            > 1))
                {
                    ulong sff = neighbors_of(side_friendlies)
                        & start.placement[side]
                        & neighbors_of(start.bitBoards[Piece.EMPTY]);
                    if (sff & ~start.bitBoards[myrabbit])
                        return 4;
                    while (sff)
                    {
                        ulong sffb = sff & -sff;
                        sff ^= sffb;
                        if (neighbors_of(sffb)
                                & start.bitBoards[Piece.EMPTY]
                                & ~backward(sffb, side))
                            return 4;
                    }
                }
                if ((neighbors_of(side_friendlies)
                            & start.bitBoards[Piece.EMPTY])
                        && (neighbors_of(bneighbors
                                & start.bitBoards[Piece.EMPTY])
                            & start.placement[side]
                            & ~start.frozen & ~back_bit))
                {
                    return 4;
                }
                ulong pushed = neighbors_of(side_friendlies)
                    & start.placement[side^1]
                            & neighbors_of(start.bitBoards[Piece.EMPTY]);
                if ((back_bit & neighbors_of(start.placement[side^1]
                            & ~start.bitBoards[erabbit]))
                        && (popcount(bneighbors & start.placement[side]) < 2))
                    pushed &= bneighbors;
                while (pushed)
                {
                    ulong obit = pushed & -pushed;
                    pushed ^= obit;
                    bitix oix = bitindex(obit);
                    if (start.pieces[oix] >= start.strongest[side][oix]
                            + enemyoffset)
                        continue;
                    ulong pushers = neighbors_of(obit) & side_neighbors
                        & start.placement[side];
                    while (pushers)
                    {
                        ulong pbit = pushers & -pushers;
                        pushers ^= pbit;
                        bitix pix = bitindex(pbit);
                        if (start.pieces[pix] + enemyoffset
                                > start.pieces[oix])
                            return 4;
                    }
                }
            } else {
                // unable to move or push anything to the side so if we're
                // frozen we can't goal
                if (gbit & start.frozen)
                    return NOT_FOUND;

                // if there's a place for us to go we can goal
                ulong to = bneighbors & start.bitBoards[Piece.EMPTY];
                if (to)
                {
                    if (to & ~(TRAPS & ~neighbors_of(start.placement[side])))
                        return 4;
                    if (!(bneighbors & start.placement[side^1]
                                & ~start.bitBoards[erabbit]))
                        return 4;
                }
            }
        }
        return NOT_FOUND;
    }

    private int empty_goal(ulong gbit, Side side)
    {
        const static ulong dist3 = 0x10387CFE7C381000UL;

        bitix gix = bitindex(gbit);
        int enemyoffset;
        Piece myrabbit;
        Piece erabbit;
        ulong back_bit;
        ulong rabbit_mask;
        if (side == Side.WHITE)
        {
            myrabbit = Piece.WRABBIT;
            erabbit = Piece.BRABBIT;
            enemyoffset = 6;
            back_bit = gbit >> 8;
            rabbit_mask = dist3 << (gix-44);
        } else {
            myrabbit = Piece.BRABBIT;
            erabbit = Piece.WRABBIT;
            enemyoffset = -6;
            back_bit = gbit << 8;
            rabbit_mask = dist3 >> (28-gix);
        }

        // check that there is a rabbit within range
        if (!(rabbit_mask & start.bitBoards[myrabbit]))
            return NOT_FOUND;

        ulong bneighbors = neighbors_of(back_bit);
        if (back_bit & start.placement[side^1])
        {
            ulong rabbits = bneighbors & start.bitBoards[myrabbit];
            // check that there is a rabbit close enough and a piece that can
            // potentially pull the opponent out of the way
            if (!(bneighbors & start.bitBoards[myrabbit]))
                return NOT_FOUND;
            bool safe_bb = !((bneighbors | back_bit) & start.placement[side^1]
                        & ~start.bitBoards[erabbit]);
            bitix bix = bitindex(back_bit);
            if (((1UL << start.lastfrom) & bneighbors)
                    && (start.lastpiece + enemyoffset
                        > start.pieces[bix])
                    && (safe_bb
                        || popcount(bneighbors & start.placement[side]) > 1
                        || ((1UL << start.lastfrom) & TRAPS &
                            ~neighbors_of(start.placement[side^1]
                                & ~back_bit))))
            {
                return 3;
            }

            ulong pullers = bneighbors & start.placement[side]
                & ~start.bitBoards[myrabbit]
                & ~start.frozen;
            if (!pullers)
                return NOT_FOUND;
            // check that there really is a strong enough piece to pull
            if (start.strongest[side][bix] + enemyoffset <= start.pieces[bix])
                return NOT_FOUND;

            // check that the rabbit won't freeze when moving into the square
            if (!safe_bb && popcount(bneighbors & start.placement[side]) != 3)
            {
                pullers &= TRAPS & ~neighbors_of(start.placement[side^1]
                        & ~back_bit);
                if (!pullers || (bneighbors & start.placement[side^1]
                            & ~start.bitBoards[erabbit]))
                    return NOT_FOUND;
            }

            while (pullers)
            {
                ulong pbit = pullers & -pullers;
                pullers ^= pbit;
                bitix pix = bitindex(pbit);

                if (start.pieces[pix] + enemyoffset <= start.pieces[bix])
                    continue;

                ulong pn_empties = neighbors_of(pbit)
                    & start.bitBoards[Piece.EMPTY];
                if (!pn_empties)
                    continue;

                if ((rabbits & ~start.frozen)
                        || (neighbors_of(rabbits) & pn_empties))
                    return 4;

                ulong pr = rabbits;
                while (pr)
                {
                    ulong rbit = pr & -pr;
                    pr ^= rbit;

                    if (popcount(neighbors_of(rbit) & start.placement[side^1]
                                & ~start.bitBoards[erabbit]) < 2)
                        return 4;
                }
            }
            // fall through to NOT_FOUND return
        }
        else if (back_bit & start.bitBoards[Piece.EMPTY])
        {
            if ((bneighbors & start.placement[side^1]
                        & ~start.bitBoards[erabbit])
                    && !(bneighbors & start.placement[side]))
            {
                // there are only enemy pieces and maybe empty spaces
                ulong nbn_empties = neighbors_of(bneighbors
                        & start.bitBoards[Piece.EMPTY]
                        & ~gbit);
                ulong prabbits = nbn_empties & start.bitBoards[myrabbit];
                if (!prabbits)
                    return NOT_FOUND;

                ulong unfreezers = nbn_empties & start.placement[side]
                    & ~start.frozen;
                if (popcount(unfreezers | prabbits) < 2)
                {
                    assert(popcount(prabbits) == 1);
                    if (prabbits & start.frozen)
                        return NOT_FOUND;
                    ulong pbn = neighbors_of(prabbits) & bneighbors
                        & start.bitBoards[Piece.EMPTY];
                    unfreezers = neighbors_of(pbn) & start.placement[side]
                        & ~prabbits & (neighbors_of(bneighbors
                                    & start.bitBoards[Piece.EMPTY] & ~pbn
                                    & ~gbit));
                    pbn &= neighbors_of(unfreezers);
                    if (!((bneighbors & start.bitBoards[Piece.EMPTY] & ~pbn
                                & neighbors_of(unfreezers))
                                || popcount(pbn) > 1))
                        return NOT_FOUND;
                    // make sure rabbit doesn't freeze and unfreezer doesn't
                    // get trapped
                    if ((pbn & ~((TRAPS | neighbors_of(start.placement[side^1]
                                        & ~start.bitBoards[erabbit]))
                                & ~neighbors_of(start.placement[side]
                                    & ~unfreezers & ~prabbits)))
                            && ((neighbors_of(unfreezers) & bneighbors
                                    & start.bitBoards[Piece.EMPTY]
                                    & ~pbn) & ~(TRAPS
                                        & ~neighbors_of(start.placement[side]
                                            & ~unfreezers))))
                    {
                        return 4;
                    }
                    return NOT_FOUND;
                }

                while (prabbits)
                {
                    ulong rbit = prabbits & -prabbits;
                    prabbits ^= rbit;

                    if (rbit & start.frozen)
                    {
                        ulong runf = unfreezers & ~rbit;
                        ulong unfsqs = neighbors_of(runf) & neighbors_of(rbit)
                            & bneighbors & start.bitBoards[Piece.EMPTY];
                        if (popcount(unfsqs) > 1)
                        {
                            return 4;
                        }
                        if (!unfsqs)
                            continue;
                        ulong to = bneighbors & start.bitBoards[Piece.EMPTY]
                                    & ~unfsqs & neighbors_of(rbit);
                        if (!to)
                            continue;
                        if ((to & ~((TRAPS | neighbors_of(start.placement[side^1]
                                        & ~start.bitBoards[erabbit]))
                                    & ~neighbors_of(start.placement[side]
                                        & ~rbit)))
                                && ((unfsqs & ~TRAPS)
                                    || popcount(neighbors_of(unfsqs)
                                        & start.placement[side]) > 2))
                        {
                            return 4;
                        }
                        continue;
                    }

                    ulong bn_bits = neighbors_of(rbit) & bneighbors
                        & start.bitBoards[Piece.EMPTY];
                    while (bn_bits)
                    {
                        ulong bnb = bn_bits & -bn_bits;
                        bn_bits ^= bnb;

                        ulong bnb_neighbors = neighbors_of(bnb);
                        if ((unfreezers & ~rbit) && ((popcount(bnb_neighbors
                                    & start.placement[side]) > 1)
                                || ((bnb & ~TRAPS) && !(bnb_neighbors
                                        & start.placement[side^1]
                                        & ~start.bitBoards[erabbit]))))
                        {
                            return 4;
                        }
                        ulong punfreezers = neighbors_of(bnb) & ~rbit
                                    & start.placement[side]
                                    & neighbors_of(bneighbors
                                            & start.bitBoards[Piece.EMPTY]
                                            & ~bnb);
                        assert(!(punfreezers & ~start.frozen));
                        while (punfreezers)
                        {
                            ulong punb = punfreezers & -punfreezers;
                            punfreezers ^= punb;
                            ulong to = bneighbors & ~bnb
                                & neighbors_of(punb);
                            if ((to & ~(TRAPS & ~neighbors_of(
                                            start.placement[side] & ~punb)))
                                    && (bnb & ~(TRAPS & ~neighbors_of(
                                                start.placement[side] & ~rbit
                                                & ~punb)))
                                    && (bnb & ~neighbors_of(
                                            start.placement[side^1]
                                            & ~start.bitBoards[erabbit])))
                            {
                                return 4;
                            }
                        }
                    }
                }
                return NOT_FOUND;
            }
            else if (!(bneighbors & start.placement[side^1]
                        & ~start.bitBoards[erabbit]))
            {
                // no enemy pieces around back bit
                int shortest_goal = NOT_FOUND;
                ulong bn_rabbits = bneighbors & start.bitBoards[myrabbit];
                if (bn_rabbits)
                {
                    if (bn_rabbits & ~start.frozen)
                        return 2;

                    ulong ebnr_neighbors = neighbors_of(neighbors_of(bn_rabbits)
                            & start.bitBoards[Piece.EMPTY] & ~back_bit);
                    if (ebnr_neighbors & start.placement[side] & ~start.frozen)
                        return 3;

                    ulong unfsqs = ebnr_neighbors
                        & start.bitBoards[Piece.EMPTY];
                    unfsqs &= neighbors_of(start.placement[side]
                            & ~start.bitBoards[myrabbit]
                            & ~start.frozen)
                        | neighbors_of(start.bitBoards[myrabbit]
                                & ~start.frozen
                                & ~forward(unfsqs, side));
                    if (unfsqs)
                    {
                        if (unfsqs & ~(TRAPS
                                    | neighbors_of(start.placement[side^1]
                                        & ~start.bitBoards[erabbit])))
                        {
                            shortest_goal = 4;
                        } else {
                            while (unfsqs)
                            {
                                ulong u_bit = unfsqs & -unfsqs;
                                unfsqs ^= u_bit;

                                ulong u_neighbors = neighbors_of(u_bit);
                                ulong fn = u_neighbors & start.placement[side];
                                if (popcount(fn) > 1)
                                {
                                    shortest_goal = 4;
                                    break;
                                }
                                else if (u_bit & ~TRAPS)
                                {
                                    assert (popcount(fn) == 1);
                                    bitix uix = bitindex(u_bit);
                                    bitix fix = bitindex(fn);
                                    if (start.pieces[fix] + enemyoffset >=
                                            start.strongest[side^1][uix])
                                    {
                                        shortest_goal = 4;
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    ulong unfunf = neighbors_of(neighbors_of(ebnr_neighbors
                                    & start.placement[side])
                                & start.bitBoards[Piece.EMPTY] & ~back_bit)
                            & start.placement[side] & ~start.frozen;
                    if (unfunf)
                    {
                        if ((unfunf & ~(start.bitBoards[myrabbit]
                                    & neighbors_of(forward(ebnr_neighbors,
                                            side))))
                                || (neighbors_of(unfunf) & start.bitBoards[Piece.EMPTY]
                                    & forward(ebnr_neighbors, side)))
                        {
                            shortest_goal = 4;
                        }
                    }
                    ulong orn = neighbors_of(bn_rabbits)
                        & start.placement[side^1];
                    if (start.lastpiece != Piece.EMPTY
                            && (neighbors_of(orn) & (1UL << start.lastfrom)))
                    {
                        ulong lfbit = 1UL << start.lastfrom;
                        ulong potentials = orn & neighbors_of(lfbit);
                        while (potentials)
                        {
                            ulong pbit = potentials & -potentials;
                            potentials ^= pbit;
                            bitix pix = bitindex(pbit);
                            if (start.lastpiece + enemyoffset
                                    < start.pieces[pix])
                                continue;
                            if ((bn_rabbits &
                                    ~neighbors_of(start.placement[side^1]
                                        & ~start.bitBoards[erabbit]
                                        & ~pbit))
                                    && ((lfbit & ~bneighbors)
                                        || popcount(bneighbors
                                            & start.placement[side]) > 1
                                        || (lfbit & (TRAPS & ~neighbors_of(
                                                    start.placement[side^1]
                                                    & ~pbit)))))
                            {
                                return 3;
                            }
                        }
                    }
                    if (orn & TRAPS)
                    {
                        ulong ptb = orn & TRAPS;
                        assert (popcount(ptb) == 1);
                        ulong pt_hanging = neighbors_of(ptb)
                            & start.placement[side^1];
                        if ((bn_rabbits & ~neighbors_of(start.placement[side^1]
                                        & ~start.bitBoards[erabbit]
                                        & ~ptb))
                                && popcount(pt_hanging) == 1)
                        {
                            ulong pth_neighbors = neighbors_of(pt_hanging);
                            bitix pthix = bitindex(pt_hanging);
                            if (start.lastpiece != Piece.EMPTY
                                    && (pth_neighbors
                                        & (1UL << start.lastfrom))
                                    && start.lastpiece + enemyoffset
                                    > start.pieces[pthix])
                                return 3;
                            if (start.pieces[pthix]
                                    < start.strongest[side][pthix]
                                    + enemyoffset)
                            {
                                ulong pth_friendlies = pth_neighbors
                                    & start.placement[side]
                                    & ~start.bitBoards[myrabbit]
                                    & ~start.frozen;
                                while (pth_friendlies)
                                {
                                    ulong pthfb = pth_friendlies
                                        & -pth_friendlies;
                                    pth_friendlies ^= pthfb;
                                    bitix pthfix = bitindex(pthfb);
                                    if (start.pieces[pthfix] + enemyoffset
                                            > start.pieces[pthix])
                                    {
                                        shortest_goal = 4;
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    orn &= neighbors_of(start.placement[side]
                                & ~start.bitBoards[myrabbit]
                                & ~start.frozen);
                    while (orn && shortest_goal == NOT_FOUND)
                    {
                        ulong opbit = orn & -orn;
                        orn ^= opbit;
                        bitix opix = bitindex(opbit);
                        if (start.strongest[side][opix] + enemyoffset
                                <= start.pieces[opix])
                            continue;
                        ulong pushers = neighbors_of(opbit)
                            & start.placement[side]
                            & ~start.bitBoards[myrabbit]
                            & ~start.frozen;
                        while (pushers && shortest_goal == NOT_FOUND)
                        {
                            ulong pbit = pushers & -pushers;
                            pushers ^= pbit;
                            bitix pix = bitindex(pbit);
                            if (start.pieces[pix] + enemyoffset
                                    <= start.pieces[opix])
                                continue;
                            ulong op_neighbors = neighbors_of(opbit);
                            ulong op_to = op_neighbors
                                & start.bitBoards[Piece.EMPTY]
                                & ~gbit;
                            if (op_to && ((op_to & ~bneighbors)
                                    || (opbit & start.bitBoards[erabbit])
                                    || (op_to & TRAPS &
                                        ~neighbors_of(start.placement[side^1]
                                            & ~opbit))
                                    || (popcount(bneighbors
                                            & start.placement[side]
                                            & ~pbit) > 1)))
                            {
                                shortest_goal = 4;
                                break;
                            }
                            // can't safely push, how about pull?
                            if (((pbit & ~bneighbors)
                                        || popcount(bneighbors
                                            & start.placement[side]) > 2)
                                    && (neighbors_of(pbit)
                                        & start.bitBoards[Piece.EMPTY]
                                        & ~back_bit)
                                    && !(opbit & start.bitBoards[erabbit]))
                            {
                                ulong pr = bn_rabbits & neighbors_of(opbit);
                                while (pr)
                                {
                                    ulong prbit = pr & -pr;
                                    pr ^= prbit;
                                    if (!(~opbit & (neighbors_of(prbit)
                                                & start.placement[side^1]
                                                & ~start.bitBoards[erabbit])))
                                    {
                                        shortest_goal = 4;
                                        break;
                                    }
                                }
                            }
                        } // while (pushers)
                    } // while (orn)
                } // while (bn_rabbits)
                ulong empty_bn = bneighbors & start.bitBoards[Piece.EMPTY];
                if (empty_bn)
                {
                    ulong ufrabbits = neighbors_of(empty_bn)
                        & start.bitBoards[myrabbit] & ~start.frozen;
                    while (ufrabbits)
                    {
                        ulong ufrb = ufrabbits & -ufrabbits;
                        ufrabbits ^= ufrb;

                        ulong ufr_neighbors = neighbors_of(ufrb);
                        // unfrozen rabbit neighbor and back neighbor
                        ulong ufrnbn = ufr_neighbors & empty_bn;
                        bool trap_only = !(ufrnbn & ~TRAPS);
                        while (ufrnbn)
                        {
                            ulong eufrn = ufrnbn & -ufrnbn;
                            ufrnbn ^= eufrn;

                            ulong eufrn_neighbors = neighbors_of(eufrn);
                            if (popcount(eufrn_neighbors
                                        & start.placement[side]) > 1
                                    || (!(eufrn & TRAPS)
                                        && !(eufrn_neighbors
                                            & start.placement[side^1]
                                            & ~start.bitBoards[erabbit])))
                                return 3;

                            if (shortest_goal != NOT_FOUND)
                                continue;
                            ulong unfreezers = neighbors_of(eufrn_neighbors
                                        & start.bitBoards[Piece.EMPTY]
                                        & ~back_bit)
                                & start.placement[side] & ~start.frozen;
                            // they aren't neighbors one can for sure move first
                            if (unfreezers & ~ufr_neighbors)
                            {
                                shortest_goal = 4;
                                continue;
                            }
                            ulong unfsqs = neighbors_of(unfreezers)
                                & eufrn_neighbors & start.bitBoards[Piece.EMPTY];
                            // can an unfreezer move first
                            if (unfreezers && (!((ufrb & TRAPS)
                                            || (ufr_neighbors
                                                & start.placement[side^1]
                                                & ~start.bitBoards[erabbit]))
                                    || popcount(ufr_neighbors
                                        & start.placement[side]) > 1)
                                    && ((unfsqs & ~TRAPS)
                                        || popcount(neighbors_of(unfsqs)
                                            & start.placement[side]) > 1))
                            {
                                shortest_goal = 4;
                                continue;
                            }
                            if (eufrn & ~TRAPS)
                                unfreezers |= ufr_neighbors & start.placement[side];
                            if (!unfreezers || !(eufrn & ~TRAPS))
                                continue;
                            if (unfreezers & ~((TRAPS
                                        | neighbors_of(start.placement[side^1]
                                            & ~start.bitBoards[erabbit]))
                                        & ~neighbors_of(start.placement[side]
                                            & ~ufrb)))
                            {
                                shortest_goal = 4;
                                continue;
                            }
                            unfreezers &= ~TRAPS;
                            while (unfreezers)
                            {
                                ulong unfbit = unfreezers & -unfreezers;
                                unfreezers ^= unfbit;
                                bitix unfix = bitindex(unfbit);
                                if (start.pieces[unfix] + enemyoffset
                                        >= start.strongest[side^1][unfix])
                                {
                                    shortest_goal = 4;
                                    break;
                                }
                            }
                        }
                        if (shortest_goal != NOT_FOUND)
                            continue;

                        if (trap_only)
                            continue;
                        // unfrozen rabbit friendly neighbor
                        ulong ufrfn = neighbors_of(ufrb)
                            & start.placement[side]
                            & neighbors_of(neighbors_of(empty_bn)
                                    & start.bitBoards[Piece.EMPTY]);
                        while (ufrfn)
                        {
                            ulong ufrfnb = ufrfn & -ufrfn;

                            ulong ufrfn_neighbors = neighbors_of(ufrfnb);
                            if (popcount(ufrfn_neighbors
                                        & start.placement[side]) > 1)
                            {
                                shortest_goal = 4;
                                break;
                            }

                            bitix ufrfnix = bitindex(ufrfnb);
                            if ((ufrfnb & ~TRAPS)
                                    && start.strongest[side^1][ufrfnix] <=
                                    start.pieces[ufrfnix] + enemyoffset)
                            {
                                shortest_goal = 4;
                                break;
                            }

                            ufrfn ^= ufrfnb;
                        }
                    }
                    if (shortest_goal != NOT_FOUND)
                        return shortest_goal;
                    // narrow down to safe squares only
                    empty_bn &= neighbors_of(start.placement[side])
                        | ~(TRAPS | neighbors_of(start.placement[side^1]
                                    & ~start.bitBoards[erabbit]));
                    ulong ebn_neighbors = neighbors_of(empty_bn);
                    ulong potentials = ebn_neighbors
                        & start.bitBoards[Piece.EMPTY]
                        & neighbors_of(start.bitBoards[myrabbit]
                                & ~start.frozen);
                    // if there are any completely safe then we know for sure
                    if (potentials & ~(TRAPS
                                | neighbors_of(start.placement[side^1]
                                    & ~start.bitBoards[erabbit]))
                            & ~neighbors_of(neighbors_of(start.placement[side]
                                    & TRAPS & neighbors_of(empty_bn
                                        & (TRAPS | neighbors_of(
                                                start.placement[side^1]
                                                & ~start.bitBoards[erabbit]))))
                                & start.placement[side]))
                    {
                        return 4;
                    }
                    while (potentials)
                    {
                        ulong pbit = potentials & -potentials;
                        potentials ^= pbit;

                        if ((pbit & (TRAPS
                                        | neighbors_of(start.placement[side^1]
                                            & ~start.bitBoards[erabbit])))
                                && popcount(neighbors_of(pbit)
                                    & start.placement[side]) < 2)
                            continue;
                        ulong prabbits = neighbors_of(pbit)
                            & start.bitBoards[myrabbit] & ~start.frozen;
                        if (prabbits & ~neighbors_of(start.placement[side]
                                    & TRAPS & ebn_neighbors))
                        {
                            return 4;
                        }
                        assert (popcount(prabbits) == 1);
                        ulong prh = neighbors_of(prabbits)
                            & TRAPS & ebn_neighbors;
                        ulong ebn = neighbors_of(prh) & neighbors_of(pbit)
                            & bneighbors;
                        if ((ebn & ~(TRAPS
                                        | neighbors_of(start.placement[side^1]
                                            & ~start.bitBoards[erabbit])))
                                || (neighbors_of(prh) & start.placement[side]
                                    & ~prabbits))
                        {
                            return 4;
                        }
                    }
                    ulong frabbits = ebn_neighbors
                        & start.bitBoards[myrabbit] & start.frozen;
                    while (frabbits)
                    {
                        ulong fr_bit = frabbits & -frabbits;
                        frabbits ^= fr_bit;

                        ulong fr_neighbors = neighbors_of(fr_bit);
                        ulong unusable = empty_bn & fr_neighbors;
                        if (popcount(unusable) == 2)
                            unusable = 0;
                        ulong unfreezers = neighbors_of(fr_neighbors
                                & start.bitBoards[Piece.EMPTY]
                                & ~unusable)
                            & start.placement[side]
                            & ~start.frozen;
                        if (unfreezers)
                        {
                            ulong to = empty_bn
                                & fr_neighbors
                                & start.bitBoards[Piece.EMPTY];
                            ulong safe_to = to & ~(TRAPS
                                    | neighbors_of(start.placement[side^1]
                                        & ~start.bitBoards[erabbit]));
                            if ((safe_to && (neighbors_of(unfreezers)
                                            & start.bitBoards[Piece.EMPTY]
                                            & fr_neighbors & ~safe_to))
                                    || popcount(safe_to) > 1)
                                return 4;
                            while (to)
                            {
                                ulong to_bit = to & -to;
                                ulong to_neighbors = neighbors_of(to_bit);
                                int to_pop = popcount(to_neighbors
                                        & start.placement[side]);
                                if (to_pop > 1)
                                {
                                    if (unfreezers & ~to_neighbors)
                                        return 4;

                                    if (to_pop > 2
                                            && (neighbors_of(unfreezers)
                                                & fr_neighbors
                                                & start.bitBoards[Piece.EMPTY]
                                                & ~to_bit))
                                        return 4;
                                }
                                to ^= to_bit;
                            }
                        }
                    }
                }
                ulong friendly_bn = bneighbors & start.placement[side]
                    & neighbors_of(start.bitBoards[myrabbit])
                    & neighbors_of(start.bitBoards[Piece.EMPTY]);
                while (friendly_bn)
                {
                    ulong fbnbit = friendly_bn & -friendly_bn;
                    friendly_bn ^= fbnbit;

                    ulong fbnb_neighbors = neighbors_of(fbnbit);
                    // make sure the friendly has a place to move to
                    if (!(fbnb_neighbors & start.bitBoards[Piece.EMPTY]
                            & ~back_bit))
                        continue;
                    // make sure rabbit won't freeze once moving into this spot
                    if (popcount(fbnb_neighbors & start.placement[side]) == 1
                            && (fbnb_neighbors & start.placement[side^1]
                                & ~start.bitBoards[erabbit])
                            && !(fbnb_neighbors & start.bitBoards[Piece.EMPTY]
                                & ~(TRAPS
                                    & ~neighbors_of(start.placement[side]
                                        & ~fbnbit))
                                & ~back_bit))
                        continue;

                    ulong prabbits = fbnb_neighbors
                        & start.bitBoards[myrabbit];
                    while (prabbits)
                    {
                        ulong prb = prabbits & -prabbits;

                        ulong prb_neighbors = neighbors_of(prb);
                        if (!((prb & TRAPS) || (prb_neighbors
                                        & start.placement[side^1]
                                        & ~start.bitBoards[erabbit]))
                                || popcount(prb_neighbors
                                    & start.placement[side]) > 1)
                            return 4;
                        prabbits ^= prb;
                    }
                }
            } else {
                // there are a mix of friendly and enemy pieces around back bit
                int shortest_goal = NOT_FOUND;
                ulong bn_rabbits = bneighbors & start.bitBoards[myrabbit];
                if ((bn_rabbits & ~start.frozen)
                        && popcount(bneighbors & start.placement[side]) > 1)
                    return 2;
                while (bn_rabbits)
                {
                    ulong rbit = bn_rabbits & -bn_rabbits;
                    bn_rabbits ^= rbit;

                    if (rbit & ~start.frozen)
                    {
                        // there can only be one empty square besides the goal
                        ulong empty = bneighbors & start.bitBoards[Piece.EMPTY]
                            & ~gbit;
                        if (empty)
                        {
                            ulong fne = neighbors_of(empty)
                                & start.placement[side];
                            while (fne)
                            {
                                ulong fneb = fne & -fne;
                                fne ^= fneb;

                                ulong fneb_neighbors = neighbors_of(fneb);
                                if (fneb & ~start.frozen)
                                {
                                    if (!(fneb_neighbors & rbit))
                                        return 3;
                                    // can the unfreezer move once the rabbit
                                    // moves away
                                    if (popcount(fneb_neighbors
                                            & start.placement[side]) > 1)
                                        return 3;
                                    if (fneb & ~TRAPS)
                                    {
                                        bitix fneix = bitindex(fneb);
                                        if (start.strongest[side^1][fneix] <=
                                                start.pieces[fneix] + enemyoffset
                                                && !(fneb & TRAPS))
                                        {
                                            return 3;
                                        }
                                    }
                                    // can the rabbit move once the unfreezer
                                    // moves away
                                    ulong bad_after_fneb = (TRAPS
                                            | neighbors_of(
                                                start.placement[side^1]
                                                & ~start.bitBoards[erabbit]))
                                        & ~neighbors_of(
                                                start.placement[side]
                                                & ~fneb);
                                    bool safe_rb = !(rbit & bad_after_fneb);
                                    ulong trap_rb = rbit & (TRAPS
                                            & ~neighbors_of(
                                                start.placement[side]
                                                & ~fneb));
                                    ulong e_neighbors = neighbors_of(empty);
                                    ulong fn_rabbit = fneb
                                        & start.bitBoards[myrabbit];
                                    // can the unfreezer move first
                                    if (safe_rb && ((empty & ~TRAPS)
                                                || popcount(e_neighbors
                                                    & start.placement[side])
                                                > 1))
                                    {
                                        return 3;
                                    }
                                    // can the unfreezer goal
                                    bool safe_empty = !(empty
                                            & bad_after_fneb);
                                    if (fn_rabbit && !trap_rb && safe_empty)
                                    {
                                        return 3;
                                    }
                                    if ((safe_rb || fn_rabbit)
                                            && (neighbors_of(e_neighbors
                                                    & start.bitBoards[Piece.EMPTY])
                                                    & start.placement[side]
                                                    & ~start.frozen
                                                    & ~rbit)
                                            && (rbit & ~TRAPS))
                                    {
                                        shortest_goal = 4;
                                    }
                                    else if ((empty & ~(TRAPS
                                                    & ~neighbors_of(
                                                        start.placement[side]
                                                        & ~fneb)))
                                            && (neighbors_of(neighbors_of(rbit)
                                                    & start.bitBoards[Piece.EMPTY])
                                                & start.placement[side]
                                                & ~start.frozen
                                                & ~rbit))
                                    {
                                        shortest_goal = 4;
                                    }
                                }
                                else if (neighbors_of(fneb_neighbors
                                            & start.bitBoards[Piece.EMPTY]
                                            & ~bneighbors)
                                        & start.placement[side]
                                        & ~start.frozen
                                        & ~neighbors_of(rbit)
                                        & ~(start.bitBoards[myrabbit]
                                            & neighbors_of(
                                                forward(fneb, side))))
                                {
                                    shortest_goal = 4;
                                }
                            }
                            ulong ene = neighbors_of(empty)
                                & start.bitBoards[Piece.EMPTY]
                                & neighbors_of(start.placement[side]
                                        & ~start.frozen
                                        & ~rbit);
                            ulong safe_empty = empty & ~(TRAPS
                                    & ~neighbors_of(start.placement[side]));
                            if (ene & ~(TRAPS
                                        | neighbors_of(start.placement[side^1]
                                            & ~start.bitBoards[erabbit])))
                            {
                                shortest_goal = 4;
                            }
                            while (ene && shortest_goal == NOT_FOUND)
                            {
                                ulong ebit = ene & -ene;
                                ene ^= ebit;
                                ulong e_neighbors = neighbors_of(ebit);
                                ulong unfreezers = e_neighbors
                                    & start.placement[side];
                                if (((safe_empty || !(unfreezers & rbit))
                                            && popcount(unfreezers) > 1)
                                        || popcount(unfreezers) > 2)
                                {
                                    shortest_goal = 4;
                                    break;
                                }
                                if (ebit & TRAPS)
                                    continue;
                                assert (unfreezers & ~start.frozen);
                                bitix eix = bitindex(ebit);
                                if (start.strongest[side][eix] + enemyoffset
                                        >= start.strongest[side^1][eix])
                                {
                                    shortest_goal = 4;
                                }
                            }
                        } // if (empty)
                        ulong f_neighbors = neighbors_of(rbit)
                            & start.placement[side];
                        while (f_neighbors)
                        {
                            ulong fnb = f_neighbors & -f_neighbors;
                            f_neighbors ^= fnb;
                            bitix fnix = bitindex(fnb);

                            if (!(fnb & TRAPS)
                                    && (start.strongest[side^1][fnix] <=
                                    start.pieces[fnix] + enemyoffset))
                                return 3;

                            ulong fn_neighbors = neighbors_of(fnb);
                            if (popcount(fn_neighbors & start.placement[side])
                                    > 1)
                                return 3;

                            if (neighbors_of(fn_neighbors
                                        & start.bitBoards[Piece.EMPTY])
                                    & start.placement[side]
                                    & ~start.frozen
                                    & ~fnb
                                    & ~(start.bitBoards[myrabbit]
                                        & neighbors_of(forward(fnb, side))))
                            {
                                shortest_goal = 4;
                            }
                        }
                        ulong bne = bneighbors & start.placement[side^1];
                        if (popcount(bne & ~start.bitBoards[erabbit]) == 1)
                        {
                            ulong bneb = bne & ~start.bitBoards[erabbit];
                            ulong bneb_neighbors = neighbors_of(bneb);
                            bitix bneix = bitindex(bneb);
                            ulong lfbit = 1UL << start.lastfrom;
                            if ((bneb_neighbors & lfbit)
                                    && (start.lastpiece + enemyoffset >
                                    start.pieces[bneix]))
                            {
                                ulong lf_neighbors = neighbors_of(lfbit);
                                if (!(lf_neighbors & rbit)
                                        || (neighbors_of(rbit)
                                            & start.placement[side]))
                                    return 3;
                            }
                            ulong holder = bneb_neighbors
                                & start.placement[side^1];
                            if ((bneb & TRAPS)
                                    && popcount(holder) == 1)
                            {
                                ulong h_neighbors = neighbors_of(holder);
                                bitix hix = bitindex(holder);
                                if ((h_neighbors & lfbit)
                                        && (start.lastpiece + enemyoffset
                                            > start.pieces[hix]))
                                {
                                    return 3;
                                }
                                if ((start.strongest[side][hix] + enemyoffset
                                        > start.pieces[hix])
                                        && (h_neighbors & start.placement[side]
                                            & ~start.frozen))
                                {
                                    ulong hpushers = h_neighbors
                                        & start.placement[side]
                                        & ~start.frozen;
                                    ulong can_push = h_neighbors
                                        & start.bitBoards[Piece.EMPTY];
                                    if (holder & ~start.bitBoards[erabbit])
                                        can_push &= ~bneighbors;
                                    while (hpushers)
                                    {
                                        ulong hpbit = hpushers & -hpushers;
                                        hpushers ^= hpbit;
                                        bitix hpix = bitindex(hpbit);

                                        if (start.pieces[hpix] + enemyoffset
                                                <= start.pieces[hix])
                                            continue;
                                        if (can_push
                                                || (neighbors_of(hpbit)
                                                    & start.bitBoards[Piece.EMPTY]))
                                            return 4;
                                    }
                                }
                            }
                            if (start.strongest[side][bneix] + enemyoffset >
                                    start.pieces[bneix])
                            {
                                ulong bnep = bneb_neighbors
                                    & start.placement[side]
                                    & neighbors_of(start.bitBoards[Piece.EMPTY]
                                            & ~gbit)
                                    & ~start.frozen;
                                while (bnep)
                                {
                                    ulong bnepb = bnep & -bnep;
                                    bitix bnepix = bitindex(bnepb);

                                    if (start.pieces[bnepix] + enemyoffset
                                            > start.pieces[bneix])
                                    {
                                        ulong bnepbn = neighbors_of(bnepb);
                                        if (!(bnepbn & rbit)
                                                || popcount(
                                                    neighbors_of(rbit)
                                                    & start.placement[side])
                                                > 1
                                                || (start.pieces[bnepix]
                                                + enemyoffset >=
                                                start.strongest[side^1][bnepix]
                                                && !(bnepb & TRAPS))
                                                || (popcount(bnepbn
                                                        & start.placement[side])
                                                    > 1))
                                        {
                                            return 4;
                                        }
                                    }
                                    bnep ^= bnepb;
                                }
                            }
                        }
                        if (shortest_goal < NOT_FOUND)
                            return shortest_goal;
                        while (bne)
                        {
                            ulong bneb = bne & -bne;
                            bne ^= bneb;
                            bitix bneix = bitindex(bneb);
                            if (start.strongest[side][bneix] + enemyoffset
                                    <= start.pieces[bneix])
                                continue;

                            ulong bnen = neighbors_of(bneb);
                            // has to be a place to push it to
                            if (!(bnen & start.bitBoards[Piece.EMPTY]
                                        & ~back_bit)
                                    && !(neighbors_of(rbit)
                                        & start.placement[side]
                                        & (TRAPS & ~neighbors_of(start.placement[side] & ~rbit))
                                        & bnen))
                                continue;

                            ulong bnep = bnen & start.placement[side]
                                & ~start.frozen;
                            while (bnep)
                            {
                                ulong bnepb = bnep & -bnep;
                                bitix bnepix = bitindex(bnepb);
                                if (start.pieces[bnepix] + enemyoffset
                                        > start.pieces[bneix])
                                {
                                    ulong bnepbn = neighbors_of(bnepb);
                                    if (!(bnepbn & rbit)
                                            || !((rbit & TRAPS)
                                                | (neighbors_of(rbit)
                                                    & start.placement[side^1]
                                                    & ~start.bitBoards[erabbit]))
                                            || popcount(neighbors_of(rbit)
                                                & start.placement[side])
                                            > 1
                                            || (start.pieces[bnepix]
                                                + enemyoffset >=
                                                start.strongest[side^1][bnepix]
                                                && !(bnepb & TRAPS))
                                            || (popcount(bnepbn
                                                    & start.placement[side])
                                                > 1))
                                    {
                                        return 4;
                                    }
                                }
                                bnep ^= bnepb;
                            }
                        }
                        ulong unfsqs = neighbors_of(rbit)
                            & start.bitBoards[Piece.EMPTY]
                            & neighbors_of(start.placement[side]
                                    & ~start.frozen & ~rbit);
                        if (unfsqs & ~(TRAPS
                                    | neighbors_of(start.placement[side^1]
                                        & ~start.bitBoards[erabbit])))
                            return 4;
                        while (unfsqs)
                        {
                            ulong unfsqb = unfsqs & -unfsqs;
                            unfsqs ^= unfsqb;
                            ulong unfsq_neighbors = neighbors_of(unfsqb);
                            if (popcount(unfsq_neighbors
                                        & start.placement[side]) > 2)
                                return 4;
                            if (unfsqb & TRAPS)
                                continue;
                            bitix unfsqix = bitindex(unfsqb);
                            if (start.strongest[side][unfsqix] + enemyoffset
                                    >= start.strongest[side^1][unfsqix])
                                return 4;
                        }
                        // if we can't get an unfrozen bn rabbit to goal
                        // we won't get any others there either.
                        return NOT_FOUND;
                    } else { // bn rabbit is frozen
                        int bnf_pop = popcount(bneighbors
                                & start.placement[side]);
                        ulong rb_neighbors = neighbors_of(rbit);
                        ulong unfreezers = neighbors_of(rb_neighbors
                            & start.bitBoards[Piece.EMPTY] & ~back_bit)
                            & start.placement[side] & ~start.frozen;
                        if (unfreezers)
                        {
                            // if the rabbit won't freeze once on bn we will goal
                            if ((unfreezers & ~bneighbors) && bnf_pop > 1)
                            {
                                return 3;
                            }
                            ulong ubn = unfreezers & bneighbors;
                            if (ubn)
                            {
                                assert (popcount(ubn) == 1);
                                ulong unfsq = neighbors_of(ubn)
                                    & rb_neighbors
                                    & ~back_bit;
                                // can unfreezer unfreeze then move back
                                if (unfsq & ~((TRAPS
                                                | neighbors_of(
                                                    start.placement[side^1]
                                                    & ~start.bitBoards[erabbit]))
                                            & ~neighbors_of(start.placement[side]
                                                & ~ubn & ~rbit)))
                                {
                                    shortest_goal = 4;
                                }
                                else if (unfsq & ~TRAPS)
                                {
                                    bitix ubix = bitindex(ubn);
                                    bitix unfix = bitindex(unfsq);
                                    if (start.pieces[ubix] + enemyoffset
                                            >= start.strongest[side^1][unfix])
                                    {
                                        shortest_goal = 4;
                                    }
                                }
                                if (shortest_goal == NOT_FOUND)
                                {
                                    ulong ubn_friendlies =  neighbors_of(ubn)
                                        & start.placement[side]
                                        & ~start.frozen;
                                    while (ubn_friendlies)
                                    {
                                        ulong ubnf = ubn_friendlies
                                            & -ubn_friendlies;
                                        ubn_friendlies ^= ubnf;
                                        if (popcount(neighbors_of(ubnf)
                                                    & start.placement[side])
                                                > 1)
                                        {
                                            shortest_goal = 4;
                                            break;
                                        }
                                        if (ubnf & TRAPS)
                                            continue;
                                        bitix ubnfix = bitindex(ubnf);
                                        if (start.pieces[ubnfix] + enemyoffset
                                                >= start.strongest[side^1][ubnfix])
                                        {
                                            shortest_goal = 4;
                                            break;
                                        }
                                    }
                                }
                            }

                            if (neighbors_of(bneighbors & ~gbit
                                        & start.bitBoards[Piece.EMPTY])
                                    & start.placement[side]
                                    & ~start.frozen)
                            {
                                shortest_goal = 4;
                            } else {
                                ulong unfsqs = neighbors_of(unfreezers)
                                    & neighbors_of(rbit)
                                    & start.bitBoards[Piece.EMPTY]
                                    & ~back_bit;
                                if (unfsqs & ~(TRAPS
                                            | neighbors_of(
                                                start.placement[side^1]
                                                & ~start.bitBoards[erabbit])))
                                {
                                    shortest_goal = 4;
                                }
                                while (unfsqs && shortest_goal == NOT_FOUND)
                                {
                                    ulong unfsqb = unfsqs & -unfsqs;
                                    unfsqs ^= unfsqb;

                                    ulong unfsqn = neighbors_of(unfsqb);
                                    if (popcount(unfsqn
                                                & start.placement[side]) > 2)
                                    {
                                        shortest_goal = 4;
                                        break;
                                    }
                                    if (unfsqb & TRAPS)
                                        continue;
                                    bitix usqix = bitindex(unfsqb);
                                    if (start.strongest[side][usqix]
                                            + enemyoffset
                                            >= start.strongest[side^1][usqix])
                                    {
                                        shortest_goal = 4;
                                        break;
                                    }
                                }
                            }
                        }
                        ulong opn = rb_neighbors & start.placement[side^1];
                        ulong fopn = opn & ~start.bitBoards[erabbit];
                        ulong fopn_neighbors = neighbors_of(fopn);
                        ulong is_holder = 0;
                        if (popcount(bneighbors & start.placement[side^1]
                                        & ~start.bitBoards[erabbit]) == 1)
                        {
                            is_holder = neighbors_of(bneighbors
                                    & start.placement[side^1]
                                    & ~start.bitBoards[erabbit]
                                    & TRAPS) & start.placement[side^1];
                            if ((is_holder & fopn) != is_holder)
                                is_holder = 0;
                        }
                        if (popcount(fopn) == 1)
                        {
                            ulong lfbit = 1UL << start.lastfrom;
                            if (start.lastpiece != Piece.EMPTY
                                    && (lfbit & fopn_neighbors)
                                    && (bnf_pop > 1
                                        || is_holder))
                            {
                                bitix fix = bitindex(fopn);
                                if (start.lastpiece + enemyoffset
                                        > start.pieces[fix])
                                    return 3;
                            }
                            ulong holder = fopn_neighbors
                                & start.placement[side^1];
                            if ((fopn & TRAPS)
                                    && popcount(holder) == 1)
                            {
                                bitix hix = bitindex(holder);
                                ulong h_neighbors = neighbors_of(holder);
                                if ((lfbit & h_neighbors)
                                        && start.lastpiece != Piece.EMPTY
                                        && start.lastpiece + enemyoffset
                                        > start.pieces[hix]
                                        && (bnf_pop > 1
                                            || ((holder & bneighbors)
                                                && !(bneighbors
                                                    & start.placement[side^1]
                                                    & ~start.bitBoards[erabbit]
                                                    & ~holder))))
                                {
                                    return 3;
                                }
                                if (start.strongest[side][hix] + enemyoffset
                                        > start.pieces[hix])
                                {
                                    ulong can_push = h_neighbors
                                        & start.bitBoards[Piece.EMPTY]
                                        & ~back_bit;
                                    ulong pushers = h_neighbors
                                        & start.placement[side]
                                        & ~start.bitBoards[myrabbit]
                                        & ~start.frozen;
                                    while (pushers)
                                    {
                                        ulong pbit = pushers & -pushers;
                                        pushers ^= pbit;
                                        bitix pix = bitindex(pbit);
                                        if (start.pieces[pix] + enemyoffset
                                                <= start.pieces[hix])
                                            continue;
                                        if (can_push
                                                && (bnf_pop > 2
                                                    || (holder & bneighbors)))
                                        {
                                            shortest_goal = 4;
                                            break;
                                        }
                                        ulong p_to = neighbors_of(pbit)
                                            & start.bitBoards[Piece.EMPTY];
                                        if (!p_to)
                                            continue;
                                        if (p_to & bneighbors)
                                        {
                                            shortest_goal = 4;
                                            break;
                                        }
                                        if (bnf_pop > 1)
                                        {
                                            shortest_goal = 4;
                                            break;
                                        }
                                        if ((holder & bneighbors)
                                                && !(bneighbors
                                                    & start.placement[side^1]
                                                    & ~start.bitBoards[erabbit]
                                                    & ~holder))
                                        {
                                            shortest_goal = 4;
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                        opn &= neighbors_of(start.placement[side]
                                    & ~start.frozen);
                        if (bnf_pop < 2)
                        {
                            opn &= is_holder;
                        }
                        while (opn && shortest_goal == NOT_FOUND)
                        {
                            ulong obit = opn & -opn;
                            opn ^= obit;
                            bitix oix = bitindex(obit);
                            if (start.pieces[oix]
                                    >= start.strongest[side][oix]
                                    + enemyoffset)
                                continue;
                            ulong o_neighbors = neighbors_of(obit);
                            ulong pushers = o_neighbors & start.placement[side]
                                & ~start.frozen & ~start.bitBoards[myrabbit]
                                & ~bneighbors;
                            while (pushers)
                            {
                                ulong pbit = pushers & -pushers;
                                pushers ^= pbit;
                                bitix pix = bitindex(pbit);
                                if (start.pieces[pix] + enemyoffset
                                        <= start.pieces[oix])
                                    continue;
                                if (o_neighbors
                                        & start.bitBoards[Piece.EMPTY]
                                        & ~gbit)
                                {
                                    shortest_goal = 4;
                                    break;
                                }
                                if (!(rb_neighbors & start.placement[side^1]
                                            & ~start.bitBoards[erabbit]
                                            & ~obit)
                                        && (neighbors_of(pbit)
                                            & start.bitBoards[Piece.EMPTY]))
                                {
                                    shortest_goal = 4;
                                    break;
                                }
                            }
                        }
                        if (bnf_pop < 2)
                            continue;
                        ulong funf = neighbors_of(rb_neighbors
                                        & start.bitBoards[Piece.EMPTY]
                                        & ~back_bit)
                                    & start.placement[side] & ~bneighbors
                                    & start.frozen;
                        if (neighbors_of(neighbors_of(funf)
                                & start.bitBoards[Piece.EMPTY])
                            & start.placement[side] & ~start.frozen
                            & ~(start.bitBoards[myrabbit]
                                    & neighbors_of(forward(funf, side))))
                        {
                            shortest_goal = 4;
                            continue;
                        }
                        ulong unfsqs = neighbors_of(rb_neighbors
                                & start.bitBoards[Piece.EMPTY] & ~back_bit)
                            & start.bitBoards[Piece.EMPTY]
                            & neighbors_of(start.placement[side] & ~start.frozen);
                        if (unfsqs & ~(TRAPS | neighbors_of(start.placement[side^1]
                                    & ~start.bitBoards[erabbit]))
                                & neighbors_of(start.placement[side]
                                    & ~start.bitBoards[myrabbit]
                                    & ~start.frozen))
                        {
                            shortest_goal = 4;
                            continue;
                        }
                        while (unfsqs && shortest_goal == NOT_FOUND)
                        {
                            ulong unfsqb = unfsqs & -unfsqs;
                            unfsqs ^= unfsqb;

                            ulong unfp = neighbors_of(unfsqb)
                                & start.placement[side] & ~start.frozen;
                            if (!(unfp & ~start.bitBoards[myrabbit])
                                    && !(neighbors_of(unfp)
                                        & ~backward(unfp, side)
                                        & unfsqb))
                                continue;
                            if ((unfsqb & ~(TRAPS
                                            | neighbors_of(start.placement[side^1]
                                                & ~start.bitBoards[erabbit])))
                                    || popcount(neighbors_of(unfsqb)
                                        & start.placement[side]) > 1)
                            {
                                shortest_goal = 4;
                                break;
                            }
                            if (unfsqb & TRAPS)
                                continue;
                            assert (popcount(unfp) == 1);
                            bitix unfsqix = bitindex(unfsqb);
                            bitix unfpix = bitindex(unfp);
                            if (start.pieces[unfpix] + enemyoffset
                                    >= start.strongest[side^1][unfsqix])
                            {
                                shortest_goal = 4;
                                break;
                            }
                        }
                    } // frozen bn rabbit
                } // while (bn_rabbits)
                ulong empty_bn = bneighbors & start.bitBoards[Piece.EMPTY]
                    & ~gbit;
                // there can only be one empty
                assert (popcount(empty_bn) < 2);
                if (empty_bn)
                {
                    ulong en = neighbors_of(empty_bn);
                    ulong rabbits = en & start.bitBoards[myrabbit]
                        & ~start.frozen;
                    if (rabbits)
                    {
                        if (popcount(en & start.placement[side]) > 1)
                            return 3;
                        if (!(empty_bn & TRAPS)
                                && !(en & start.placement[side^1]
                                    & ~start.bitBoards[erabbit]))
                            return 3;
                        if (shortest_goal < NOT_FOUND)
                            return shortest_goal;
                        ulong rn = neighbors_of(rabbits);
                        ulong unfreezers = (neighbors_of(en
                                & start.bitBoards[Piece.EMPTY])
                                | rn)
                            & start.placement[side] & ~start.frozen
                            & ~bneighbors;
                        if (!unfreezers)
                            return shortest_goal;
                        if (unfreezers & ~rn)
                        {
                            return 4;
                        }
                        assert (popcount(rabbits) == 1);
                        // can an unfreezer move first?
                        if ((!(rabbits & TRAPS)
                                    || popcount(rn & start.placement[side]) > 1)
                                && (!(rn & start.placement[side^1]
                                    & ~start.bitBoards[erabbit])
                                    || popcount(rn
                                        & start.placement[side]) > 1)
                                && (unfreezers & neighbors_of(en
                                        & start.bitBoards[Piece.EMPTY])))
                        {
                            if (unfreezers & neighbors_of(en
                                        & start.bitBoards[Piece.EMPTY]
                                        & ~(TRAPS
                                            & ~neighbors_of(
                                                start.placement[side]
                                                & ~unfreezers))))
                                return 4;
                            if (popcount(start.placement[side] & neighbors_of(en
                                            & start.bitBoards[Piece.EMPTY]
                                            & TRAPS)) > 1)
                                return 4;
                        }
                        // does the rabbit get trapped if it moves first
                        if (empty_bn & ~TRAPS)
                        {
                            if (unfreezers & ~((TRAPS
                                        | neighbors_of(start.placement[side^1]
                                            & ~start.bitBoards[erabbit]))
                                        & ~neighbors_of(start.placement[side]
                                            & ~rabbits)))
                            {
                                return 4;
                            }
                            // get rid of unfreezers that are captured when the
                            // rabbit moves
                            unfreezers &= ~(TRAPS
                                    & ~neighbors_of(start.placement[side]
                                        & ~rabbits));
                            while (unfreezers)
                            {
                                ulong unfbit = unfreezers & -unfreezers;
                                unfreezers ^= unfbit;
                                bitix unfix = bitindex(unfbit);
                                if (start.pieces[unfix] + enemyoffset
                                        >= start.strongest[side^1][unfix])
                                    return 4;
                            }
                        }
                    }
                    if (shortest_goal != NOT_FOUND)
                        return shortest_goal;
                    bool eb_safe = !(empty_bn & TRAPS)
                        && !(en & start.placement[side^1]
                                & ~start.bitBoards[erabbit]);
                    rabbits = en & start.bitBoards[myrabbit];
                    int fnb_pop = popcount(en & start.placement[side]);
                    if (rabbits
                            && (eb_safe
                                || fnb_pop > 1))
                    {
                        ulong unfreezers = neighbors_of(neighbors_of(rabbits)
                                & start.bitBoards[Piece.EMPTY] & ~empty_bn)
                            & start.placement[side]
                            & ~start.frozen
                            & ~(start.bitBoards[myrabbit]
                                    & neighbors_of(forward(rabbits, side)));
                        if (unfreezers)
                        {
                            if ((unfreezers & ~en)
                                    || popcount(unfreezers) > 1)
                            {
                                return 4;
                            }

                            if (eb_safe || fnb_pop > 2)
                            {
                                if (unfreezers & ~neighbors_of(TRAPS
                                            & bneighbors
                                            & start.placement[side]))
                                {
                                    return 4;
                                }
                                if (popcount(neighbors_of(TRAPS
                                                & bneighbors
                                                & start.placement[side])
                                            & start.placement[side]) > 1)
                                {
                                    return 4;
                                }
                            }
                        }
                    }

                    if (shortest_goal != NOT_FOUND
                            || popcount(en & start.placement[side]) == 0
                            && !eb_safe)
                        return shortest_goal;

                    // narrow it down to en with unfrozen rabbit neighbors
                    ulong safe_sq = ~(TRAPS
                        | neighbors_of(start.placement[side^1]
                                & ~start.bitBoards[erabbit]));
                    en &= neighbors_of(start.bitBoards[myrabbit]
                            & ~start.frozen)
                        & start.bitBoards[Piece.EMPTY];
                    if (en & safe_sq)
                    {
                        return 4;
                    }
                    while (en)
                    {
                        ulong enbit = en & -en;
                        en ^= enbit;
                        if (popcount(neighbors_of(enbit)
                                    & start.placement[side]) > 1)
                            return 4;
                    }
                } // if (empty_bn)
                if ((shortest_goal != NOT_FOUND)
                        || (popcount(bneighbors & start.placement[side]) < 2))
                    return shortest_goal;
                ulong fbn = bneighbors & start.placement[side] & ~start.frozen
                    & neighbors_of(start.bitBoards[myrabbit])
                    & neighbors_of(start.bitBoards[Piece.EMPTY]
                            & ~back_bit);
                while (fbn)
                {
                    ulong fbnb = fbn & -fbn;
                    fbn ^= fbnb;

                    ulong fbn_neighbors = neighbors_of(fbnb);
                    ulong fbn_to = fbn_neighbors & start.bitBoards[Piece.EMPTY]
                        & ~back_bit;
                    // make sure fbnb is safe after piece moves off
                    if (!(fbnb & ~(TRAPS | neighbors_of(start.placement[side^1]
                                        & ~start.bitBoards[erabbit])))
                            && !((fbn_to & ~TRAPS)
                                    || (neighbors_of(fbn_to)
                                        & start.placement[side]
                                        & ~fbnb)
                                    || popcount(fbn_neighbors
                                        & start.placement[side]) > 1))
                        continue;
                    ulong rabbits = fbn_neighbors & start.bitBoards[myrabbit];
                    while (rabbits)
                    {
                        ulong rbit = rabbits & -rabbits;
                        rabbits ^= rbit;

                        ulong rneighbors = neighbors_of(rbit);
                        if (!((rbit & TRAPS)
                                    || (rneighbors & start.placement[side^1]
                                        & ~start.bitBoards[erabbit]))
                                || popcount(rneighbors & start.placement[side])
                                > 1)
                        {
                            return 4;
                        }
                    }
                }
            } // mixed population bneighbors 
        }
        else if (back_bit & start.bitBoards[myrabbit])
        {
            int shortest_goal = NOT_FOUND;
            if (back_bit & ~start.frozen)
            {
                return 1;
            }
            ulong ebn = bneighbors & start.bitBoards[Piece.EMPTY]
                & ~gbit;
            ulong fnebn = neighbors_of(ebn) & start.placement[side]
                & ~back_bit;
            if (fnebn & ~start.frozen)
                return 2;
            ulong obn = bneighbors & start.placement[side^1];
            ulong frbn = obn & ~start.bitBoards[erabbit];
            if (popcount(frbn) == 1)
            {
                ulong lfbit = 1UL << start.lastfrom;
                bitix frix = bitindex(frbn);
                if (start.lastpiece != Piece.EMPTY
                        && (lfbit & neighbors_of(frbn))
                        && start.lastpiece + enemyoffset
                        > start.pieces[frix])
                    return 2;
                ulong holder = neighbors_of(frbn)
                    & start.placement[side^1];
                if ((frbn & TRAPS)
                        && popcount(holder) == 1)
                {
                    bitix hix = bitindex(holder);
                    ulong h_neighbors = neighbors_of(holder);
                    if ((lfbit & h_neighbors)
                            && start.lastpiece != Piece.EMPTY
                            && start.lastpiece + enemyoffset
                            > start.pieces[hix])
                    {
                        return 2;
                    }
                    if (start.strongest[side][hix] + enemyoffset
                            > start.pieces[hix])
                    {
                        ulong can_push = h_neighbors
                            & start.bitBoards[Piece.EMPTY];
                        if (!(holder & start.bitBoards[erabbit]))
                            can_push &= ~bneighbors;
                        ulong pushers = h_neighbors
                            & start.placement[side]
                            & ~start.bitBoards[myrabbit];
                        while (pushers)
                        {
                            ulong pbit = pushers & -pushers;
                            pushers ^= pbit;
                            bitix pix = bitindex(pbit);
                            if (start.pieces[pix] + enemyoffset
                                    <= start.pieces[hix])
                                continue;
                            ulong p_neighbors = neighbors_of(pbit);
                            if (pbit & ~start.frozen)
                            {
                                if (can_push)
                                {
                                    return 3;
                                }
                                ulong pull_to = p_neighbors
                                    & start.bitBoards[Piece.EMPTY];
                                if (pull_to)
                                {
                                    return 3;
                                }
                                if (shortest_goal != NOT_FOUND)
                                    continue;
                                // can a friendly move out of the way
                                ulong p_friendlies = p_neighbors
                                    & start.placement[side];
                                if (start.pieces[pix] + enemyoffset
                                        < start.strongest[side^1][pix]
                                        && popcount(p_friendlies) < 2)
                                    continue;
                                if (p_friendlies & ~start.bitBoards[myrabbit]
                                        & neighbors_of(
                                            start.bitBoards[Piece.EMPTY]))
                                {
                                    shortest_goal = 4;
                                    continue;
                                }
                                p_friendlies &= start.bitBoards[myrabbit];
                                while (p_friendlies)
                                {
                                    ulong prbit = p_friendlies & -p_friendlies;
                                    p_friendlies ^= prbit;
                                    if (neighbors_of(prbit)
                                            & start.bitBoards[Piece.EMPTY]
                                            & ~backward(prbit, side))
                                    {
                                        shortest_goal = 4;
                                        break;
                                    }
                                }
                            }
                            else if (can_push || popcount(p_neighbors
                                        & start.bitBoards[Piece.EMPTY]) > 1)
                            { // can someone step in and unfreeze
                                ulong unfreezers = neighbors_of(p_neighbors
                                        & start.bitBoards[Piece.EMPTY])
                                    & start.placement[side] & ~start.frozen
                                    & ~(start.bitBoards[myrabbit]
                                            & neighbors_of(forward(pbit, side)));
                                if (unfreezers)
                                {
                                    shortest_goal = 4;
                                }
                            }
                        }
                    }
                    ulong pempties = neighbors_of(holder)
                        & start.bitBoards[Piece.EMPTY]
                        & neighbors_of(start.placement[side]
                                & ~start.bitBoards[myrabbit]
                                & ~start.frozen);
                    while (pempties && shortest_goal == NOT_FOUND)
                    {
                        ulong ebit = pempties & -pempties;
                        pempties ^= ebit;
                        bitix eix = bitindex(ebit);
                        if (start.strongest[side][eix] + enemyoffset
                                <= start.pieces[hix])
                            continue;
                        ulong ef_pop = popcount(neighbors_of(ebit)
                                & start.placement[side]);
                        ulong pullers = neighbors_of(ebit)
                            & start.placement[side]
                            & ~start.bitBoards[myrabbit]
                            & ~start.frozen;
                        while (pullers)
                        {
                            ulong pbit = pullers & -pullers;
                            pullers ^= pbit;
                            bitix pix = bitindex(pbit);
                            if (start.pieces[pix] + enemyoffset
                                    > start.pieces[hix]
                                    && (start.pieces[pix] + enemyoffset
                                    > start.strongest[side^1][eix]
                                    || ef_pop > 1))
                            {
                                shortest_goal = 4;
                                break;
                            }
                        }
                    }
                }
            }
            if (obn & TRAPS)
            {
                ulong otr = obn & TRAPS;
                ulong holder = neighbors_of(otr) & start.placement[side^1];
                if (holder == (holder & -holder)) // popcount(holder) == 1
                {
                    bitix hix = bitindex(holder);
                    if (start.strongest[side][hix] + enemyoffset
                            > start.pieces[hix])
                    {
                        ulong h_neighbors = neighbors_of(holder);
                        bool has_fn = popcount(h_neighbors
                                & start.placement[side]) > 1;
                        ulong pushers = h_neighbors & start.placement[side]
                            & ~start.bitBoards[myrabbit] & ~start.frozen;
                        while (pushers)
                        {
                            ulong pbit = pushers & -pushers;
                            pushers ^= pbit;
                            bitix pix = bitindex(pbit);
                            if (start.pieces[pix] + enemyoffset
                                    <= start.pieces[hix])
                                continue;
                            if (has_fn || (start.pieces[pix] + enemyoffset
                                    >= start.strongest[side^1][hix]))
                            {
                                shortest_goal = 4;
                                break;
                            }
                        }
                    }
                }
            }
            ulong fnenfnebn = neighbors_of(neighbors_of(fnebn)
                & start.bitBoards[Piece.EMPTY]) & start.placement[side]
                & ~back_bit & ~fnebn & ~(start.bitBoards[myrabbit]
                        & neighbors_of(forward(fnebn, side)));
            if (fnenfnebn & ~start.frozen)
            {
                return 3;
            }
            ulong enebn = neighbors_of(ebn) & start.bitBoards[Piece.EMPTY];
            while (enebn)
            {
                ulong en_bit = enebn & -enebn;
                enebn ^= en_bit;

                ulong en_neighbors = neighbors_of(en_bit);
                ulong f_neighbors = en_neighbors
                    & start.placement[side];
                int fn_pop = popcount(f_neighbors);
                if (fn_pop > 1 && (f_neighbors & ~start.frozen))
                    return 3;
                bitix enix = bitindex(en_bit);
                while (f_neighbors)
                {
                    ulong fn_bit = f_neighbors & -f_neighbors;
                    f_neighbors ^= fn_bit;

                    bitix fnix = bitindex(fn_bit);
                    bool en_safe = fn_pop > 1;
                    if (!en_safe && !(en_bit & TRAPS))
                    {
                        en_safe = start.pieces[fnix] + enemyoffset >=
                            start.strongest[side^1][enix];
                    }
                    if (fn_bit & ~start.frozen)
                    {
                        if (en_safe || fn_pop > 1)
                            return 3;
                        if (shortest_goal < NOT_FOUND)
                            continue;
                        ulong unfreezers = (neighbors_of(en_neighbors
                                & start.bitBoards[Piece.EMPTY])
                            & start.placement[side] & ~start.frozen)
                            | (neighbors_of(fn_bit) & start.placement[side]);
                        // get rid of rabbits that would have to move backward
                        unfreezers &= ~(start.bitBoards[myrabbit]
                                & neighbors_of(forward(en_bit, side)));
                        // is there a unfreezer that can for sure move second
                        if ((unfreezers & ~neighbors_of(fn_bit))
                                || ((unfreezers &
                                    neighbors_of(start.placement[side]
                                        & ~fn_bit))
                                    && (en_bit & ~TRAPS)))
                        {
                            shortest_goal = 4;
                            continue;
                        }
                        // can the fn move second
                        bool safe_fn = (!(fn_bit & TRAPS)
                                && (start.pieces[fnix] + enemyoffset
                                    >= start.strongest[side^1][fnix]))
                            || popcount(neighbors_of(fn_bit)
                                    & start.placement[side]) > 1;
                        while (unfreezers)
                        {
                            ulong unfb = unfreezers & -unfreezers;
                            unfreezers ^= unfb;

                            // can unf move first
                            ulong safe_to = en_neighbors & neighbors_of(unfb)
                                & start.bitBoards[Piece.EMPTY]
                                    & ~(TRAPS & ~neighbors_of(start.placement[side]
                                            & ~unfb));
                            if (safe_fn && safe_to)
                            {
                                shortest_goal = 4;
                                break;
                            }
                            // unfreezer has to move last
                            if (en_bit & TRAPS)
                                continue;
                            ulong unf_neighbors = neighbors_of(unfb);
                            if (unf_neighbors & start.placement[side]
                                & ~fn_bit)
                            {
                                shortest_goal = 4;
                                break;
                            }
                            if (unfb & TRAPS)
                                continue;
                            bitix unfix = bitindex(unfb);
                            if (start.pieces[unfix] + enemyoffset
                                    >= start.strongest[side^1][unfix])
                            {
                                shortest_goal = 4;
                                break;
                            }
                        }
                    }
                    else if (shortest_goal == NOT_FOUND
                            && (en_safe || fn_pop > 1))
                    { // fn is frozen
                        ulong unfreezers = neighbors_of(neighbors_of(fn_bit)
                                & start.bitBoards[Piece.EMPTY])
                            & start.placement[side] & ~start.frozen;
                        if (unfreezers && (en_safe
                                    || (unfreezers & ~en_neighbors)
                                    || (fn_pop > 2)))
                        {
                            shortest_goal = 4;
                        }
                    }
                } // while (f_neighbors)
                if (shortest_goal != NOT_FOUND || !(fn_pop
                            || !(en_bit & TRAPS)))
                    continue;
                ulong pempties = en_neighbors
                    & start.bitBoards[Piece.EMPTY]
                    & neighbors_of(start.placement[side] & ~start.frozen
                            & ~(start.bitBoards[myrabbit]
                                & neighbors_of(forward(en_bit, side))));
                ulong noop = ~neighbors_of(start.placement[side^1]
                        & ~start.bitBoards[erabbit]);
                if ((pempties & ~TRAPS & noop)
                        && (en_bit & (noop
                            | neighbors_of(start.placement[side]
                                & ~TRAPS))))
                {
                    shortest_goal = 4;
                    continue;
                }
                while (pempties)
                {
                    ulong pe_bit = pempties & -pempties;
                    pempties ^= pe_bit;

                    ulong pe_neighbors = neighbors_of(pe_bit);
                    ulong unfreezers = pe_neighbors & start.placement[side];
                    int f_pop = popcount(unfreezers);
                    unfreezers &= ~start.frozen;
                    bool en_safe = cast(bool)(en_bit & (noop
                            | neighbors_of(start.placement[side]
                                & ~(TRAPS & ~neighbors_of(~unfreezers
                                        & start.placement[side])))));
                    if (!en_safe && (en_neighbors & start.placement[side]))
                    {
                        ulong st_bit = en_neighbors & start.placement[side];
                        assert ((st_bit & TRAPS) && popcount(st_bit) == 1);
                        if (popcount(unfreezers) > 1
                            || (unfreezers & ~neighbors_of(st_bit))
                            || popcount(neighbors_of(st_bit)
                                & start.placement[side]) > 1)
                        {
                            en_safe = true;
                        }
                    }
                    if (!en_safe)
                    {
                        while (unfreezers)
                        {
                            ulong unfbit = unfreezers & -unfreezers;
                            unfreezers ^= unfbit;
                            bitix unfix = bitindex(unfbit);
                            if (start.pieces[unfix] + enemyoffset
                                    >= start.strongest[side^1][enix])
                            {
                                en_safe = true;
                                break;
                            }
                        }
                        if (!en_safe)
                            continue;
                    }
                    if (f_pop > 1)
                    {
                        shortest_goal = 4;
                        break;
                    }
                    if (pe_bit & TRAPS)
                        continue;
                    ulong f_bit = pe_neighbors & start.placement[side];
                    assert (popcount(f_bit) == 1);
                    bitix fix = bitindex(f_bit);
                    bitix peix = bitindex(pe_bit);
                    if (start.pieces[fix] + enemyoffset
                            >= start.strongest[side^1][peix])
                    {
                        shortest_goal = 4;
                        break;
                    }
                }
            } // while (enebn)
            ulong lfbit = 1UL << start.lastfrom;
            while (obn)
            {
                ulong o_bit = obn & -obn;
                obn ^= o_bit;
                bitix oix = bitindex(o_bit);

                ulong o_neighbors = neighbors_of(o_bit);
                // check to see if pieces is getting pulled away
                if ((o_neighbors & lfbit)
                        && start.lastpiece + enemyoffset > start.pieces[oix])
                {
                    // can a piece move in and unfreeze once o_bit is gone
                    ulong fon = o_neighbors & start.placement[side];
                    if ((fon & ~start.frozen)
                            || (fon & ~neighbors_of(start.placement[side^1]
                                    & ~start.bitBoards[erabbit]
                                    & ~o_bit)))
                    {
                        return 3;
                    }
                    while (fon)
                    {
                        ulong fbit = fon & -fon;
                        fon ^= fbit;
                        bitix fix = bitindex(fbit);
                        ulong ofn = neighbors_of(fbit)
                            & start.placement[side^1]
                            & ~start.bitBoards[erabbit]
                            & ~o_bit;
                        while (ofn)
                        {
                            ulong ofbit = ofn & -ofn;
                            bitix ofix = bitindex(ofbit);
                            if (start.pieces[fix] + enemyoffset
                                    < start.pieces[ofix])
                                break;
                            ofn ^= ofbit;
                        }
                        if (!ofn)
                            return 3;
                    }
                }
                if (start.pieces[oix] < start.strongest[side][oix]
                        + enemyoffset)
                {
                    ulong can_push = false;
                    if (o_neighbors & start.bitBoards[Piece.EMPTY])
                        can_push = true;
                    ulong pushers = o_neighbors & start.placement[side]
                        & ~start.bitBoards[myrabbit];
                    while (pushers)
                    {
                        ulong p_bit = pushers & -pushers;
                        pushers ^= p_bit;
                        bitix pix = bitindex(p_bit);

                        if (start.pieces[pix] + enemyoffset <=
                                start.pieces[oix])
                            continue;

                        ulong p_neighbors = neighbors_of(p_bit);
                        if (p_bit & ~start.frozen)
                        {
                            if (can_push)
                                return 3;
                            if (!(~o_bit & frbn))
                            {
                                if (p_neighbors & start.bitBoards[Piece.EMPTY]
                                        & ~gbit)
                                {
                                    return 3;
                                }
                                ulong pf_neighbors = p_neighbors
                                    & start.placement[side]
                                    & neighbors_of(
                                            start.bitBoards[Piece.EMPTY]);
                                if (!(pf_neighbors
                                            & ~start.bitBoards[myrabbit]))
                                {
                                    while (pf_neighbors)
                                    {
                                        ulong pfb = pf_neighbors
                                            & -pf_neighbors;
                                        if (neighbors_of(pfb)
                                                & start.bitBoards[Piece.EMPTY]
                                                & ~backward(pfb, side))
                                            break;
                                        pf_neighbors ^= pfb;
                                    }
                                }
                                if (pf_neighbors)
                                {
                                    if ((p_bit & ~TRAPS)
                                            && start.pieces[pix] + enemyoffset
                                            >= start.strongest[side^1][pix])
                                    {
                                        shortest_goal = 4;
                                        continue;
                                    }
                                    if (popcount(p_neighbors
                                                & start.placement[side]) > 1)
                                    {
                                        shortest_goal = 4;
                                        continue;
                                    }
                                }
                            }
                            // maybe we really can push if there's a friendly
                            // neighbor that can move out of the way
                            ulong clear = neighbors_of(o_bit)
                                & start.placement[side]
                                & ~p_bit & ~back_bit;
                            if (clear)
                            {
                                // can a clear piece for sure move away
                                if (clear & ~start.frozen
                                        & ~start.bitBoards[myrabbit]
                                        & neighbors_of(start.bitBoards[Piece.EMPTY]
                                            & ~gbit))
                                {
                                    shortest_goal = 4;
                                    continue;
                                }
                                // can a clear piece for sure move in if we
                                // pull away
                                ulong pb_empties = neighbors_of(p_bit) &
                                    start.bitBoards[Piece.EMPTY] & ~gbit;
                                if (((clear & ~start.frozen)
                                            && pb_empties)
                                        || (clear & neighbors_of(pb_empties)))
                                {
                                    shortest_goal = 4;
                                    continue;
                                }
                                clear &= ~(~start.frozen
                                        & ~start.bitBoards[myrabbit]);
                                while (clear)
                                {
                                    ulong cbit = clear & -clear;
                                    clear ^= cbit;
                                    // the only unfrozens can be rabbits
                                    if (cbit & ~start.frozen)
                                    {
                                        if (cbit & neighbors_of(
                                                start.bitBoards[Piece.EMPTY]
                                                & ~backward(cbit, side)))
                                        {
                                            shortest_goal = 4;
                                            break;
                                        }
                                        if (cbit & TRAPS)
                                        {
                                            ulong cbholder = neighbors_of(cbit)
                                                & start.placement[side];
                                            ulong cbhn = neighbors_of(cbholder);
                                            if (popcount(cbholder) == 1
                                                    && (cbhn & start.bitBoards[Piece.EMPTY])
                                                    && ((cbholder & ~p_neighbors)
                                                        || (p_neighbors
                                                            & start.placement[side]
                                                            & ~cbholder)
                                                        || start.pieces[pix] + enemyoffset
                                                        >= start.strongest[side^1][pix]))
                                            {
                                                if (cbholder & ~start.bitBoards[myrabbit])
                                                {
                                                    shortest_goal = 4;
                                                    break;
                                                }
                                                if (cbhn & start.placement[Piece.EMPTY]
                                                        & ~backward(cbholder, side))
                                                {
                                                    shortest_goal = 4;
                                                    break;
                                                }
                                            }
                                        }
                                    }
                                    if (!pb_empties)
                                    {
                                        continue;
                                    }
                                    // will it unfreeze after o_bit is pulled
                                    ulong freezers = neighbors_of(cbit)
                                        & start.placement[side^1]
                                        & ~start.bitBoards[erabbit]
                                        & ~o_bit;
                                    bitix cix = bitindex(cbit);
                                    while (freezers)
                                    {
                                        ulong fbit = freezers & -freezers;
                                        bitix fix = bitindex(fbit);
                                        if (start.pieces[cix] + enemyoffset
                                                < start.pieces[fix])
                                            break;
                                        freezers ^= fbit;
                                    }
                                    if (!freezers)
                                    {
                                        shortest_goal = 4;
                                        break;
                                    }
                                }
                            }
                            continue;
                        }
                        ulong unfreezers = p_neighbors
                            & start.bitBoards[Piece.EMPTY]
                            & (neighbors_of(start.placement[side]
                                        & ~start.bitBoards[myrabbit]
                                        & ~start.frozen)
                                    | neighbors_of(start.bitBoards[myrabbit]
                                        & ~start.frozen
                                        & ~neighbors_of(
                                            forward(p_bit, side))));
                        if (unfreezers)
                        {
                            if (can_push)
                            {
                                shortest_goal = 4;
                                continue;
                            }
                            if (!(~o_bit & bneighbors
                                        & start.placement[side^1]
                                        & ~start.bitBoards[erabbit])
                                    && ((p_neighbors
                                        & start.bitBoards[Piece.EMPTY]
                                        & ~unfreezers)
                                        || popcount(unfreezers) > 1))
                            {
                                shortest_goal = 4;
                            }
                            continue;
                        }
                    }
                }
                if (shortest_goal == NOT_FOUND && (o_bit & TRAPS))
                {
                    ulong holder = o_neighbors & start.placement[side^1];
                    if (popcount(holder) == 1)
                    {
                        bitix hix = bitindex(holder);
                        ulong h_neighbors = neighbors_of(holder);
                        ulong can_pull = o_neighbors
                            & start.placement[side];
                        if (!(can_pull & ~start.frozen)
                                && !(can_pull & ~neighbors_of(
                                        start.placement[side^1]
                                        & ~start.bitBoards[erabbit]
                                        & ~o_bit)))
                        {
                            can_pull &= ~start.bitBoards[myrabbit];
                            while (can_pull)
                            {
                                ulong unb = can_pull & -can_pull;
                                bitix unix = bitindex(unb);
                                if (start.strongest[side^1][unix]
                                        > start.pieces[hix])
                                {
                                    can_pull ^= unb;
                                    continue;
                                }
                                ulong freezers = neighbors_of(unb)
                                    & start.placement[side^1]
                                    & ~start.bitBoards[erabbit]
                                    & ~o_bit;
                                while (freezers)
                                {
                                    ulong fbit = freezers & -freezers;
                                    bitix fix = bitindex(fbit);
                                    if (start.pieces[unix] + enemyoffset
                                            < start.pieces[fix])
                                        break;
                                    freezers ^= fbit;
                                }
                                if (!freezers)
                                    break;
                                can_pull ^= unb;
                            }
                        }
                        if (start.lastpiece != Piece.EMPTY
                                && ((1UL << start.lastfrom) & h_neighbors)
                                && can_pull && (start.lastpiece + enemyoffset
                                    > start.pieces[hix]))
                        {
                            return 3;
                        }
                        if (start.strongest[side][hix] + enemyoffset
                                > start.pieces[hix])
                        {
                            int unf_level = start.strongest[side^1][hix];
                            if (popcount(h_neighbors & start.placement[side])
                                    > 1)
                                unf_level = Piece.EMPTY;
                            ulong can_push = h_neighbors
                                & start.bitBoards[Piece.EMPTY];
                            ulong hpushers = neighbors_of(holder)
                                & start.placement[side]
                                & ~start.bitBoards[myrabbit]
                                & ~start.frozen;
                            while (hpushers)
                            {
                                ulong pbit = hpushers & -hpushers;
                                hpushers ^= pbit;
                                bitix pix = bitindex(pbit);
                                if (start.pieces[pix] + enemyoffset
                                        > start.pieces[hix])
                                {
                                    if (can_push
                                            && start.pieces[pix] + enemyoffset
                                            > unf_level)
                                    {
                                        shortest_goal = 4;
                                        break;
                                    }
                                    if (can_pull && (neighbors_of(pbit)
                                                & start.bitBoards[Piece.EMPTY]))
                                    {
                                        shortest_goal = 4;
                                        break;
                                    }
                                }
                            }
                        }
                    }
                }
                if (shortest_goal != NOT_FOUND)
                    continue;
                ulong empties = o_neighbors & start.bitBoards[Piece.EMPTY];
                if (popcount(empties) < 2
                        && (~o_bit & bneighbors
                            & start.placement[side^1]
                            & ~start.bitBoards[erabbit]))
                {
                    ulong pusher = neighbors_of(o_neighbors
                            & start.placement[side] & TRAPS)
                        & start.placement[side];
                    // see if there is a possibility of a pusher that will
                    // open a space up when it moves away
                    if (popcount(pusher) != 1)
                        continue;
                    pusher &= neighbors_of(empties) & ~start.frozen;
                    if (pusher)
                    {
                        bitix pix = bitindex(pusher);
                        bitix eix = bitindex(empties);
                        if (start.pieces[pix] + enemyoffset
                                > start.pieces[oix]
                                && start.pieces[pix] + enemyoffset
                                >= start.strongest[side^1][eix])
                        {
                            shortest_goal = 4;
                        }
                    }
                    continue;
                }
                empties &= neighbors_of(start.placement[side]
                        & ~start.bitBoards[myrabbit]
                        & ~start.frozen);
                while (empties)
                {
                    ulong e_bit = empties & -empties;
                    empties ^= e_bit;
                    bitix eix = bitindex(e_bit);
                    if (start.strongest[side][eix] + enemyoffset <=
                            start.pieces[oix])
                        continue;

                    ulong e_neighbors = neighbors_of(e_bit);
                    ulong pushers = e_neighbors & start.placement[side]
                        & ~start.bitBoards[myrabbit] & ~start.frozen;
                    while (pushers)
                    {
                        ulong p_bit = pushers & -pushers;
                        pushers ^= p_bit;
                        bitix pix = bitindex(p_bit);

                        if (start.pieces[pix] + enemyoffset <=
                                start.pieces[oix])
                            continue;

                        if (((e_bit & ~TRAPS)
                                    && start.strongest[side^1][eix] <=
                                    start.pieces[pix] + enemyoffset)
                                || popcount(e_neighbors
                                    & start.placement[side]) > 1)
                        {
                            shortest_goal = 4;
                            break;
                        }
                    }
                    if (shortest_goal != NOT_FOUND)
                        break;
                }
            }
            while (ebn)
            {
                ulong en_bit = ebn & -ebn;
                ebn ^= en_bit;

                ulong en_neighbors = neighbors_of(en_bit) & ~back_bit;
                ulong f_neighbors = en_neighbors & start.placement[side];
                assert (f_neighbors == (f_neighbors & start.frozen));
                while (f_neighbors)
                {
                    ulong f_bit = f_neighbors & -f_neighbors;
                    f_neighbors ^= f_bit;

                    ulong fb_neighbors = neighbors_of(f_bit);
                    bitix fix = bitindex(f_bit);
                    // all bneighbor opponents should have been dealt with earlier
                    ulong opn = fb_neighbors & start.placement[side^1] & ~bneighbors;
                    ulong fob_neighbors = neighbors_of(start.placement[side] & ~start.frozen);
                    while (opn)
                    {
                        ulong obit = opn & -opn;
                        opn ^= obit;
                        bitix oix = bitindex(obit);
                        ulong pfrs = fb_neighbors
                            & start.placement[side^1]
                            & ~start.bitBoards[erabbit]
                            & ~obit;
                        while (pfrs)
                        {
                            ulong pfbit = pfrs & -pfrs;
                            bitix pfix = bitindex(pfbit);
                            if (start.pieces[fix] + enemyoffset
                                    < start.pieces[pfix])
                                break;
                            pfrs ^= pfbit;
                        }
                        if (!pfrs && (start.lastpiece != Piece.EMPTY)
                                && (neighbors_of(obit)
                                    & (1UL << start.lastfrom))
                                && (start.lastpiece + enemyoffset
                                    > start.pieces[oix]))
                        {
                            return 3;
                        }
                        if (!pfrs && (obit & TRAPS))
                        {
                            ulong holder = neighbors_of(obit)
                                & start.placement[side^1];
                            if (holder == (holder & -holder)) // popcount(holder) == 1
                            {
                                bitix hix = bitindex(holder);
                                if (start.lastpiece != Piece.EMPTY
                                        && (neighbors_of(holder)
                                            & (1UL << start.lastfrom))
                                        && (start.lastpiece + enemyoffset
                                            > start.pieces[hix]))
                                {
                                    return 3;
                                }
                                ulong pushers = neighbors_of(holder)
                                    & start.placement[side] & ~start.frozen
                                    & ~start.bitBoards[myrabbit];
                                while (pushers && shortest_goal == NOT_FOUND)
                                {
                                    ulong pbit = pushers & -pushers;
                                    pushers ^= pbit;
                                    bitix pix = bitindex(pbit);
                                    if (start.pieces[pix] + enemyoffset
                                            <= start.pieces[hix])
                                        continue;
                                    ulong hto = neighbors_of(holder)
                                        & start.bitBoards[Piece.EMPTY];
                                    if ((hto & ~fb_neighbors)
                                            || (hto && start.pieces[fix]
                                                + enemyoffset
                                                >= start.pieces[hix]))
                                    {
                                        shortest_goal = 4;
                                        break;
                                    }
                                    if (neighbors_of(pbit)
                                            & start.bitBoards[Piece.EMPTY])
                                    {
                                        shortest_goal = 4;
                                        break;
                                    }
                                }
                            }
                        }
                        if ((shortest_goal != NOT_FOUND)
                                || (obit & ~fob_neighbors)
                                || (start.pieces[oix] >= start.strongest[side][oix]
                                + enemyoffset))
                            continue;
                        ulong pushers = neighbors_of(obit)
                            & start.placement[side] & ~start.frozen;
                        while (pushers && shortest_goal == NOT_FOUND)
                        {
                            ulong pbit = pushers & -pushers;
                            pushers ^= pbit;
                            bitix pix = bitindex(pbit);
                            if (start.pieces[pix] + enemyoffset
                                    <= start.pieces[oix])
                                continue;
                            if (neighbors_of(obit)
                                    & start.bitBoards[Piece.EMPTY])
                            {
                                assert((neighbors_of(obit)
                                            & start.bitBoards[Piece.EMPTY])
                                        & ~bneighbors);
                                shortest_goal = 4;
                                break;
                            }
                            if (!pfrs && (neighbors_of(pbit)
                                        & start.bitBoards[Piece.EMPTY]
                                        & ~gbit))
                            {
                                shortest_goal = 4;
                                break;
                            }
                        }
                    }
                    if (shortest_goal != NOT_FOUND)
                        continue;
                    ulong pempties = neighbors_of(fb_neighbors &
                            start.bitBoards[Piece.EMPTY])
                    & start.bitBoards[Piece.EMPTY]
                    & neighbors_of(start.placement[side] & ~start.frozen
                            & ~(start.bitBoards[myrabbit]
                                & neighbors_of(forward(fb_neighbors, side))));
                    if (pempties & ~TRAPS
                            & ~neighbors_of(start.placement[side^1]
                                & ~start.bitBoards[erabbit]))
                    {
                        shortest_goal = 4;
                        break;
                    }
                    while (pempties)
                    {
                        ulong pe_bit = pempties & -pempties;
                        pempties ^= pe_bit;

                        ulong pe_neighbors = neighbors_of(pe_bit);
                        if (popcount(pe_neighbors & start.placement[side]) > 1)
                        {
                            shortest_goal = 4;
                            break;
                        }
                        if (pe_bit & TRAPS)
                        {
                            continue;
                        }
                        ulong uf_bit = pe_neighbors & start.placement[side];
                        assert (popcount(uf_bit) == 1);
                        bitix ufix = bitindex(uf_bit);
                        bitix peix = bitindex(pe_bit);
                        if (start.pieces[ufix] + enemyoffset
                                >= start.strongest[side^1][peix])
                        {
                            shortest_goal = 4;
                            break;
                        }
                    }
                } // while (f_neighbors)
                ulong exclusions = ~gbit;
                if ((en_bit & ~TRAPS)
                        || popcount(en_neighbors
                            & start.placement[side^1]) != 1)
                    exclusions &= ~en_bit;
                ulong blockers = en_neighbors
                    & start.placement[side^1]
                    & neighbors_of(start.placement[side] & ~start.frozen)
                    & neighbors_of(start.bitBoards[Piece.EMPTY] & exclusions);
                while (blockers && shortest_goal == NOT_FOUND)
                {
                    ulong b_bit = blockers & -blockers;
                    blockers ^= b_bit;
                    bitix bix = bitindex(b_bit);
                    if (start.pieces[bix]
                            >= start.strongest[side][bix] + enemyoffset)
                        continue;
                    ulong b_neighbors = neighbors_of(b_bit);
                    int bfn_pop = popcount(b_neighbors
                            & start.placement[side]);
                    if ((b_bit & TRAPS) && bfn_pop < 2)
                        continue;
                    ulong pushers = b_neighbors & start.placement[side]
                        & ~start.frozen & ~start.bitBoards[myrabbit];
                    while (pushers)
                    {
                        ulong p_bit = pushers & -pushers;
                        pushers ^= p_bit;
                        bitix pix = bitindex(p_bit);
                        if (start.pieces[pix] + enemyoffset
                                <= start.pieces[bix])
                            continue;
                        if (bfn_pop > 1
                                || (!(b_bit & TRAPS)
                                    && (start.pieces[pix] + enemyoffset >=
                                        start.strongest[side^1][bix])))
                        {
                            shortest_goal = 4;
                            break;
                        }
                    }
                } // while (blockers)
            } // while (ebn)
            if (shortest_goal < NOT_FOUND)
                return shortest_goal;
            if (neighbors_of(neighbors_of(fnenfnebn)
                        & start.bitBoards[Piece.EMPTY]) & start.placement[side]
                    & ~start.frozen)
                return 4;
        } else { // back_bit must be friendly non-rabbit
            assert (back_bit & start.placement[side]
                    & ~start.bitBoards[myrabbit]);
            ulong en = bneighbors & start.bitBoards[Piece.EMPTY]
                & ~gbit;
            ulong rn = bneighbors & start.bitBoards[myrabbit];
            if (!en && !rn)
                return NOT_FOUND;
            bitix bix = bitindex(back_bit);
            ulong safe_en = en & ~(TRAPS
                        & ~neighbors_of(start.placement[side]
                        & ~back_bit));
            int shortest_goal = NOT_FOUND;
            while (rn)
            {
                ulong rn_bit = rn & -rn;
                rn ^= rn_bit;

                ulong rn_neighbors = neighbors_of(rn_bit);
                if ((!(rn_bit & TRAPS)
                        && !(rn_neighbors & start.placement[side^1]
                            & ~start.bitBoards[erabbit]))
                        || popcount(rn_neighbors & start.placement[side]) > 1)
                {
                    if (safe_en
                            || (!(bneighbors & start.placement[side^1]
                                & ~start.bitBoards[erabbit])
                                && en))
                        return 3;
                    assert (!(en & ~TRAPS)); // Any en left is a trap
                    assert (popcount(en) < 2); // which means one at most
                    if (en && (neighbors_of(neighbors_of(en)
                                        & start.bitBoards[Piece.EMPTY])
                                    & start.placement[side] & ~rn_bit
                                    & ~start.frozen))
                    {
                        shortest_goal = 4;
                        continue;
                    }
                    if (en)
                    {
                        ulong unfreezers = neighbors_of(rn_bit)
                            & start.placement[side] & ~back_bit;
                        if (neighbors_of(unfreezers) & start.placement[side]
                                & ~rn_bit)
                        {
                            shortest_goal = 4;
                            continue;
                        }
                        while (unfreezers)
                        {
                            ulong unbit = unfreezers & -unfreezers;
                            unfreezers ^= unbit;
                            if (!(neighbors_of(unbit) & start.placement[side^1]
                                        & ~start.bitBoards[erabbit]))
                            {
                                shortest_goal = 4;
                                break;
                            }
                            // en is a trap so unbit shouldn't be
                            assert (!(unbit & TRAPS));
                            bitix uix = bitindex(unbit);
                            if (start.pieces[uix] + enemyoffset
                                    >= start.strongest[side^1][uix])
                            {
                                shortest_goal = 4;
                                break;
                            }
                        }
                        if (shortest_goal != NOT_FOUND)
                            continue;
                    }
                    ulong clear = bneighbors & start.placement[side] & ~rn_bit
                            & neighbors_of(start.bitBoards[Piece.EMPTY]);
                    if (clear & ~start.bitBoards[myrabbit])
                    {
                        shortest_goal = 4;
                        continue;
                    }
                    while (clear)
                    {
                        ulong cbit = clear & -clear;
                        clear ^= cbit;
                        if (neighbors_of(cbit) & start.bitBoards[Piece.EMPTY]
                                & ~backward(cbit, side))
                        {
                            shortest_goal = 4;
                            break;
                        }
                    }
                    if (shortest_goal != NOT_FOUND)
                        continue;
                    ulong pushed = bneighbors & start.placement[side^1]
                        & neighbors_of(start.bitBoards[Piece.EMPTY]);
                    while (pushed)
                    {
                        ulong p_bit = pushed & -pushed;
                        pushed ^= p_bit;
                        bitix pix = bitindex(p_bit);
                        if (start.pieces[bix] + enemyoffset
                                <= start.pieces[pix])
                            continue;
                        ulong to_bits = neighbors_of(p_bit)
                            & start.bitBoards[Piece.EMPTY];
                        if ((to_bits & ~rn_neighbors)
                                || (to_bits & (TRAPS
                                        & ~neighbors_of(start.placement[side^1]
                                            & ~p_bit)))
                                || (p_bit & start.bitBoards[erabbit])
                                || (popcount(rn_neighbors
                                        & start.placement[side]) > 1))
                        {
                            shortest_goal = 4;
                            break;
                        }
                    }
                    if ((neighbors_of(gbit) & start.bitBoards[Piece.EMPTY])
                            && (!(bneighbors & start.placement[side^1]
                                    & ~start.bitBoards[erabbit])
                                || popcount(bneighbors
                                    & start.placement[side]) > 1))
                    {
                        shortest_goal = 4;
                        continue;
                    }
                } else {
                    ulong frn = neighbors_of(rn_bit) & start.placement[side^1]
                        & ~start.bitBoards[erabbit];
                    if (frn && !(frn & ~(TRAPS & neighbors_of(bneighbors
                                        & start.placement[side^1]))))
                    {
                        assert (popcount(frn) == 1);
                        ulong holder = neighbors_of(frn)
                            & start.placement[side^1];
                        if ((holder == (holder & -holder)) // popcount(holder) == 1
                                && (neighbors_of(holder)
                                    & start.bitBoards[Piece.EMPTY]))
                        {
                            assert (holder & bneighbors);
                            bitix hix = bitindex(holder);
                            if (start.pieces[bix] + enemyoffset
                                    > start.pieces[hix])
                            {
                                shortest_goal = 4;
                                continue;
                            }
                        }
                    }
                    if (!en)
                    {
                        if (bneighbors & start.placement[side] & ~rn_bit
                                & neighbors_of(start.bitBoards[Piece.EMPTY]
                                    & neighbors_of(rn_bit)))
                            shortest_goal = 4;
                        continue;
                    }
                    if (!safe_en && (bneighbors & start.placement[side^1]
                                & ~start.bitBoards[erabbit]))
                    {
                        // can a piece move in and safe the trap and unfreeze
                        // the rabbit
                        if (neighbors_of(neighbors_of(en)
                                    & neighbors_of(rn_bit)
                                    & start.bitBoards[Piece.EMPTY])
                                & start.placement[side] & ~start.frozen
                                & ~rn_bit)
                        {
                            shortest_goal = 4;
                        }
                        continue;
                    }
                    if ((neighbors_of(safe_en) & neighbors_of(rn_bit)
                                & start.bitBoards[Piece.EMPTY])
                            && !(bneighbors & start.placement[side^1]
                                & ~start.bitBoards[erabbit])
                            && (rn_bit & ~TRAPS))
                    {
                        ulong tsqs = safe_en & neighbors_of(neighbors_of(rn_bit)
                                & start.bitBoards[Piece.EMPTY]);
                        if (tsqs & ~(neighbors_of(start.placement[side^1]
                                        & ~start.bitBoards[erabbit])
                                    & ~neighbors_of(start.placement[side]
                                        & ~back_bit)))
                        {
                            shortest_goal = 4;
                        }
                        while (tsqs && shortest_goal == NOT_FOUND)
                        {
                            ulong tbit = tsqs & -tsqs;
                            tsqs ^= tbit;
                            bitix tix = bitindex(tbit);
                            if (start.pieces[bix] + enemyoffset
                                    >= start.strongest[side^1][tix])
                            {
                                shortest_goal = 4;
                            }
                        }
                    }
                    ulong unfreezers = neighbors_of(neighbors_of(rn_bit)
                            & start.bitBoards[Piece.EMPTY])
                        & start.placement[side] & ~start.frozen;
                    if (unfreezers && (!(unfreezers & bneighbors)
                                || popcount(unfreezers) > 1))
                    {
                        shortest_goal = 4;
                    }
                }
            } // while (rn)
            if (shortest_goal != NOT_FOUND
                    || popcount(en) < 2)
                return shortest_goal;
            ulong prn = en & neighbors_of(start.bitBoards[myrabbit]
                & ~start.frozen);
            if (prn)
            {
                if ((prn & ~(TRAPS
                            | neighbors_of(start.placement[side^1]
                                & ~start.bitBoards[erabbit])))
                        && ((en & ~TRAPS & ~prn)
                            || popcount(en & ~TRAPS) > 1
                            || (bneighbors & start.placement[side])))
                {
                    return 4;
                }
                while (prn)
                {
                    ulong prn_bit = prn & -prn;
                    prn ^= prn_bit;

                    if ((prn_bit & (TRAPS
                                    | neighbors_of(start.placement[side^1]
                                        & ~start.bitBoards[erabbit])))
                            && popcount(neighbors_of(prn_bit)
                                & start.placement[side]) < 3)
                        continue;
                    ulong rabbits = neighbors_of(prn_bit)
                        & start.bitBoards[myrabbit]
                        & ~start.frozen;
                    if (popcount(rabbits) > 1)
                        return 4;
                    if (!(bneighbors & start.placement[side^1]
                                & ~start.bitBoards[erabbit])
                            || (en & ~(TRAPS
                                    & ~neighbors_of(start.placement[side]
                                        & ~rabbits & ~back_bit))
                                & ~prn_bit))
                        return 4;
                }
            }
            if (back_bit & ~start.frozen)
            {
                ulong rabbits = neighbors_of(en)
                    & start.bitBoards[myrabbit] & start.frozen;
                en &= neighbors_of(rabbits);
                if (popcount(en) < 2)
                    return NOT_FOUND;
                while (rabbits)
                {
                    ulong rbit = rabbits & -rabbits;
                    rabbits ^= rbit;

                    ulong ernbn = neighbors_of(rbit) & en;
                    if (popcount(ernbn) < 2)
                        continue;
                    ulong safe_ern = ernbn & ~((TRAPS
                                | neighbors_of(start.placement[side^1]
                                    & ~start.bitBoards[erabbit]))
                                & ~neighbors_of(start.placement[side]
                                    & ~rbit & ~back_bit));
                    if (safe_ern)
                    {
                        if ((popcount(safe_ern) > 1)
                                || (en & ~safe_ern & ~TRAPS)
                                || (!(bneighbors & start.placement[side^1]
                                    & ~start.bitBoards[erabbit])))
                            return 4;
                    }
                }
            }
        }
        return NOT_FOUND;
    }

    void find_goals()
    {
        int goal = NOT_FOUND;
        ulong goal_bits = RANK_8;
        while (goal_bits)
        {
            int length = NOT_FOUND;
            ulong gbit = goal_bits & -goal_bits;
            goal_bits ^= gbit;
            if (gbit & start.placement[Side.BLACK])
                length = opponent_goal(gbit, Side.WHITE);
            else if (gbit & start.bitBoards[Piece.EMPTY])
                length = empty_goal(gbit, Side.WHITE);
            else if (gbit & start.placement[Side.WHITE])
                length = friendly_goal(gbit, Side.WHITE);
            if (length)
            {
                goal_squares |= gbit;
                if (length < goal)
                    goal = length;
            }
        }
        shortest[Side.WHITE] = goal;

        goal = NOT_FOUND;
        goal_bits = RANK_1;
        while (goal_bits)
        {
            int length = NOT_FOUND;
            ulong gbit = goal_bits & -goal_bits;
            goal_bits ^= gbit;
            if (gbit & start.placement[Side.WHITE])
                length = opponent_goal(gbit, Side.BLACK);
            else if (gbit & start.bitBoards[Piece.EMPTY])
                length = empty_goal(gbit, Side.BLACK);
            else if (gbit & start.placement[Side.BLACK])
                length = friendly_goal(gbit, Side.BLACK);
            if (length)
            {
                goal_squares |= gbit;
                if (length < goal)
                    goal = length;
            }
        }
        shortest[Side.BLACK] = goal;
    }
}
