
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

    int wgoal;
    int bgoal;

    void set_start(Position pos)
    {
        if (start !is null)
        {
            Position.free(start);
        }
        start = pos.dup;
        wgoal = bgoal = NOT_FOUND;
    }

    void clear_start()
    {
        if (start !is null)
        {
            Position.free(start);
        }
        start = null;
        wgoal = bgoal = NOT_FOUND;
    }

    private ulong backward(ulong bits, Side side)
    {
        return side ? bits >> 8 : bits << 8;
    }

    private int opponent_goal(ulong gbit, Side side)
    {
        ulong gneighbors = neighbors_of(gbit);
        ulong side_friendlies;
        int pieceoffset;
        int enemyoffset;
        if (gbit & RANK_8)
        {
            pieceoffset = 0;
            enemyoffset = 6;
            side_friendlies = (gneighbors & RANK_8)
                & start.placement[Side.WHITE]
                & ~start.frozen;
        } else {
            pieceoffset = 6;
            enemyoffset = -6;
            side_friendlies = (gneighbors & RANK_1)
                & start.placement[Side.BLACK]
                & ~start.frozen;
        }

        // Check that unfrozen friendlies to the side of the opponent on the
        // goal square exist
        if (!side_friendlies)
            return NOT_FOUND;

        bitix gix = bitindex(gbit);
        // check that some friendly neighbor of the goal square is stronger
        // than it. It's a fast check so can give an early exit.
        if (start.pieces[gix] >= start.strongest[side][gix] + enemyoffset)
            return NOT_FOUND;

        ulong pullers = 0;
        while (side_friendlies)
        {
            ulong sfbit = side_friendlies & -side_friendlies;
            side_friendlies ^= sfbit;
            bitix sfix = bitindex(sfbit);

            // Is this piece stronger than the goal square piece
            if (start.pieces[sfix] + enemyoffset <= start.pieces[gix])
                continue;

            ulong empty_neighbors = neighbors_of(sfbit)
                & start.bitBoards[Piece.EMPTY];
            // Is there some place for us to move so we can pull the piece
            // off the goal square
            if (!empty_neighbors)
            {
                // check to see if we can move a rabbit towards goal and 
                // out of the way
                if ((backward(sfbit, side)
                            & start.bitBoards[Piece.WRABBIT + pieceoffset])
                        && (backward(gbit, side)
                            & start.bitBoards[Piece.WRABBIT + pieceoffset]))
                    return 4;
                continue;
            }

            pullers |= sfbit;
        }
        // Can the piece occupying the goal square be pulled off
        if (!pullers)
            return NOT_FOUND;

        ulong back_bit = backward(gbit, side);
        // check for a rabbit on the square back from the goal square
        if (back_bit & start.bitBoards[Piece.WRABBIT + pieceoffset])
        {
            // it's unfrozen
            if (back_bit & ~start.frozen)
                return 3;
            ulong empty_neighbors = neighbors_of(back_bit)
                & start.bitBoards[Piece.EMPTY];
            // it can be unfrozen by the puller
            if (empty_neighbors & neighbors_of(pullers))
                return 3;
            // there is another piece that can come unfreeze it
            if (neighbors_of(empty_neighbors) & ~start.frozen
                    & start.placement[side])
                return 4;
        }
        else if ((back_bit & start.bitBoards[Piece.EMPTY])
                 && (neighbors_of(back_bit)
                     & start.bitBoards[Piece.WRABBIT + pieceoffset]
                     & ~start.frozen))
        {
            return 4;
        }

        return NOT_FOUND;
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
            rabbit_mask = dist2 << (gix-45);
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
                if ((bneighbors & start.placement[side])
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
                        & start.bitBoards[Piece.EMPTY]) & start.placement[side];
                if (unfreezers & ~start.frozen)
                    return 3;

                // if the unfreezers are all frozen check to see if another
                // piece can unfreeze them
                if ((neighbors_of(neighbors_of(unfreezers)
                            & start.bitBoards[Piece.EMPTY]) & ~back_bit)
                    & start.placement[side] & ~start.frozen)
                    return 4;

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
                            || !(rn & start.placement[side^1]
                                & ~start.bitBoards[erabbit]))
                        return 4;
                }
                return NOT_FOUND;
            } else { // back_bit is empty
                assert (back_bit & start.bitBoards[Piece.EMPTY]);
                ulong bn_rabbits = bneighbors & start.bitBoards[myrabbit];
                if (bn_rabbits & ~start.frozen)
                {
                    if (!(bneighbors & start.placement[side^1]
                                & ~start.bitBoards[erabbit])
                            || popcount(bneighbors & start.placement[side]
                                & ~gbit) > 1)
                        return 3;

                    assert (popcount(bn_rabbits) == 1);
                    // one neighbor is the goal, one is the rabbit,
                    // one is the freezing piece so there can only be one empty
                    ulong bn_empty = bneighbors & start.bitBoards[Piece.EMPTY];
                    if (!bn_empty)
                        return NOT_FOUND;

                    ulong unfreezers = neighbors_of(bn_empty)
                        & start.placement[side]
                        & ~start.frozen;
                    // if there is an unfreezer that is not a current neighbor
                    // of the rabbit we can goal for sure
                    ulong rneighbors = neighbors_of(bn_rabbits);
                    if (rneighbors & ~unfreezers)
                        return 4;
                    assert (popcount(unfreezers) == 1);
                    // otherwise we have to check that one of them won't freeze
                    // when the other moves and that the unfreezer won't be
                    // trapped
                    if (!(rneighbors & start.placement[side^1]
                                & ~start.bitBoards[erabbit]))
                        return 4;

                    if (!(unfreezers & TRAPS))
                    {
                        bitix unix = bitindex(unfreezers);
                        if (start.strongest[side^1][unix] <= start.pieces[unix])
                            return 4;
                    }
                }
                return NOT_FOUND;
            }
            assert (false);
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

            int bside_pop = popcount(bneighbors & start.placement[side]);
            ulong side_check = side_neighbors;
            while (side_check)
            {
                ulong sideb = side_check & -side_check;
                side_check ^= sideb;
                bitix sideix = bitindex(sideb);

                if (start.pieces[gix] + enemyoffset > start.pieces[sideix])
                {
                    ulong sideb_empties = neighbors_of(sideb)
                        & start.bitBoards[Piece.EMPTY];
                    if (!sideb_empties)
                        continue;

                    if ((sideb_empties & goal_rank)
                        || (sideb & start.bitBoards[erabbit]))
                    {
                        if (back_bit & start.bitBoards[myrabbit])
                        {
                            if (bside_pop > 1
                                    || !(bneighbors & start.placement[side^1]
                                        & ~start.bitBoards[erabbit]))
                                return 3;

                            ulong empty_bn = bneighbors
                                & start.bitBoards[Piece.EMPTY];
                            if (!(sideb_empties & goal_rank))
                                empty_bn &= ~backward(sideb, side);

                            if (neighbors_of(empty_bn) & ~back_bit
                                    & start.placement[side] & ~start.frozen)
                                return 4;
                        }
                        else if (bside_pop > 1
                                || !(bneighbors & start.placement[side^1]
                                    & ~start.bitBoards[erabbit]))
                        {
                            return 4;
                        }
                    }
                    else if (bside_pop > 1)
                    {
                        if (back_bit)
                            return 3;
                        else
                            return 4;
                    }
                    else if (back_bit)
                    {
                        ulong empty_bn = bneighbors
                            & start.bitBoards[Piece.EMPTY]
                            & ~backward(sideb, side);

                        if (neighbors_of(empty_bn) & ~back_bit
                                & start.placement[side] & ~start.frozen)
                            return 4;
                    }
                }
            }

            // unable to move or push anything to the side so if we're frozen
            // or blocked in we can't goal
            if ((gbit & start.frozen)
                    || (back_bit & start.bitBoards[myrabbit]))
                return NOT_FOUND;

            // if there's a place for us to go we can goal
            if (bneighbors & start.bitBoards[Piece.EMPTY])
                return 4;
        }
        return NOT_FOUND;
    }

    private int empty_goal(ulong gbit, Side side)
    {
        const static ulong dist3 = 0x10387CFE7C3810UL;

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
            rabbit_mask = dist3 << (gix-45);
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
            ulong pullers = bneighbors & start.placement[side]
                & ~start.bitBoards[myrabbit]
                & ~start.frozen;
            ulong rabbits = bneighbors & start.bitBoards[myrabbit];
            // check that there is a rabbit close enough and a piece that can
            // potentially pull the opponent out of the way
            if (!(bneighbors & start.bitBoards[myrabbit])
                    || !pullers)
                return NOT_FOUND;

            bitix bix = bitindex(back_bit);
            // check that there really is a strong enough piece to pull
            if (start.strongest[side][bix] + enemyoffset <= start.pieces[bix])
                return NOT_FOUND;

            // check that the rabbit won't freeze when moving into the square
            if (!((bneighbors | back_bit) & start.placement[side^1]
                        & ~start.bitBoards[erabbit])
                    || popcount(bneighbors & start.placement[side]) != 3)
                return NOT_FOUND;

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
                        & start.bitBoards[Piece.EMPTY]);
                ulong prabbits = nbn_empties & start.bitBoards[myrabbit]
                    & ~start.frozen;
                if (!prabbits)
                    return NOT_FOUND;

                ulong unfreezers = nbn_empties & start.placement[side]
                    & ~start.frozen;
                if (popcount(unfreezers) < 2)
                    return NOT_FOUND;

                while (prabbits)
                {
                    ulong rbit = prabbits & -prabbits;
                    prabbits ^= rbit;

                    ulong bn_bits = neighbors_of(rbit) & bneighbors
                        & start.bitBoards[Piece.EMPTY];
                    while (bn_bits)
                    {
                        ulong bnb = bn_bits & -bn_bits;
                        bn_bits ^= bnb;

                        ulong bnb_neighbors = neighbors_of(bnb);
                        if ((popcount(bnb_neighbors
                                    & start.placement[side]) > 1)
                                || ((bnb & ~TRAPS) && !(bnb_neighbors
                                        & start.placement[side^1]
                                        & ~start.bitBoards[erabbit])))
                            return 4;
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
                            & start.bitBoards[Piece.EMPTY] & ~back_bit
                            & ~bneighbors);
                    if (ebnr_neighbors & start.placement[side] & ~start.frozen)
                        return 3;

                    if (neighbors_of(ebnr_neighbors
                                & start.bitBoards[Piece.EMPTY])
                            & start.placement[side] & ~start.frozen)
                    {
                        shortest_goal = 4;
                    }
                    else if (neighbors_of(neighbors_of(ebnr_neighbors
                                    & start.placement[side])
                                & start.bitBoards[Piece.EMPTY])
                            & start.placement[side] & ~start.frozen)
                    {
                        shortest_goal = 4;
                    }
                }
                ulong empty_bn = bneighbors & start.bitBoards[Piece.EMPTY];
                if (empty_bn)
                {
                    ulong ufrabbits = neighbors_of(empty_bn)
                        & start.bitBoards[myrabbit] & ~start.frozen;
                    while (ufrabbits)
                    {
                        ulong ufrb = ufrabbits & -ufrabbits;
                        ufrabbits ^= ufrb;

                        // unfrozen rabbit neighbor and back neighbor
                        ulong ufrnbn = neighbors_of(ufrb) & bneighbors;
                        while (ufrnbn)
                        {
                            ulong eufrn = ufrnbn & -ufrnbn;

                            ulong eufrn_neighbors = neighbors_of(eufrn);
                            if (popcount(eufrn_neighbors
                                        & start.placement[side]) > 1
                                    || (!(eufrn & TRAPS)
                                        && !(eufrn_neighbors
                                            & start.placement[side^1]
                                            & ~start.bitBoards[erabbit])))
                                return 3;

                            if (neighbors_of(eufrn_neighbors
                                        & start.bitBoards[Piece.EMPTY])
                                    & start.placement[side] & ~start.frozen)
                                shortest_goal = 4;

                            ufrnbn ^= eufrn;
                        }

                        if (shortest_goal < NOT_FOUND)
                            return shortest_goal;

                        // unfrozen rabbit friendly neighbor
                        ulong ufrfn = neighbors_of(ufrb)
                            & start.placement[side];
                        while (ufrfn)
                        {
                            ulong ufrfnb = ufrfn & -ufrfn;

                            ulong ufrfn_neighbors = neighbors_of(ufrfnb);
                            if (popcount(ufrfn_neighbors
                                        & start.placement[side]) > 1)
                                return 4;

                            bitix ufrfnix = bitindex(ufrfnb);
                            if ((ufrfnb & ~TRAPS)
                                    && start.strongest[side^1][ufrfnix] <=
                                    start.pieces[ufrfnix] + enemyoffset)
                                return 4;

                            ufrfn ^= ufrfnb;
                        }
                    }
                    if (shortest_goal < NOT_FOUND)
                        return shortest_goal;
                }
                ulong friendly_bn = bneighbors & start.placement[side]
                    & neighbors_of(start.bitBoards[myrabbit])
                    & neighbors_of(start.bitBoards[Piece.EMPTY]);
                while (friendly_bn)
                {
                    ulong fbnbit = friendly_bn & -friendly_bn;
                    friendly_bn ^= fbnbit;

                    ulong fbnb_neighbors = neighbors_of(fbnbit);
                    // make sure rabbit won't freeze once moving into this spot
                    if (popcount(fbnb_neighbors & start.placement[side]) == 1
                            && (fbnb_neighbors & start.placement[side^1]
                                & ~start.placement[erabbit])
                            && !(fbnb_neighbors & start.bitBoards[Piece.EMPTY]
                                & (TRAPS
                                    & ~neighbors_of(start.placement[side]))))
                        continue;

                    ulong prabbits = fbnb_neighbors
                        & start.bitBoards[myrabbit];
                    while (prabbits)
                    {
                        ulong prb = prabbits & -prabbits;

                        ulong prb_neighbors = neighbors_of(prb);
                        if (!(prb_neighbors & start.placement[side^1]
                                    & ~start.bitBoards[erabbit])
                                || popcount(prb_neighbors
                                    & start.placement[side]) > 1)
                            return 4;
                    }
                }
            } else {
                // there are a mix of friendly and enemy pieces
                int shortest_goal = NOT_FOUND;
                ulong bn_rabbits = bneighbors & start.bitBoards[myrabbit];
                if ((bn_rabbits & ~start.frozen)
                        && popcount(bneighbors & start.placement[side]) > 1)
                    return 2;
                while (bn_rabbits)
                {
                    ulong bnrb = bn_rabbits & -bn_rabbits;
                    bn_rabbits ^= bnrb;

                    if (bnrb & ~start.frozen)
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
                                if (!(fneb_neighbors & bnrb)
                                        || popcount(fneb_neighbors
                                            & start.placement[side]) > 1)
                                    return 3;

                                bitix fneix = bitindex(fneb);
                                if (start.strongest[side^1][fneix] <=
                                        start.pieces[fneix]
                                        && !(fneb & TRAPS))
                                    return 3;

                                if (neighbors_of(fneb_neighbors
                                            & start.bitBoards[Piece.EMPTY])
                                        & start.placement[side]
                                        & ~start.frozen)
                                    shortest_goal = 4;
                            }
                        }
                        ulong f_neighbors = neighbors_of(bnrb)
                            & start.placement[side];
                        while (f_neighbors)
                        {
                            ulong fnb = f_neighbors & -f_neighbors;
                            f_neighbors ^= fnb;
                            bitix fnix = bitindex(fnb);

                            if (!(fnb & TRAPS)
                                    && start.strongest[side^1][fnix] <=
                                    start.pieces[fnix] + enemyoffset)
                                return 3;

                            ulong fn_neighbors = neighbors_of(fnb);
                            if (popcount(fn_neighbors & start.placement[side])
                                    > 1)
                                return 3;

                            if (neighbors_of(fn_neighbors
                                        & start.bitBoards[Piece.EMPTY])
                                    & start.placement[side]
                                    & ~start.frozen)
                                return 4;
                        }
                        if (shortest_goal < NOT_FOUND)
                            return shortest_goal;

                        ulong bne = bneighbors & start.placement[side^1];
                        if (popcount(bne) == 1)
                        {
                            bitix bneix = bitindex(bne);
                            if (start.strongest[side][bneix] + enemyoffset >
                                    start.pieces[bneix])
                            {
                                ulong bnep = neighbors_of(bne)
                                    & start.placement[side]
                                    & neighbors_of(start.bitBoards[Piece.EMPTY])
                                    & ~start.frozen;
                                while (bnep)
                                {
                                    ulong bnepb = bnep & -bnep;
                                    bitix bnepix = bitindex(bnepb);

                                    if (start.pieces[bnepix] + enemyoffset
                                            > start.pieces[bneix])
                                    {
                                        ulong bnepbn = neighbors_of(bnepb);
                                        if (!(bnepbn & bnrb)
                                                || popcount(neighbors_of(bnrb)
                                                    & start.placement[side])
                                                > 1
                                                || (start.pieces[bnepix]
                                                + enemyoffset >=
                                                start.strongest[side^1][bnepix]
                                                && !(bnepb & TRAPS))
                                                || (popcount(bnepbn
                                                        & start.placement[side])
                                                    > 1))
                                            return 4;
                                    }
                                    bnep ^= bnepb;
                                }
                            }
                        }
                        while (bne)
                        {
                            ulong bneb = bne & -bne;
                            bne ^= bneb;

                            ulong bnen = neighbors_of(bneb);
                            // has to be a place to push it to
                            if (!(bnen & start.bitBoards[Piece.EMPTY]
                                        & ~back_bit))
                                continue;
                            // and at least a possible piece to push it
                            ulong bnep = bnen & start.placement[side]
                                & ~start.frozen;
                            if (!bnep)
                                continue;

                            bitix bneix = bitindex(bneb);
                            if (start.strongest[side][bneix] + enemyoffset
                                    <= start.pieces[bneix])
                                continue;
                            while (bnep)
                            {
                                ulong bnepb = bnep & -bnep;
                                bitix bnepix = bitindex(bnepb);
                                if (start.pieces[bnepix] + enemyoffset
                                        > start.pieces[bneix])
                                {
                                    ulong bnepbn = neighbors_of(bnepb);
                                    if (!(bnepbn & bnrb)
                                            || popcount(neighbors_of(bnrb)
                                                & start.placement[side])
                                            > 1
                                            || (start.pieces[bnepix]
                                                + enemyoffset >=
                                                start.strongest[side^1][bnepix]
                                                && !(bnepb & TRAPS))
                                            || (popcount(bnepbn
                                                    & start.placement[side])
                                                > 1))
                                        return 4;
                                }
                                bnep ^= bnepb;
                            }
                        }
                        // if we can't get an unfrozen bn rabbit to goal
                        // we won't get any others there either.
                        return NOT_FOUND;
                    } else { // bn rabbit is frozen
                        ulong unfreezers = neighbors_of(neighbors_of(bnrb)
                            & start.bitBoards[Piece.EMPTY])
                            & start.placement[side] & ~start.frozen;
                        if (!unfreezers)
                            continue;
                        // if the rabbit won't freeze once on bn we will goal
                        if (popcount(bneighbors & start.placement[side]) > 1)
                            return 3;

                        if (neighbors_of(bneighbors
                                    & start.bitBoards[Piece.EMPTY])
                                & start.placement[side]
                                & ~start.frozen)
                        {
                            shortest_goal = 4;
                        } else {
                            ulong unfsqs = neighbors_of(unfreezers)
                                & neighbors_of(bnrb);
                            while (unfsqs)
                            {
                                ulong unfsqb = unfsqs & -unfsqs;
                                unfsqs ^= unfsqb;

                                ulong unfsqn = neighbors_of(unfsqb);
                                if (!(unfsqb & TRAPS)
                                        && !(unfsqn & start.placement[side^1]
                                            & ~start.bitBoards[erabbit]))
                                {
                                    shortest_goal = 4;
                                    break;
                                }
                                if (popcount(unfsqn
                                            & start.placement[side]) > 2)
                                {
                                    shortest_goal = 4;
                                    break;
                                }

                                bitix unfix = bitindex(unfsqn & unfreezers);
                                bitix unfsqix = bitindex(unfsqb);
                                if (start.pieces[unfix] + enemyoffset
                                        > start.strongest[side^1][unfsqix])
                                {
                                    shortest_goal = 4;
                                    break;
                                }
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
                        ulong unfreezers = neighbors_of(en
                                & start.bitBoards[Piece.EMPTY])
                            & start.placement[side] & ~start.frozen;
                        if (!unfreezers)
                            return NOT_FOUND;
                        if (unfreezers & ~rn)
                            return 4;
                        assert (popcount(unfreezers) == 1);
                        assert (popcount(rabbits) == 1);
                        if (!(rabbits & TRAPS)
                                && !(rn & start.placement[side^1]
                                    & ~start.bitBoards[erabbit]))
                            return 4;
                        ulong unfn = neighbors_of(unfreezers);
                        if (popcount(rn & start.placement[side]) > 1
                                || popcount(unfn & start.placement[side]) > 1)
                            return 4;
                        bitix unfix = bitindex(unfreezers);
                        if (!(unfreezers & TRAPS)
                                && start.pieces[unfix] + enemyoffset
                                >= start.strongest[side^1][unfix])
                            return 4;
                    }
                    bool eb_safe = !(empty_bn & TRAPS)
                        && !(en & start.placement[side^1]
                                & ~start.bitBoards[erabbit]);
                    rabbits = en & start.bitBoards[myrabbit];
                    if (rabbits
                            && (eb_safe
                                || popcount(en & start.placement[side]) > 1))
                    {
                        ulong unfreezers = neighbors_of(neighbors_of(rabbits)
                                & start.bitBoards[Piece.EMPTY])
                            & start.placement[side]
                            & ~start.frozen;
                        if (unfreezers)
                        {
                            if (unfreezers & ~en)
                                return 4;
                            assert (popcount(unfreezers) == 1);

                            if (eb_safe)
                                return 4;
                        }
                    }

                    if (popcount(en & start.placement[side]) == 0
                            && !eb_safe)
                        return NOT_FOUND;

                    // narrow it down to safe en
                    ulong safe_sq = neighbors_of(start.placement[side])
                        | (~TRAPS & ~neighbors_of(start.placement[side^1]
                                    & ~start.bitBoards[erabbit]));
                    en &= safe_sq;
                    ulong eenn = neighbors_of(en)
                        & start.bitBoards[Piece.EMPTY]
                        & neighbors_of(start.bitBoards[myrabbit]
                                & ~start.frozen)
                        & safe_sq;
                    if (eenn)
                        return 4;
                }
                if (popcount(bneighbors & start.placement[side]) < 2)
                    return NOT_FOUND;
                ulong fbn = bneighbors & start.placement[side] & ~start.frozen
                    & neighbors_of(start.bitBoards[myrabbit])
                    & neighbors_of(start.bitBoards[Piece.EMPTY]
                            & ~back_bit);
                while (fbn)
                {
                    ulong fbnb = fbn & -fbn;
                    fbn ^= fbnb;

                    ulong fbn_neighbors = neighbors_of(fbnb);
                    ulong fbn_to = fbn_neighbors & start.bitBoards[Piece.EMPTY];
                    if (!((fbn_to & ~TRAPS)
                            || (neighbors_of(fbn_to) & start.placement[side])
                            || popcount(fbn_neighbors & start.placement[side])
                            > 1))
                        continue;
                    ulong rabbits = fbn_neighbors & start.bitBoards[myrabbit];
                    while (rabbits)
                    {
                        ulong rbit = rabbits & -rabbits;
                        rabbits ^= rbit;

                        ulong rneighbors = neighbors_of(rbit);
                        if (!((rbit & TRAPS)
                                    || (rneighbors & start.placement[side^1]
                                        & start.bitBoards[erabbit]))
                                || popcount(rneighbors & start.placement[side])
                                > 1)
                            return 4;
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
            ulong fnebn = neighbors_of(ebn) & start.placement[side];
            if (fnebn & ~start.frozen)
                return 2;
            ulong fnenfnebn = neighbors_of(neighbors_of(fnebn)
                & start.bitBoards[Piece.EMPTY]) & start.placement[side];
            if (fnenfnebn & ~start.frozen)
                return 3;
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
                        if (unfreezers & ~neighbors_of(fn_bit))
                        {
                            shortest_goal = 4;
                            continue;
                        }
                        if (unfreezers)
                        {
                            assert (popcount(unfreezers) == 1);
                            if (!(en_bit & TRAPS)
                                    && ((start.pieces[fnix] + enemyoffset
                                            >= start.strongest[side^1][fnix]
                                            && !(fn_bit & TRAPS))
                                        || popcount(f_neighbors
                                            & start.placement[side])
                                        > 1))
                            {
                                shortest_goal = 4;
                                continue;
                            }
                            if (!((neighbors_of(unfreezers) & en_neighbors)
                                        & TRAPS))
                            {
                                bitix unfix = bitindex(unfreezers);
                                if ((start.pieces[unfix] + enemyoffset
                                            >= start.strongest[side^1][unfix]
                                            && !(unfreezers & TRAPS))
                                        || popcount(neighbors_of(unfreezers)
                                            & start.placement[side]) > 1)
                                {
                                    shortest_goal = 4;
                                    continue;
                                }
                            }
                        }
                    }
                    else if (shortest_goal == NOT_FOUND
                            && (en_safe || fn_pop > 1))
                    { // fn is frozen
                        ulong unfreezers = neighbors_of(neighbors_of(fn_bit)
                                & start.bitBoards[Piece.EMPTY])
                            & start.placement[side] & ~start.frozen;
                        if (en_safe || (unfreezers & ~en_neighbors)
                                || fn_pop > 2)
                            shortest_goal = 4;
                    }
                } // while (f_neighbors)
                if (shortest_goal < NOT_FOUND || !(fn_pop
                            || !((en_bit & TRAPS)
                                || en_neighbors & start.placement[side^1]
                                & ~start.bitBoards[erabbit])))
                    continue;
                ulong pempties = neighbors_of(en_bit)
                    & start.bitBoards[Piece.EMPTY]
                    & neighbors_of(start.placement[side] & ~start.frozen);
                if (pempties & ~TRAPS & ~neighbors_of(start.placement[side^1]
                            & ~start.bitBoards[erabbit]))
                {
                    shortest_goal = 4;
                    continue;
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
                        continue;
                    ulong f_bit = pe_neighbors & start.placement[side];
                    assert (popcount(f_bit) == 1);
                    bitix fix = bitindex(f_bit);
                    bitix peix = bitindex(pe_bit);
                    if (start.pieces[fix] >= start.strongest[side^1][peix])
                    {
                        shortest_goal = 4;
                        break;
                    }
                }
            } // while (enebn)
            if (shortest_goal < NOT_FOUND)
                return shortest_goal;
            while (ebn)
            {
                ulong en_bit = ebn & -ebn;
                ebn ^= en_bit;

                ulong en_neighbors = neighbors_of(en_bit) & ~back_bit;
                ulong f_neighbors = en_neighbors & start.placement[side];
                assert (f_neighbors == (f_neighbors & start.frozen));
                while (f_neighbors && shortest_goal == NOT_FOUND)
                {
                    ulong f_bit = f_neighbors & -f_neighbors;
                    f_neighbors ^= f_bit;

                    ulong pempties = neighbors_of(neighbors_of(f_bit) &
                            start.bitBoards[Piece.EMPTY])
                    & start.bitBoards[Piece.EMPTY]
                    & neighbors_of(start.placement[side] & ~start.frozen);
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
                        if (start.pieces[ufix] >= start.strongest[side^1][peix])
                        {
                            shortest_goal = 4;
                            break;
                        }
                    }
                } // while (f_neighbors)

                ulong blockers = en_neighbors
                    & start.placement[side^1]
                    & neighbors_of(start.placement[side] & ~start.frozen)
                    & neighbors_of(start.bitBoards[Piece.EMPTY] & ~en_bit);
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
            ulong en = bneighbors & start.bitBoards[Piece.EMPTY];
            ulong rn = bneighbors & start.bitBoards[myrabbit];
            if (!en && !rn)
                return NOT_FOUND;
            bool safe_en = cast(bool)(en & ~(TRAPS
                        & ~neighbors_of(start.placement[side]
                        & ~back_bit)));
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
                    if (safe_en)
                        return 3;
                    if (en && (neighbors_of(neighbors_of(en)
                                        & start.bitBoards[Piece.EMPTY])
                                    & start.placement[side] & ~rn_bit
                                    & ~start.frozen))
                        return 4;
                    bitix bix = bitindex(back_bit);
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
                                || (p_bit & start.bitBoards[erabbit])
                                || (popcount(rn_neighbors
                                        & start.placement[side]) > 1))
                            return 4;
                    }
                }
                if (!safe_en)
                    continue;
                ulong unfreezers = neighbors_of(neighbors_of(rn_bit)
                        & start.bitBoards[Piece.EMPTY])
                    & start.placement[side] & ~start.frozen;
                if (unfreezers && (!(unfreezers & bneighbors)
                        || popcount(unfreezers) > 1))
                    return 4;
            }
        }
        return NOT_FOUND;
    }

    void find_goals()
    {
        wgoal = NOT_FOUND;
        ulong goal_bits = RANK_8;
        while (goal_bits)
        {
            int length = NOT_FOUND;
            ulong gbit = goal_bits & -goal_bits;
            goal_bits ^= gbit;
            if ((wgoal > 3) && (gbit & start.placement[Side.BLACK]))
                length = opponent_goal(gbit, Side.WHITE);
            else if (gbit & start.bitBoards[Piece.EMPTY])
                length = empty_goal(gbit, Side.WHITE);
            else if (wgoal > 2)
                length = friendly_goal(gbit, Side.WHITE);
            if (length < wgoal)
                wgoal = length;
        }

        bgoal = NOT_FOUND;
        goal_bits = RANK_1;
        while (goal_bits)
        {
            int length = NOT_FOUND;
            ulong gbit = goal_bits & -goal_bits;
            goal_bits ^= gbit;
            if ((bgoal > 3) && (gbit & start.placement[Side.WHITE]))
                length = opponent_goal(gbit, Side.BLACK);
            else if (gbit & start.bitBoards[Piece.EMPTY])
                length = empty_goal(gbit, Side.BLACK);
            else if (bgoal > 2)
                length = friendly_goal(gbit, Side.BLACK);
            if (length < bgoal)
                bgoal = length;
        }
    }
}
