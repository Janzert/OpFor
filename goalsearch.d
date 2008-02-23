
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
