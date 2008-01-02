
import std.stdio;

import position;

class GoalSearch
{
    Position start;

    int[2] goals_found;
    bitix[8][2] rabbit_location;
    int[8][2] goal_depth;
    int[64] board_depth;

    Side cur_side;
    ulong goal_line;
    int enemy_offset;

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

    void set_side(Side s)
    {
        cur_side = s;
        if (s == Side.WHITE)
        {
            goal_line = RANK_8;
            enemy_offset = 6;
        } else {
            goal_line = RANK_1;
            enemy_offset = 0;
        }
    }

    private ulong expand_forward(ulong bits)
    {
        ulong expanded;
        expanded = (bits & NOT_A_FILE) << 1;
        expanded |= (bits & NOT_H_FILE) >> 1;
        expanded |= (cur_side == Side.WHITE) ? 
                    (bits & NOT_RANK_8) << 8 : (bits & NOT_RANK_1) >> 8;

        return bits | expanded;
    }

    int find_unassisted(ulong rbit, int max_depth)
    {
        // rbit is assumed to be a friendly unfrozen rabbit

        ulong friend_neighbors = neighbors_of(start.placement[cur_side] ^ rbit);
        ulong bad_neighbors = neighbors_of(start.placement[cur_side ^1] ^ start.bitBoards[Piece.WRABBIT+enemy_offset]);
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
        set_side(Side.WHITE);
        goals_found[Side.WHITE] = 0;
        ulong rabbits = start.bitBoards[Piece.WRABBIT] & ~start.frozen;
        while (rabbits)
        {
            bitix rix = msbindex(rabbits);
            ulong rbit = 1UL << rix;
            rabbits ^= rbit;

            int gdepth = find_unassisted(rbit, search_depth);
            board_depth[rix] = gdepth;
            if (gdepth <= search_depth)
            {
                int cur_goal = goals_found[Side.WHITE]++;
                rabbit_location[Side.WHITE][cur_goal] = rix;
                goal_depth[Side.WHITE][cur_goal] = gdepth;
                while (cur_goal > 0 
                        && goal_depth[Side.WHITE][cur_goal] < goal_depth[Side.WHITE][cur_goal-1])
                {
                    rabbit_location[Side.WHITE][cur_goal-1] ^= rabbit_location[Side.WHITE][cur_goal];
                    rabbit_location[Side.WHITE][cur_goal] ^= rabbit_location[Side.WHITE][cur_goal-1];
                    rabbit_location[Side.WHITE][cur_goal-1] ^= rabbit_location[Side.WHITE][cur_goal];
                    goal_depth[Side.WHITE][cur_goal-1] ^= goal_depth[Side.WHITE][cur_goal];
                    goal_depth[Side.WHITE][cur_goal] ^= goal_depth[Side.WHITE][cur_goal-1];
                    goal_depth[Side.WHITE][cur_goal-1] ^= goal_depth[Side.WHITE][cur_goal];
                }
            }
        }

        set_side(Side.BLACK);
        goals_found[Side.BLACK] = 0;
        rabbits = start.bitBoards[Piece.BRABBIT] & ~start.frozen;
        while (rabbits)
        {
            ulong rbit = rabbits & -rabbits;
            rabbits ^= rbit;
            bitix rix = bitindex(rbit);

            int gdepth = find_unassisted(rbit, search_depth);
            board_depth[rix] = gdepth;
            if (gdepth <= search_depth)
            {
                int cur_goal = goals_found[Side.BLACK]++;
                rabbit_location[Side.BLACK][cur_goal] = bitindex(rbit);
                goal_depth[Side.BLACK][cur_goal] = gdepth;
                while (cur_goal > 0 
                        && goal_depth[Side.BLACK][cur_goal] < goal_depth[Side.BLACK][cur_goal-1])
                {
                    rabbit_location[Side.BLACK][cur_goal-1] ^= rabbit_location[Side.BLACK][cur_goal];
                    rabbit_location[Side.BLACK][cur_goal] ^= rabbit_location[Side.BLACK][cur_goal-1];
                    rabbit_location[Side.BLACK][cur_goal-1] ^= rabbit_location[Side.BLACK][cur_goal];
                    goal_depth[Side.BLACK][cur_goal-1] ^= goal_depth[Side.BLACK][cur_goal];
                    goal_depth[Side.BLACK][cur_goal] ^= goal_depth[Side.BLACK][cur_goal-1];
                    goal_depth[Side.BLACK][cur_goal-1] ^= goal_depth[Side.BLACK][cur_goal];
                }
            }
        }
    }
}
