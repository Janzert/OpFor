/// Checks the goal search against goals found by full move generation.
module goal_check;

import tango_compat;

import goalsearch;
import position;

/// Compares gold's shortest goal in pos, found by generating every move,
/// with what gs finds in pos, in pos with the colors reversed, and after
/// each step of the shortest goal. Returns null if they all agree, or else
/// a description of the first disagreement.
string check_goals(Position pos, GoalSearchDT gs)
{
    int shortest_goal = gs.NOT_FOUND;
    StepList shortest_move;
    gs.clear_start();
    PosStore moves = pos.get_moves();
    foreach (Position res; moves)
    {
        if (res.endscore() == 1)
        {
            StepList move = moves.getpos(res);
            int goal_len = 0;
            for (int i=0; i < move.numsteps; i++)
            {
                if (move.steps[i].frombit != INV_STEP
                        && move.steps[i].tobit != INV_STEP)
                    goal_len += 1;
            }
            if (goal_len < shortest_goal)
            {
                shortest_goal = goal_len;
                shortest_move = move;
            }
        }
    }
    if (shortest_goal != gs.NOT_FOUND)
        shortest_move = shortest_move.dup;
    moves.free_items();
    scope (exit)
    {
        if (shortest_move !is null)
            StepList.free(shortest_move);
    }

    string mismatch(Position at, string side, int expected, int found)
    {
        return Format("{}\n{} goal in {}, goal search found {}",
                at.to_long_str(), side, expected, found);
    }

    gs.set_start(pos);
    gs.find_goals();
    int wgoal = gs.shortest[Side.WHITE];
    if (wgoal != shortest_goal)
        return mismatch(pos, "Gold", shortest_goal, wgoal);
    Position bpos = pos.reverse();
    gs.set_start(bpos);
    gs.find_goals();
    int bgoal = gs.shortest[Side.BLACK];
    if (bgoal != wgoal)
    {
        string msg = mismatch(bpos, "Silver", wgoal, bgoal);
        Position.free(bpos);
        return msg;
    }
    Position.free(bpos);
    if (shortest_goal == gs.NOT_FOUND)
        return null;

    Position mpos = pos.dup;
    scope (exit) Position.free(mpos);
    for (int i=0; i < (shortest_goal-1); i++)
    {
        mpos.do_step(shortest_move.steps[i]);
        if (mpos.inpush)
            continue;
        int left = shortest_goal - (i+1);
        gs.set_start(mpos);
        gs.find_goals();
        if (gs.shortest[Side.WHITE] != left)
            return Format("{} step {}\n", shortest_move.to_move_str(pos), i+1)
                ~ mismatch(mpos, "Gold", left, gs.shortest[Side.WHITE]);
        bpos = mpos.reverse();
        gs.set_start(bpos);
        gs.find_goals();
        int found = gs.shortest[Side.BLACK];
        if (found != left)
        {
            string msg = Format("{} step {}\n",
                    shortest_move.to_move_str(pos), i+1)
                ~ mismatch(bpos, "Silver", left, found);
            Position.free(bpos);
            return msg;
        }
        Position.free(bpos);
    }
    return null;
}
