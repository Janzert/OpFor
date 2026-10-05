/// Checks goal detection on random positions until it finds an error.
import tango_compat;

import goal_check;
import goalsearch;
import position;
import randompos;

int main(string[] args)
{
    Position pos = new Position();
    GoalSearchDT gs = new GoalSearchDT();
    for (int pos_count = 1; ; pos_count++)
    {
        pos.clear();
        goal_position(pos);
        Stdout.format("{}w", pos_count).newline;
        Stdout(pos.to_long_str()).newline;
        string error = check_goals(pos, gs);
        if (error !is null)
        {
            Stdout(error).newline;
            Stdout("\a").flush;
            return 1;
        }
    }
}
