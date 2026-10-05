/// Checks capture detection on random positions until it finds an error.
import tango_compat;

import position;
import randompos;
import trap_check;
import trapmoves;

int main(string[] args)
{
    Position pos = new Position();
    StepList steps = StepList.allocate();
    TrapCheck cap_checker = new TrapCheck();
    int pos_count;
    while (true)
    {
        full_position(pos);
        pos_count += 1;
        Stdout.format("{}w", pos_count).newline;
        Stdout(pos.to_long_str()).newline;
        cap_checker.check_captures(pos, pos, steps);
        Position bpos = pos.reverse();
        Stdout.format("{}b", pos_count).newline;
        Stdout(bpos.to_long_str()).newline;
        cap_checker.check_captures(bpos, bpos, steps);
        Position.free(bpos);
        assert (steps.numsteps == 0);
        pos.clear();
    }
}
