/// Seeded runs of the fuzzers in tools/: the mobility estimate, capture
/// detection and goal search, each checked against full move generation on
/// random positions.
module fuzz_test;

import std.random : rndGen;

import goal_check;
import goalsearch;
import mobility_check;
import position;
import randompos;
import trap_check;

@("mobility estimate on random positions")
unittest
{
    rndGen.seed(1);
    Position pos = new Position();
    foreach (i; 0 .. 40)
    {
        random_position(pos);
        check_mobility(pos);
        pos.clear();
    }
}

@("capture detection on random positions")
unittest
{
    rndGen.seed(2);
    Position pos = new Position();
    StepList steps = StepList.allocate();
    TrapCheck checker = new TrapCheck();
    foreach (i; 0 .. 10)
    {
        full_position(pos);
        checker.check_captures(pos, pos, steps);
        Position bpos = pos.reverse();
        checker.check_captures(bpos, bpos, steps);
        Position.free(bpos);
        assert(steps.numsteps == 0);
        pos.clear();
    }
}

@("goal search on random positions")
unittest
{
    rndGen.seed(3);
    Position pos = new Position();
    GoalSearchDT gs = new GoalSearchDT();
    foreach (i; 0 .. 20)
    {
        pos.clear();
        goal_position(pos);
        string error = check_goals(pos, gs);
        assert(error is null, error);
    }
}
