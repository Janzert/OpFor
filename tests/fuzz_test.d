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

@("goal search ignores the mover's last step for the other side")
unittest
{
    // Silver dog d8, silver cat c8, gold rabbit d7. Silver's cat stepping
    // c8-b8 must not let gold pull it back to free d8.
    Position pos = parse_short_str(Side.BLACK, 4,
        "[  cd                       r        rr      R    E   R R R R RRR ]");
    pos.place_piece(Piece.WRABBIT, 1UL << 52); // d7
    GoalSearchDT gs = new GoalSearchDT();
    gs.set_start(pos);
    gs.find_goals();
    assert(gs.shortest[Side.WHITE] == gs.NOT_FOUND);
    StepList steps = StepList.allocate();
    scope (exit) StepList.free(steps);
    pos.get_steps(steps);
    foreach (i; 0 .. steps.numsteps)
    {
        if (steps.steps[i].frombit == (1UL << 61) // c8
                && steps.steps[i].tobit == (1UL << 62)) // b8
        {
            pos.do_step(steps.steps[i]);
            break;
        }
    }
    assert(pos.lastfrom == 61);
    gs.set_start(pos);
    gs.find_goals();
    assert(gs.shortest[Side.WHITE] == gs.NOT_FOUND);
    assert(check_waiting_goal(pos, gs) is null);
}
