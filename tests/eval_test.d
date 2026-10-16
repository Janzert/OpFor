/// Tests of single static evaluation terms.
module eval_test;

import goalsearch;
import logging;
import position;
import staticeval;
import trapmoves;

private StaticEval evaluator(string board, int steps = 4,
        Side side = Side.WHITE)
{
    StaticEval ev = new StaticEval(new Logger(), new GoalSearchDT(),
            new TrapGenerator());
    ev.pos = parse_short_str(side, steps, board);
    ev.material_values(population(ev.pos));
    ev.trap_safety();
    return ev;
}

@("piece on trap counts every occupied trap")
unittest
{
    // Gold cat on c3 and dog on f3, each with a rabbit beside it.
    enum both = "[r  e   r" ~ "        " ~ "        " ~ "        "
        ~ "        " ~ "  C  D  " ~ "  R  R  " ~ "   E    ]";
    enum mirror = "[r  e   r" ~ "        " ~ "        " ~ "        "
        ~ "        " ~ "  D  C  " ~ "  R  R  " ~ "   E    ]";
    enum cat_only = "[r  e   r" ~ "        " ~ "        " ~ "        "
        ~ "        " ~ "  C     " ~ "  R  R  " ~ "   E    ]";
    enum dog_only = "[r  e   r" ~ "        " ~ "        " ~ "        "
        ~ "        " ~ "     D  " ~ "  R  R  " ~ "   E    ]";
    int score = evaluator(both).on_trap();
    assert(score == evaluator(mirror).on_trap());
    assert(score < evaluator(cat_only).on_trap());
    assert(score < evaluator(dog_only).on_trap());
}

private int goal_threat(string board)
{
    StaticEval ev = evaluator(board, 3);
    ev.goals.set_start(ev.pos);
    ev.goals.find_goals();
    assert(ev.goals.shortest[Side.WHITE] == 4);
    assert(ev.goals.shortest[Side.BLACK] == 1);
    return ev.goal_threat();
}

@("goal threat doesn't depend on file order")
unittest
{
    // Gold can reach goal on d8 to f8, silver on b1 to e1. The file-flipped
    // board must score the same.
    enum board = "[e   M   " ~ "  H     " ~ "E       " ~ "  C R   "
        ~ "r      h" ~ "h     R " ~ "m r  R H" ~ "      R ]";
    enum mirror = "[   M   e" ~ "     H  " ~ "       E" ~ "   R C  "
        ~ "h      r" ~ " R     h" ~ "H R  r m" ~ " R      ]";
    assert(goal_threat(board) == goal_threat(mirror));
}

private int capture_threat(string board)
{
    StaticEval ev = evaluator(board, 3, Side.BLACK);
    int pop = population(ev.pos);
    return ev.static_trap_eval(Side.WHITE, pop, ev.material_values(pop));
}

@("capture threats don't depend on the order captures are found")
unittest
{
    // Gold threatens a silver horse and several silver rabbits, two of
    // them equally near capture. The frozen one must be among those
    // counted, whichever order they are found in.
    enum board = "[rE      " ~ "  Rh Re " ~ " R    Rr" ~ " mr H   "
        ~ "  h r  R" ~ "      Hr" ~ "   M   c" ~ "  D     ]";
    enum mirror = "[      Er" ~ " eR hR  " ~ "rR    R " ~ "   H rm "
        ~ "R  r h  " ~ "rH      " ~ "c   M   " ~ "     D  ]";
    int score = capture_threat(board);
    assert(score > 0);
    assert(score == capture_threat(mirror));
}
