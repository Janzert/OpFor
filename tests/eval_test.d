/// Tests of single static evaluation terms.
module eval_test;

import goalsearch;
import logging;
import position;
import staticeval;
import trapmoves;
import unit_threaded.runner.attrs : Tags;

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

private double goal_threat(string board)
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

private double goal_threat(string board, int steps, Side side)
{
    StaticEval ev = evaluator(board, steps, side);
    ev.goals.set_start(ev.pos);
    ev.goals.find_goals();
    return ev.goal_threat();
}

@("goal threat doesn't depend on colour")
unittest
{
    // Both sides have a goal threat, gold's worth about 166 here and
    // silver's about 366. Adding them must give the same result whichever
    // is added first, so the colour-flipped board scores the exact
    // opposite.
    enum board = "[er    rr" ~ "m  R   d" ~ "   h    " ~ " H h Er "
        ~ " R      " ~ "    C   " ~ "r    H  " ~ "  D    M]";
    enum flipped = "[  d    m" ~ "R    h  " ~ "    c   " ~ " r      "
        ~ " h H eR " ~ "   H    " ~ "M  r   D" ~ "ER    RR]";
    double score = goal_threat(board, 2, Side.WHITE);
    assert(score < -150);
    assert(score == -goal_threat(flipped, 2, Side.BLACK));
}

private int capture_threat(string board)
{
    StaticEval ev = evaluator(board, 3, Side.BLACK);
    int pop = population(ev.pos);
    return ev.static_trap_eval(Side.WHITE, pop, ev.material_values(pop));
}

@("logged eval matches static eval")
unittest
{
    // The goal threat board above, where gold's goal threat counts.
    enum board = "[e   M   " ~ "  H     " ~ "E       " ~ "  C R   "
        ~ "r      h" ~ "h     R " ~ "m r  R H" ~ "      R ]";
    StaticEval ev = evaluator(board, 3);
    ev.goals.set_start(ev.pos);
    ev.goals.find_goals();
    assert(ev.goal_threat() != 0);
    Position pos = ev.pos;
    assert(ev.logged_eval(pos) == evaluator(board, 3).static_eval(pos));
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

// It changes a tunable, so it runs apart from the other tests (tests/ut.d).
@("this turn's captures use their own weight")
@Tags("tunables")
unittest
{
    import tunables : NOW_VICTIM_PER;

    // Gold, to move with 4 steps, can push the silver cat on d3 into c3.
    enum board = "[       e" ~ "       r" ~ "        " ~ "        "
        ~ "        " ~ "   cD   " ~ "        " ~ "E      R]";
    int threat()
    {
        StaticEval ev = evaluator(board);
        int pop = population(ev.pos);
        return ev.static_trap_eval(Side.WHITE, pop, ev.material_values(pop));
    }
    double saved = NOW_VICTIM_PER;
    scope (exit) NOW_VICTIM_PER = saved;
    int base = threat();
    assert(base > 0);
    NOW_VICTIM_PER = saved * 2;
    int doubled = threat();
    assert(doubled >= 2 * base - 1 && doubled <= 2 * base + 1);
}

@("rabbit strength doesn't depend on file order")
unittest
{
    // A gold rabbit on c3 and its mirror on f3.
    enum board = "[e       " ~ "        " ~ "        " ~ "        "
        ~ "        " ~ "  R     " ~ "        " ~ "        ]";
    enum mirror = "[       e" ~ "        " ~ "        " ~ "        "
        ~ "        " ~ "     R  " ~ "        " ~ "        ]";
    assert(evaluator(board).rabbit_strength()
            == evaluator(mirror).rabbit_strength());
}

@("frozen piece power doesn't depend on colour")
unittest
{
    // A gold camel on d4 frozen by a silver elephant on e4, with a silver
    // horse on a8 far enough away that its power isn't clamped, and the
    // same with colours and ranks swapped.
    enum board = "[h      r" ~ "        " ~ "        " ~ "        "
        ~ "   Me   " ~ "        " ~ "        " ~ "       R]";
    enum flipped = "[       r" ~ "        " ~ "        " ~ "   mE   "
        ~ "        " ~ "        " ~ "        " ~ "H      R]";
    StaticEval ev = evaluator(board);
    assert(ev.pos.frozen != 0);
    assert(ev.piece_strength()
            == -evaluator(flipped, 4, Side.BLACK).piece_strength());
}

@("strong rabbit bonus grows with its support")
unittest
{
    // A gold rabbit on c6 with a gold cat behind it, close (c5) or one
    // square further (c4). Neither gives full support, so both get part
    // of the bonus, the closer cat more.
    enum close = "[        " ~ "        " ~ "  R     " ~ "  C     "
        ~ "        " ~ "        " ~ "        " ~ "       e]";
    enum far = "[        " ~ "        " ~ "  R     " ~ "        "
        ~ "  C     " ~ "        " ~ "        " ~ "       e]";
    StaticEval ev_close = evaluator(close);
    StaticEval ev_far = evaluator(far);
    ev_close.rweak_w = 0;
    ev_far.rweak_w = 0;
    double s_close = ev_close.rabbit_strength();
    double s_far = ev_far.rabbit_strength();
    assert(s_far > 0);
    assert(s_close > s_far);
}
