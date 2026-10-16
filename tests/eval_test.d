/// Tests of single static evaluation terms.
module eval_test;

import goalsearch;
import logging;
import position;
import staticeval;
import trapmoves;

private StaticEval evaluator(string board)
{
    StaticEval ev = new StaticEval(new Logger(), new GoalSearchDT(),
            new TrapGenerator());
    ev.pos = parse_short_str(Side.WHITE, 4, board);
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
