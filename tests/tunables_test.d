/// Tests of the tunable constants: their defaults rebuild the tables the
/// evaluation had before they were tunable, and options set and reset them.
module tunables_test;

import tunables;

@("derived tables match the original constants")
unittest
{
    reset();
    assert(BOTH_SAFE == [-5, 5]);
    assert(WHITE_SAFE == [20, 80]);
    assert(BLACK_SAFE == [-80, -20]);
    assert(NORABBIT_FILE == [[1, 1, 1, 2, 3, 5, 7, 0], [0, -7, -5, -3, -2, -1, -1, -1]]);
    assert(NORABBIT_ADJ == [[1, 1, 1, 2, 2, 4, 4, 0], [0, -4, -4, -2, -2, -1, -1, -1]]);
    assert(OPEN_FILE == [[2, 2, 2, 3, 10, 20, 40, 0], [0, -40, -20, -10, -3, -2, -2, -2]]);
    assert(OPEN_ADJ == [[2, 2, 3, 20, 40, 80, 120, 0], [0, -120, -80, -40, -20, -3, -2, -2]]);
    assert(RS_PIECEVAL == [0, 0, 45, 80, 150, 200, 300, 0, -45, -80, -150, -200, -300]);
    assert(RS_RANKVAL == [[0, 0, 0.1L, 0.2L, 0.4L, 1.0L, 1.2L, 0],
            [0.0L, -1.2L, -1.0L, -0.4L, -0.2L, -0.1L, 0, 0]]);
    assert(RS_WEAK_MUL == [[0.0L, 0.00L, 0.02L, 0.05L, 0.10L, 0.20L, 0.08L, 0],
            [0.0L, 0.08L, 0.20L, 0.10L, 0.05L, 0.02L, 0.00L, 0]]);
    real[64] rsq = [0.0L, 0, 0, 0, 0, 0, 0, 0,
          0.05L, 0.07L, 0.09L, 0.10L, 0.10L, 0.09L, 0.07L, 0.05L,
          0.11L, 0.12L, 0.14L, 0.15L, 0.15L, 0.14L, 0.12L, 0.11L,
          0.10L, 0.11L, 0.13L, 0.14L, 0.14L, 0.13L, 0.11L, 0.10L,
          0.09L, 0.10L, 0.11L, 0.12L, 0.12L, 0.11L, 0.10L, 0.09L,
          0.09L, 0.10L, 0.10L, 0.11L, 0.11L, 0.10L, 0.10L, 0.09L,
          0.07L, 0.08L, 0.08L, 0.09L, 0.09L, 0.08L, 0.08L, 0.07L,
          0   , 0   , 0   , 0   , 0   , 0   , 0   , 0   ];
    assert(RS_SQ == rsq);
    assert(PS_PIECEVAL == [0, 0, 8, 12, 24, 36, 44, 0, -8, -12, -24, -36, -44]);
    assert(PS_MAX_POWER == 4400 && PS_MIN_POWER == -4400);
    assert(FROZEN_PENALTY == [0, -6, -9, -12, -18, -33, -88, 6, 9, 12, 18, 33, 88]);
    real[33] pop_mul = [0.8L, 0.8L, 0.8L, 0.8L, 0.8L, 0.8L, 0.8L, 0.8L, 0.8L,
          0.9L, 0.9L, 0.9L, 0.9L, 0.9L, 0.9L, 0.9L, 0.9L,
          1.0L, 1.0L, 1.0L, 1.0L, 1.0L, 1.0L, 1.0L, 1.0L,
          1.1L, 1.1L, 1.1L, 1.1L, 1.2L, 1.2L, 1.2L, 1.2L];
    assert(POPULATION_MUL == pop_mul);
    assert(MOBILE_SIDE_MUL == [0.1L, -0.1L]);
}

// The values are shared by every thread and the other tests run in
// parallel, so these tests leave every value as it is.
@("tune options find their value; others are left alone")
unittest
{
    assert(set_option("tune_open_file_6", "40"));
    assert(set_option("tune_rs_sq_3_1", "0.11"));
    assert(set_option("tune_nmh_reduction", "4"));
    assert(OPEN_FILE[0][6] == 40 && OPEN_FILE[1][1] == -40);
    assert(!set_option("tune_no_such_thing", "1"));
    assert(!set_option("eval_goal", "1"));
    assert(!set_option("tune_", "1"));
}

@("integer tunables round")
unittest
{
    int v;
    real r;
    Tunable("i", true, &v, 0).set(3.6);
    assert(v == 4);
    Tunable("r", false, &r, 0).set(3.6);
    assert(r == 3.6L);
}

@("every tunable's name is unique and its value is its startup value")
unittest
{
    bool[string] seen;
    foreach (t; registry)
    {
        assert(t.name !in seen, t.name);
        seen[t.name] = true;
        assert(t.get() == t.initial, t.name);
    }
    assert(registry.length > 200);
}

@("shape values start at 0 and change whole tables")
unittest
{
    size_t shapes;
    foreach (t; registry)
        if (t.name.length > 8 && t.name[$ - 8 .. $ - 1] == "_shape_")
        {
            assert(t.initial == 0, t.name);
            shapes++;
        }
    assert(shapes == 56);

    // On local tables, so the shared values stay as they are.
    int[8] base = [2, 2, 2, 3, 10, 20, 40, 0];
    int[8] entry;
    real[3] none = 0;
    add_curve(entry[], base[], 0, 6, 40, none[]);
    assert(entry == base);
    real[3] up = [0, 0, 1];
    add_curve(entry[], base[], 0, 6, 40, up[]);
    assert(entry[0] == 2 && entry[3] == 13 && entry[6] == 80 && entry[7] == 0);

    real[5] decay = [1.0L, 0.6L, 0.4L, 0.2L, 0.1L];
    real[5] scaled;
    real[2] none2 = 0;
    scale_curve(scaled[], decay[], 0, 4, none2[]);
    assert(scaled == decay);
    real[2] steeper = [-0.5L, 0];
    scale_curve(scaled[], decay[], 0, 4, steeper[]);
    import std.conv : text;
    import std.math : isClose;
    assert(scaled[0] == 1.0L && isClose(scaled[4], 0.05L) && isClose(scaled[2], 0.3L), text(scaled));
    real[2] negative = [-3, 0];
    scale_curve(scaled[], decay[], 0, 4, negative[]);
    assert(scaled[0] == 1.0L && scaled[4] == 0 && scaled[3] == 0, text(scaled));
}
