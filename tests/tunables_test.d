/// Tests of the tunable constants: the tables derived from their defaults
/// (the values tuned by SPSA run 0009 since 2026-10-25), and options that
/// set and reset them. Before the tuning, the defaults rebuilt the tables
/// the evaluation had before they were tunable (checked then by
/// opfor_compare and by this test).
module tunables_test;

import tunables;

@("derived tables follow from the defaults")
unittest
{
    reset();
    assert(BOTH_SAFE == [-TSAFE_BOTH, TSAFE_BOTH]);
    assert(WHITE_SAFE == [TSAFE_HOME, TSAFE_AWAY]);
    assert(BLACK_SAFE == [-TSAFE_AWAY, -TSAFE_HOME]);
    // Silver's rank r is gold's rank 7 - r, and its values are negated
    // (the weak-rabbit multiplier keeps its sign).
    foreach (r; 0 .. 8)
    {
        assert(NORABBIT_FILE[1][r] == -NORABBIT_FILE[0][7 - r]);
        assert(NORABBIT_ADJ[1][r] == -NORABBIT_ADJ[0][7 - r]);
        assert(OPEN_FILE[1][r] == -OPEN_FILE[0][7 - r]);
        assert(OPEN_ADJ[1][r] == -OPEN_ADJ[0][7 - r]);
        assert(RS_RANKVAL[1][r] == -RS_RANKVAL[0][7 - r]);
        assert(RS_WEAK_MUL[1][r] == RS_WEAK_MUL[0][7 - r]);
        foreach (f; 0 .. 8)
            assert(RS_SQ[r * 8 + f] == RS_SQ[r * 8 + 7 - f]);
    }
    // Shapes only move the ranks they cover.
    assert(NORABBIT_FILE[0][7] == NORABBIT_FILE_BASE[7]);
    assert(RS_SQ[0 .. 8] == RS_SQ_BASE[0 .. 8] && RS_SQ[56 .. 64] == RS_SQ_BASE[56 .. 64]);
    foreach (p; 1 .. 7)
    {
        assert(RS_PIECEVAL[p + 6] == -RS_PIECEVAL[p]);
        assert(PS_PIECEVAL[p + 6] == -PS_PIECEVAL[p]);
        assert(FROZEN_PENALTY[p + 6] == -FROZEN_PENALTY[p]);
    }
    assert(PS_MAX_POWER == PS_PIECEVAL[6] * PS_DISTVAL[0] && PS_MIN_POWER == -PS_MAX_POWER);
    foreach (n; 0 .. 33)
        assert(POPULATION_MUL[n] == FROZEN_POP_LEVEL[n <= 8 ? 0 : n <= 16 ? 1 : n <= 24 ? 2 : n <= 28 ? 3 : 4]);
    assert(MOBILE_SIDE_MUL == [MOBILE_SIDE, -MOBILE_SIDE]);
}

// The values are shared by every thread and the other tests run in
// parallel, so these tests leave every value as it is.
@("tune options find their value; others are left alone")
unittest
{
    auto open_file = OPEN_FILE;
    assert(set_option("tune_open_file_6", "40"));
    assert(set_option("tune_rs_sq_3_1", "0.11"));
    assert(set_option("tune_nmh_reduction", "4"));
    assert(OPEN_FILE_BASE[6] == 40 && OPEN_FILE == open_file);
    assert(!set_option("tune_no_such_thing", "1"));
    assert(!set_option("eval_goal", "1"));
    assert(!set_option("tune_", "1"));
}

@("integer tunables round")
unittest
{
    int v;
    double r;
    Tunable("i", true, &v, 0).set(3.6);
    assert(v == 4);
    Tunable("r", false, &r, 0).set(3.6);
    assert(r == 3.6);
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

@("shape values change whole tables")
unittest
{
    size_t shapes;
    foreach (t; registry)
        if (t.name.length > 8 && t.name[$ - 8 .. $ - 1] == "_shape_")
            shapes++;
    assert(shapes == 56);

    // On local tables, so the shared values stay as they are.
    int[8] base = [2, 2, 2, 3, 10, 20, 40, 0];
    int[8] entry;
    double[3] none = 0;
    add_curve(entry[], base[], 0, 6, 40, none[]);
    assert(entry == base);
    double[3] up = [0, 0, 1];
    add_curve(entry[], base[], 0, 6, 40, up[]);
    assert(entry[0] == 2 && entry[3] == 13 && entry[6] == 80 && entry[7] == 0);

    double[5] decay = [1.0, 0.6, 0.4, 0.2, 0.1];
    double[5] scaled;
    double[2] none2 = 0;
    scale_curve(scaled[], decay[], 0, 4, none2[]);
    assert(scaled == decay);
    double[2] steeper = [-0.5, 0];
    scale_curve(scaled[], decay[], 0, 4, steeper[]);
    import std.conv : text;
    import std.math : isClose;
    assert(scaled[0] == 1.0 && isClose(scaled[4], 0.05) && isClose(scaled[2], 0.3), text(scaled));
    double[2] negative = [-3, 0];
    scale_curve(scaled[], decay[], 0, 4, negative[]);
    assert(scaled[0] == 1.0 && scaled[4] == 0 && scaled[3] == 0, text(scaled));
}
