/// Tunable constants of the evaluation and search.
///
/// Every number here was a constant in `staticeval.d`, `alphabeta.d` or
/// `bot_opfor.d`, and its default is the value it had there, so a build
/// with nothing set plays exactly as before. Each can be set by AEI
/// `setoption`: `tune_<name>` for a single value, `tune_<name>_<i>` for an
/// entry of a table (see `registry` for the full list). The values are
/// shared by every thread; set them before a search, not during one.
///
/// Tables that the code keeps for both colours (or for both halves of the
/// board) are tuned as one half, gold's, and the other half is derived
/// from it by `derive`, so a tuned set keeps the evaluation symmetric.
/// Entries no position can reach (a rabbit's goal rank, for example) are
/// left out.
///
/// Shapes: most tables can also be changed as a whole by a few
/// `<table>_shape_<k>` values, for tuning with fewer parameters. A table
/// indexed by rank gets an added curve,
///     entry[r] = base[r] + S * (s0 + s1 x + s2 x^2),  x = r / 6,
/// with S the table's largest default (so the shape values are fractions
/// of it); the rabbit square table also gets s3 times its distance from
/// the centre files. A decaying table gets a factor,
///     entry[i] = base[i] * max(0, 1 + s0 x + s1 x^2),  x = (i - lo) / (hi - lo),
/// over its used entries lo to hi, so its first entry stays as it is.
/// `base` is the table's own entries (`tune_<table>_<i>`). All shape values
/// are 0 by default, which leaves every table as it was.
module tunables;

import std.conv : to;
import std.math : lround;

// ---- trap safety (StaticEval.trap_safety) ----
__gshared int TSAFE_HOME = 17;  // one side holds its own home trap
__gshared int TSAFE_AWAY = 83;  // one side holds a trap in the other's half
__gshared int TSAFE_BOTH = 6;   // both hold it: a small edge to the away side
__gshared int[2] BOTH_SAFE;
__gshared int[2] WHITE_SAFE;
__gshared int[2] BLACK_SAFE;

// ---- open files ahead of rabbits (StaticEval.rabbit_open), gold's ranks ----
__gshared int[8] NORABBIT_FILE_BASE = [1, 1, 1, 2, 3, 5, 7, 0];
__gshared int[8] NORABBIT_ADJ_BASE = [1, 1, 1, 2, 2, 4, 4, 0];
__gshared int[8] OPEN_FILE_BASE = [2, 2, 2, 3, 10, 20, 40, 0];
__gshared int[8] OPEN_ADJ_BASE = [2, 2, 3, 20, 40, 80, 120, 0];
__gshared double[3] NORABBIT_FILE_SHAPE = [0.230025, -0.066508, -0.078639];
__gshared double[3] NORABBIT_ADJ_SHAPE = [-0.065227, 0.13054, 0.065696];
__gshared double[3] OPEN_FILE_SHAPE = [0.459365, 0.143103, -0.032555];
__gshared double[3] OPEN_ADJ_SHAPE = [0.111877, 0.035459, 0.063384];
// [side][rank], read by the eval
__gshared int[8][2] NORABBIT_FILE;
__gshared int[8][2] NORABBIT_ADJ;
__gshared int[8][2] OPEN_FILE;
__gshared int[8][2] OPEN_ADJ;

// ---- rabbits on the home ranks (StaticEval.rabbit_home) ----
__gshared int RHOME_FIRST_ROW = 3;

// ---- rabbit strength (StaticEval.rabbit_strength) ----
__gshared int[13] RS_PIECEVAL = [0, 0, 47, 94, 148, 194, 239, 0, 0, 0, 0, 0, 0];
__gshared int[16] RS_DISTVAL_BASE = [100, 100, 90, 75, 50, 10, 6, 3, 2, 1, 0, 0, 0, 0, 0, 0];
__gshared double[2] RS_DISTVAL_SHAPE = [-0.169837, -0.114968];
__gshared int[16] RS_DISTVAL;
__gshared double[8] RS_RANKVAL_BASE = [0, 0, 0.1, 0.2, 0.4, 1.0, 1.2, 0];
__gshared double[3] RS_RANKVAL_SHAPE = [0.084818, 0.30079, 0.276114];
__gshared double[8][2] RS_RANKVAL;
__gshared double[8] RS_WEAK_MUL_BASE = [0.0, 0.00, 0.02, 0.05, 0.10, 0.20, 0.08, 0];
__gshared double[3] RS_WEAK_MUL_SHAPE = [-0.384001, -0.116113, -0.066178];
__gshared double[8][2] RS_WEAK_MUL;
/// Rabbit square table, files a to d (e to h mirror them).
__gshared double[64] RS_SQ_BASE = [0.0, 0, 0, 0, 0, 0, 0, 0,
      0.05, 0.07, 0.09, 0.10, 0, 0, 0, 0,
      0.11, 0.12, 0.14, 0.15, 0, 0, 0, 0,
      0.10, 0.11, 0.13, 0.14, 0, 0, 0, 0,
      0.09, 0.10, 0.11, 0.12, 0, 0, 0, 0,
      0.09, 0.10, 0.10, 0.11, 0, 0, 0, 0,
      0.07, 0.08, 0.08, 0.09, 0, 0, 0, 0,
      0   , 0   , 0   , 0   , 0, 0, 0, 0];
__gshared double[4] RS_SQ_SHAPE = [0.481112, 0.206469, 0.021342, 0.962988];
__gshared double[64] RS_SQ;
__gshared int RS_INIT_BALANCE = -1717;
__gshared int RS_DEFENDER_BALANCE = 416;
__gshared int RS_WEAK_SPAN = 9743;
__gshared int RS_STRONG_SPAN = 8539;
__gshared double RS_STRONG_VAL = 146.047159;
__gshared double RS_STRONG_TRAP_MUL = 0.577971;
__gshared double RS_STRONG_UNSAFE_MUL = 0.508187;

// ---- piece strength (StaticEval.piece_strength) ----
__gshared int[13] PS_PIECEVAL = [0, 0, 8, 13, 20, 27, 47, 0, 0, 0, 0, 0, 0];
__gshared int[16] PS_DISTVAL_BASE = [100, 100, 95, 90, 85, 80, 40, 35, 30, 20, 1, 1, 1, 1, 0, 0];
__gshared double[2] PS_DISTVAL_SHAPE = [0.038346, -0.017819];
__gshared int[16] PS_DISTVAL;
__gshared int PS_MAX_POWER;  // the elephant's value at distance 0
__gshared int PS_MIN_POWER;

// ---- frozen pieces (StaticEval.frozen_pieces) ----
__gshared int[13] FROZEN_PENALTY = [0, -7, -7, -12, -17, -37, -88, 0, 0, 0, 0, 0, 0];
/// The penalty's multiplier by the number of pieces on the board, in
/// five levels: up to 8, 9 to 16, 17 to 24, 25 to 28 and 29 to 32.
__gshared double[5] FROZEN_POP_LEVEL_BASE = [0.8, 0.9, 1.0, 1.1, 1.2];
__gshared double[2] FROZEN_POP_LEVEL_SHAPE = [0.137512, -0.056618];
__gshared double[5] FROZEN_POP_LEVEL;
__gshared double[33] POPULATION_MUL;

// ---- hostages, frames and blockades (StaticEval.mobility) ----
__gshared double HOSTAGE_DIV = 2.205811;
__gshared double HOLDER_DIV = 13.208918;
__gshared double FROZEN_HOLDER_DIV = 3.951234;
__gshared double HOSTAGE_POWER_MUL = 0.794406;  // with the other side's power at the clamp
__gshared double HOSTAGE_POWER_SLOPE = 0.1;  // fraction off it with the hostage's own power at the clamp
__gshared double[4] MOBILE_MUL_BASE = [1.0, 0.3, 0.1, 0.05];
__gshared double[2] MOBILE_MUL_SHAPE = [0.014129, 0.06538];
__gshared double[4] MOBILE_MUL;
__gshared double EON_TRAP = 0.902444;
__gshared double EN_OF_TRAP = 0.944406;
__gshared double ENN_OF_TRAP = 0.977821;
__gshared double FRAMED_DIV = 3.470697;
__gshared double PINNED_DIV = 34.073626;
__gshared double FRAMER_DIV = 129.381951;
__gshared double BLOCKADE_DIV = 4.313951;
__gshared double[4] MOBILITY_MUL_BASE = [1.0, 0.75, 0.5, 0.25];
__gshared double[2] MOBILITY_MUL_SHAPE = [-0.049557, -0.065762];
__gshared double[4] MOBILITY_MUL;
__gshared double CLOSE_BLOCKADER_DIV = 76.330529;
__gshared double FAR_BLOCKADER_DIV = 75.260456;
__gshared double BLOCKADER_TRAP_DIV = 7.166542;
__gshared double[5] BLOCK_STRONGER_CL_BASE = [1.0, 0.6, 0.4, 0.2, 0.1];
__gshared double[5] BLOCK_STRONGER_FAR_BASE = [1.0, 0.7, 0.5, 0.3, 0.2];
__gshared double[3] BLOCK_EVEN_CL_BASE = [1.0, 0.75, 0.55];
__gshared double[3] BLOCK_EVEN_FAR_BASE = [1.0, 0.9, 0.8];
__gshared double[7] BLOCK_WEAK_CL_BASE = [1.0, 1.0, 1.0, 0.95, 0.9, 0.85, 0.8];
__gshared double[9] BLOCK_WEAK_FAR_BASE = [1.0, 1.0, 1.0, 1.0, 0.98, 0.95, 0.92, 0.9, 0.88];
__gshared double[2] BLOCK_STRONGER_CL_SHAPE = [-0.017203, 0.007771];
__gshared double[2] BLOCK_STRONGER_FAR_SHAPE = [0.054073, 0.00201];
__gshared double[2] BLOCK_EVEN_CL_SHAPE = [0.014157, -0.039371];
__gshared double[2] BLOCK_EVEN_FAR_SHAPE = [-0.00499, -0.041705];
__gshared double[2] BLOCK_WEAK_CL_SHAPE = [-0.189942, 0.00101];
__gshared double[2] BLOCK_WEAK_FAR_SHAPE = [-0.142564, 0.04225];
__gshared double[5] BLOCK_STRONGER_CL;
__gshared double[5] BLOCK_STRONGER_FAR;
__gshared double[3] BLOCK_EVEN_CL;
__gshared double[3] BLOCK_EVEN_FAR;
__gshared double[7] BLOCK_WEAK_CL;
__gshared double[9] BLOCK_WEAK_FAR;
__gshared int[4] MOBILE_VAL = [0, 25, 9, 1];
__gshared double MOBILE_SIDE = 0.108046;
__gshared double[2] MOBILE_SIDE_MUL;

// ---- threats (StaticEval.mobility) ----
__gshared double NK_TOUCH_DIV = 13.261376;
__gshared double NK_CLOSE_DIV = 18.485988;
__gshared double NK_FAR_DIV = 40.230512;
__gshared double KEPT_DIV = 67.924662;
__gshared double THREAT_COVER_DIV = 2.212211;      // a covered touch, close or kept threat
__gshared double THREAT_COVER_FAR_DIV = 4.355255;  // a covered far threat

// ---- static capture threats (StaticEval.static_trap_eval) ----
__gshared double[3] VICTIM_PER_BASE = [0.65, 0.75, 0.85];
__gshared double[2] VICTIM_PER_SHAPE = [-0.141978, 0.070352];
__gshared double[3] VICTIM_PER;
__gshared double FROZEN_PER = 0.252596;
__gshared double MULTIVIC_PER = 0.393274;
__gshared double MULTITRAP_PER = 1.399249;
__gshared double[13] LENGTH_PER_BASE = [1.0, 1.0, 1.0, 0.9, 0.9,
      0.3, 0.3, 0.2, 0.1, 0.05, 0.05, 0.01, 0.01];
__gshared double[2] LENGTH_PER_SHAPE = [0.084041, -0.003003];
__gshared double[13] LENGTH_PER;
__gshared double[5] DEFENSE_PER_BASE = [1.0, 0.9, 0.8, 0.6, 0.4];
__gshared double[2] DEFENSE_PER_SHAPE = [0.037926, -0.080372];
__gshared double[5] DEFENSE_PER;
__gshared double MAX_VICTIM_PER = 0.88553;
__gshared double NOW_VICTIM_PER = 0.88553;  // a capture the side to move can finish this turn

// ---- goal threats (StaticEval.goal_threat) ----
__gshared int[18] GOAL_THREAT_BASE = [10000, 800, 750, 650, 600,
      100, 100, 80, 80, 40, 40, 30, 30, 10, 10, 5, 5, 0];
__gshared double[2] GOAL_THREAT_SHAPE = [-0.028108, 0.143206];
__gshared int[18] GOAL_THREAT;
__gshared double[5] DEFENSE_STEPS_BASE = [1.0, 0.8, 0.66, 0.5, 0.33];
__gshared double[2] DEFENSE_STEPS_SHAPE = [-0.014425, -0.042258];
__gshared double[5] DEFENSE_STEPS;
__gshared double[9] DEFENSE_NUM_BASE = [1.0, 0.8, 0.7, 0.4, 0.2, 0.1, 0.05, 0.01, 0.01];
__gshared double[2] DEFENSE_NUM_SHAPE = [0.021778, 0.039086];
__gshared double[9] DEFENSE_NUM;

// ---- search (alphabeta.d, bot_opfor.d) ----
__gshared int NMH_MIN_DEPTH = 4;     // null move only above this depth
__gshared int NMH_REDUCTION = 4;
__gshared int LMR_MIN_DEPTH = 2;     // late move reductions above this depth
__gshared int LMR_MIN_STEPS = 3;     // ... after this many steps tried
__gshared int LMR_MIN_HISTORY = 1;   // ... and this many with history
__gshared int LMR_REDUCTION = 2;
__gshared int UNRELATED_WINDOW = 4;  // no unrelated-step pruning this close to the root
__gshared int GOAL_EXT_EXTRA = 8;    // PV goal checks up to max_depth plus this
__gshared int HISTORY_DECAY = 10;
__gshared int Q_CAPTURE_EXTRA = 2;   // qsearch captures up to stepsLeft plus this long
__gshared int[7] ROOT_REDUCTION_MARGINS = [150, 350, 1000, 2600, 6000, 15000, 30000];

/// A tunable value: an option name and where its value lives.
struct Tunable
{
    string name;
    bool is_int;
    void* ptr;
    double initial;

    double get() const
    {
        return is_int ? *cast(int*) ptr : *cast(double*) ptr;
    }

    void set(double v) const
    {
        if (is_int)
            *cast(int*) ptr = cast(int) lround(v);
        else
            *cast(double*) ptr = v;
    }
}

/// Every tunable, in a fixed order, with its value at startup.
__gshared Tunable[] registry;
private __gshared size_t[string] by_name;

private void add(string name, int* p)
{
    by_name[name] = registry.length;
    registry ~= Tunable(name, true, p, *p);
}

private void add(string name, double* p)
{
    by_name[name] = registry.length;
    registry ~= Tunable(name, false, p, *p);
}

/// Entries lo to hi (inclusive) of a table, as name_lo to name_hi.
private void add(T)(string name, T[] table, size_t lo, size_t hi)
{
    foreach (i; lo .. hi + 1)
        add(name ~ "_" ~ to!string(i), &table[i]);
}

/// A table's shape values, as name_shape_0 and up.
private void add_shape(string name, double[] shape)
{
    add(name ~ "_shape", shape, 0, shape.length - 1);
}

private int to_entry(T : int)(double v)
{
    return cast(int) lround(v);
}

private double to_entry(T : double)(double v)
{
    return v;
}

/// entry[r] = base[r] + scale * (s0 + s1 x + s2 x^2), x = r / 6, for
/// entries lo to hi; the others are copied.
void add_curve(T)(T[] entry, const T[] base, size_t lo, size_t hi,
        double scale, const double[] s)
{
    entry[] = base[];
    foreach (r; lo .. hi + 1)
    {
        double x = r / 6.0;
        entry[r] = to_entry!T(base[r] + scale * (s[0] + s[1] * x + s[2] * x * x));
    }
}

/// entry[i] = base[i] * (1 + s0 x + s1 x^2), x = (i - lo) / (hi - lo),
/// for entries lo to hi; the others are copied. The factor stops at 0, so
/// no shape turns a multiplier's sign.
void scale_curve(T)(T[] entry, const T[] base, size_t lo, size_t hi,
        const double[] s)
{
    entry[] = base[];
    foreach (i; lo .. hi + 1)
    {
        double x = (i - lo) / cast(double)(hi - lo);
        double factor = 1 + s[0] * x + s[1] * x * x;
        entry[i] = to_entry!T(base[i] * (factor > 0 ? factor : 0));
    }
}

/// Sets the tables the eval reads from the tuned values: the shapes, then
/// the halves derived by symmetry.
void derive()
{
    BOTH_SAFE = [-TSAFE_BOTH, TSAFE_BOTH];
    WHITE_SAFE = [TSAFE_HOME, TSAFE_AWAY];
    BLACK_SAFE = [-TSAFE_AWAY, -TSAFE_HOME];

    add_curve(NORABBIT_FILE[0][], NORABBIT_FILE_BASE[], 0, 6, 7, NORABBIT_FILE_SHAPE[]);
    add_curve(NORABBIT_ADJ[0][], NORABBIT_ADJ_BASE[], 0, 6, 4, NORABBIT_ADJ_SHAPE[]);
    add_curve(OPEN_FILE[0][], OPEN_FILE_BASE[], 0, 6, 40, OPEN_FILE_SHAPE[]);
    add_curve(OPEN_ADJ[0][], OPEN_ADJ_BASE[], 0, 6, 120, OPEN_ADJ_SHAPE[]);
    add_curve(RS_RANKVAL[0][], RS_RANKVAL_BASE[], 1, 6, 1.2, RS_RANKVAL_SHAPE[]);
    add_curve(RS_WEAK_MUL[0][], RS_WEAK_MUL_BASE[], 1, 6, 0.2, RS_WEAK_MUL_SHAPE[]);
    RS_SQ[] = RS_SQ_BASE[];
    foreach (r; 1 .. 7)
        foreach (f; 0 .. 4)
        {
            double x = r / 6.0;
            double edge = (3 - f) / 3.0;
            RS_SQ[r * 8 + f] = RS_SQ_BASE[r * 8 + f] + 0.15 * (RS_SQ_SHAPE[0]
                    + RS_SQ_SHAPE[1] * x + RS_SQ_SHAPE[2] * x * x + RS_SQ_SHAPE[3] * edge);
        }
    scale_curve(RS_DISTVAL[], RS_DISTVAL_BASE[], 0, 15, RS_DISTVAL_SHAPE[]);
    scale_curve(PS_DISTVAL[], PS_DISTVAL_BASE[], 0, 15, PS_DISTVAL_SHAPE[]);
    scale_curve(FROZEN_POP_LEVEL[], FROZEN_POP_LEVEL_BASE[], 0, 4, FROZEN_POP_LEVEL_SHAPE[]);
    scale_curve(MOBILE_MUL[], MOBILE_MUL_BASE[], 0, 3, MOBILE_MUL_SHAPE[]);
    scale_curve(MOBILITY_MUL[], MOBILITY_MUL_BASE[], 0, 3, MOBILITY_MUL_SHAPE[]);
    scale_curve(BLOCK_STRONGER_CL[], BLOCK_STRONGER_CL_BASE[], 0, 4, BLOCK_STRONGER_CL_SHAPE[]);
    scale_curve(BLOCK_STRONGER_FAR[], BLOCK_STRONGER_FAR_BASE[], 0, 4, BLOCK_STRONGER_FAR_SHAPE[]);
    scale_curve(BLOCK_EVEN_CL[], BLOCK_EVEN_CL_BASE[], 0, 2, BLOCK_EVEN_CL_SHAPE[]);
    scale_curve(BLOCK_EVEN_FAR[], BLOCK_EVEN_FAR_BASE[], 0, 2, BLOCK_EVEN_FAR_SHAPE[]);
    scale_curve(BLOCK_WEAK_CL[], BLOCK_WEAK_CL_BASE[], 0, 6, BLOCK_WEAK_CL_SHAPE[]);
    scale_curve(BLOCK_WEAK_FAR[], BLOCK_WEAK_FAR_BASE[], 0, 8, BLOCK_WEAK_FAR_SHAPE[]);
    scale_curve(VICTIM_PER[], VICTIM_PER_BASE[], 0, 2, VICTIM_PER_SHAPE[]);
    scale_curve(LENGTH_PER[], LENGTH_PER_BASE[], 1, 12, LENGTH_PER_SHAPE[]);
    scale_curve(DEFENSE_PER[], DEFENSE_PER_BASE[], 0, 4, DEFENSE_PER_SHAPE[]);
    scale_curve(GOAL_THREAT[], GOAL_THREAT_BASE[], 1, 4, GOAL_THREAT_SHAPE[]);
    scale_curve(DEFENSE_STEPS[], DEFENSE_STEPS_BASE[], 0, 4, DEFENSE_STEPS_SHAPE[]);
    scale_curve(DEFENSE_NUM[], DEFENSE_NUM_BASE[], 0, 8, DEFENSE_NUM_SHAPE[]);

    // Silver's rank r is gold's rank 7 - r.
    foreach (r; 0 .. 8)
    {
        NORABBIT_FILE[1][r] = -NORABBIT_FILE[0][7 - r];
        NORABBIT_ADJ[1][r] = -NORABBIT_ADJ[0][7 - r];
        OPEN_FILE[1][r] = -OPEN_FILE[0][7 - r];
        OPEN_ADJ[1][r] = -OPEN_ADJ[0][7 - r];
        RS_RANKVAL[1][r] = -RS_RANKVAL[0][7 - r];
        RS_WEAK_MUL[1][r] = RS_WEAK_MUL[0][7 - r];
        foreach (f; 4 .. 8)
            RS_SQ[r * 8 + f] = RS_SQ[r * 8 + 7 - f];
    }
    foreach (p; 1 .. 7)
    {
        RS_PIECEVAL[p + 6] = -RS_PIECEVAL[p];
        PS_PIECEVAL[p + 6] = -PS_PIECEVAL[p];
        FROZEN_PENALTY[p + 6] = -FROZEN_PENALTY[p];
    }
    PS_MAX_POWER = PS_PIECEVAL[6] * PS_DISTVAL[0];
    PS_MIN_POWER = -PS_MAX_POWER;
    foreach (n; 0 .. 33)
        POPULATION_MUL[n] = FROZEN_POP_LEVEL[n <= 8 ? 0 : n <= 16 ? 1 : n <= 24 ? 2 : n <= 28 ? 3 : 4];
    MOBILE_SIDE_MUL = [MOBILE_SIDE, -MOBILE_SIDE];
}

shared static this()
{
    add("tsafe_home", &TSAFE_HOME);
    add("tsafe_away", &TSAFE_AWAY);
    add("tsafe_both", &TSAFE_BOTH);

    add("norabbit_file", NORABBIT_FILE_BASE[], 0, 6);
    add("norabbit_adj", NORABBIT_ADJ_BASE[], 0, 6);
    add("open_file", OPEN_FILE_BASE[], 0, 6);
    add("open_adj", OPEN_ADJ_BASE[], 0, 6);
    add_shape("norabbit_file", NORABBIT_FILE_SHAPE[]);
    add_shape("norabbit_adj", NORABBIT_ADJ_SHAPE[]);
    add_shape("open_file", OPEN_FILE_SHAPE[]);
    add_shape("open_adj", OPEN_ADJ_SHAPE[]);

    add("rhome_first_row", &RHOME_FIRST_ROW);

    add("rs_pieceval", RS_PIECEVAL[], 2, 6);
    add("rs_distval", RS_DISTVAL_BASE[], 0, 15);
    add_shape("rs_distval", RS_DISTVAL_SHAPE[]);
    add("rs_rankval", RS_RANKVAL_BASE[], 1, 6);
    add_shape("rs_rankval", RS_RANKVAL_SHAPE[]);
    add("rs_weak_mul", RS_WEAK_MUL_BASE[], 1, 6);
    add_shape("rs_weak_mul", RS_WEAK_MUL_SHAPE[]);
    foreach (r; 1 .. 7)
        foreach (f; 0 .. 4)
            add("rs_sq_" ~ to!string(r) ~ "_" ~ to!string(f), &RS_SQ_BASE[r * 8 + f]);
    add_shape("rs_sq", RS_SQ_SHAPE[]);
    add("rs_init_balance", &RS_INIT_BALANCE);
    add("rs_defender_balance", &RS_DEFENDER_BALANCE);
    add("rs_weak_span", &RS_WEAK_SPAN);
    add("rs_strong_span", &RS_STRONG_SPAN);
    add("rs_strong_val", &RS_STRONG_VAL);
    add("rs_strong_trap_mul", &RS_STRONG_TRAP_MUL);
    add("rs_strong_unsafe_mul", &RS_STRONG_UNSAFE_MUL);

    add("ps_pieceval", PS_PIECEVAL[], 2, 6);
    add("ps_distval", PS_DISTVAL_BASE[], 0, 15);
    add_shape("ps_distval", PS_DISTVAL_SHAPE[]);

    add("frozen_penalty", FROZEN_PENALTY[], 1, 6);
    add("frozen_pop_level", FROZEN_POP_LEVEL_BASE[], 0, 4);
    add_shape("frozen_pop_level", FROZEN_POP_LEVEL_SHAPE[]);

    add("hostage_div", &HOSTAGE_DIV);
    add("holder_div", &HOLDER_DIV);
    add("frozen_holder_div", &FROZEN_HOLDER_DIV);
    add("hostage_power_mul", &HOSTAGE_POWER_MUL);
    add("hostage_power_slope", &HOSTAGE_POWER_SLOPE);
    add("mobile_mul", MOBILE_MUL_BASE[], 0, 3);
    add_shape("mobile_mul", MOBILE_MUL_SHAPE[]);
    add("eon_trap", &EON_TRAP);
    add("en_of_trap", &EN_OF_TRAP);
    add("enn_of_trap", &ENN_OF_TRAP);
    add("framed_div", &FRAMED_DIV);
    add("pinned_div", &PINNED_DIV);
    add("framer_div", &FRAMER_DIV);
    add("blockade_div", &BLOCKADE_DIV);
    add("mobility_mul", MOBILITY_MUL_BASE[], 0, 3);
    add_shape("mobility_mul", MOBILITY_MUL_SHAPE[]);
    add("close_blockader_div", &CLOSE_BLOCKADER_DIV);
    add("far_blockader_div", &FAR_BLOCKADER_DIV);
    add("blockader_trap_div", &BLOCKADER_TRAP_DIV);
    add("block_stronger_cl", BLOCK_STRONGER_CL_BASE[], 0, 4);
    add("block_stronger_far", BLOCK_STRONGER_FAR_BASE[], 0, 4);
    add("block_even_cl", BLOCK_EVEN_CL_BASE[], 0, 2);
    add("block_even_far", BLOCK_EVEN_FAR_BASE[], 0, 2);
    add("block_weak_cl", BLOCK_WEAK_CL_BASE[], 0, 6);
    add("block_weak_far", BLOCK_WEAK_FAR_BASE[], 0, 8);
    add_shape("block_stronger_cl", BLOCK_STRONGER_CL_SHAPE[]);
    add_shape("block_stronger_far", BLOCK_STRONGER_FAR_SHAPE[]);
    add_shape("block_even_cl", BLOCK_EVEN_CL_SHAPE[]);
    add_shape("block_even_far", BLOCK_EVEN_FAR_SHAPE[]);
    add_shape("block_weak_cl", BLOCK_WEAK_CL_SHAPE[]);
    add_shape("block_weak_far", BLOCK_WEAK_FAR_SHAPE[]);
    add("mobile_val", MOBILE_VAL[], 1, 3);
    add("mobile_side", &MOBILE_SIDE);

    add("nk_touch_div", &NK_TOUCH_DIV);
    add("nk_close_div", &NK_CLOSE_DIV);
    add("nk_far_div", &NK_FAR_DIV);
    add("kept_div", &KEPT_DIV);
    add("threat_cover_div", &THREAT_COVER_DIV);
    add("threat_cover_far_div", &THREAT_COVER_FAR_DIV);

    add("victim_per", VICTIM_PER_BASE[], 0, 2);
    add_shape("victim_per", VICTIM_PER_SHAPE[]);
    add("frozen_per", &FROZEN_PER);
    add("multivic_per", &MULTIVIC_PER);
    add("multitrap_per", &MULTITRAP_PER);
    add("length_per", LENGTH_PER_BASE[], 1, 12);
    add_shape("length_per", LENGTH_PER_SHAPE[]);
    add("defense_per", DEFENSE_PER_BASE[], 0, 4);
    add_shape("defense_per", DEFENSE_PER_SHAPE[]);
    add("max_victim_per", &MAX_VICTIM_PER);
    add("now_victim_per", &NOW_VICTIM_PER);

    add("goal_threat", GOAL_THREAT_BASE[], 1, 4);
    add_shape("goal_threat", GOAL_THREAT_SHAPE[]);
    add("defense_steps", DEFENSE_STEPS_BASE[], 0, 4);
    add_shape("defense_steps", DEFENSE_STEPS_SHAPE[]);
    add("defense_num", DEFENSE_NUM_BASE[], 0, 8);
    add_shape("defense_num", DEFENSE_NUM_SHAPE[]);

    add("nmh_min_depth", &NMH_MIN_DEPTH);
    add("nmh_reduction", &NMH_REDUCTION);
    add("lmr_min_depth", &LMR_MIN_DEPTH);
    add("lmr_min_steps", &LMR_MIN_STEPS);
    add("lmr_min_history", &LMR_MIN_HISTORY);
    add("lmr_reduction", &LMR_REDUCTION);
    add("unrelated_window", &UNRELATED_WINDOW);
    add("goal_ext_extra", &GOAL_EXT_EXTRA);
    add("history_decay", &HISTORY_DECAY);
    add("q_capture_extra", &Q_CAPTURE_EXTRA);
    add("root_reduction_margins", ROOT_REDUCTION_MARGINS[], 0, 6);

    derive();
}

/// Handles `setoption name tune_<name> value <v>`. False if the option
/// isn't a tunable.
bool set_option(string option, string value)
{
    if (option.length < 5 || option[0 .. 5] != "tune_")
        return false;
    auto ix = option[5 .. $] in by_name;
    if (ix is null)
        return false;
    registry[*ix].set(to!double(value));
    derive();
    return true;
}

/// Puts every tunable back to its value at startup.
void reset()
{
    foreach (ref t; registry)
        t.set(t.initial);
    derive();
}
