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
module tunables;

import std.conv : to;
import std.math : lround;

// ---- trap safety (StaticEval.trap_safety) ----
__gshared int TSAFE_HOME = 20;  // one side holds its own home trap
__gshared int TSAFE_AWAY = 80;  // one side holds a trap in the other's half
__gshared int TSAFE_BOTH = 5;   // both hold it: a small edge to the away side
__gshared int[2] BOTH_SAFE;
__gshared int[2] WHITE_SAFE;
__gshared int[2] BLACK_SAFE;

// ---- open files ahead of rabbits (StaticEval.rabbit_open), [side][rank] ----
__gshared int[8][2] NORABBIT_FILE = [[1, 1, 1, 2, 3, 5, 7, 0], [0, 0, 0, 0, 0, 0, 0, 0]];
__gshared int[8][2] NORABBIT_ADJ = [[1, 1, 1, 2, 2, 4, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0]];
__gshared int[8][2] OPEN_FILE = [[2, 2, 2, 3, 10, 20, 40, 0], [0, 0, 0, 0, 0, 0, 0, 0]];
__gshared int[8][2] OPEN_ADJ = [[2, 2, 3, 20, 40, 80, 120, 0], [0, 0, 0, 0, 0, 0, 0, 0]];

// ---- rabbits on the home ranks (StaticEval.rabbit_home) ----
__gshared int RHOME_FIRST_ROW = 3;

// ---- rabbit strength (StaticEval.rabbit_strength) ----
__gshared int[13] RS_PIECEVAL = [0, 0, 45, 80, 150, 200, 300, 0, 0, 0, 0, 0, 0];
__gshared int[16] RS_DISTVAL = [100, 100, 90, 75, 50, 10, 6, 3, 2, 1, 0, 0, 0, 0, 0, 0];
__gshared real[8][2] RS_RANKVAL = [[0, 0, 0.1L, 0.2L, 0.4L, 1.0L, 1.2L, 0], [0, 0, 0, 0, 0, 0, 0, 0]];
__gshared real[8][2] RS_WEAK_MUL = [[0.0L, 0.00L, 0.02L, 0.05L, 0.10L, 0.20L, 0.08L, 0],
      [0, 0, 0, 0, 0, 0, 0, 0]];
/// Rabbit square table; files e to h mirror a to d.
__gshared real[64] RS_SQ = [0.0L, 0, 0, 0, 0, 0, 0, 0,
      0.05L, 0.07L, 0.09L, 0.10L, 0, 0, 0, 0,
      0.11L, 0.12L, 0.14L, 0.15L, 0, 0, 0, 0,
      0.10L, 0.11L, 0.13L, 0.14L, 0, 0, 0, 0,
      0.09L, 0.10L, 0.11L, 0.12L, 0, 0, 0, 0,
      0.09L, 0.10L, 0.10L, 0.11L, 0, 0, 0, 0,
      0.07L, 0.08L, 0.08L, 0.09L, 0, 0, 0, 0,
      0   , 0   , 0   , 0   , 0, 0, 0, 0];
__gshared int RS_INIT_BALANCE = -2000;
__gshared int RS_DEFENDER_BALANCE = 400;
__gshared int RS_WEAK_SPAN = 8000;
__gshared int RS_STRONG_SPAN = 9000;
__gshared real RS_STRONG_VAL = 450;
__gshared real RS_STRONG_TRAP_MUL = 0.6L;
__gshared real RS_STRONG_UNSAFE_MUL = 0.5L;

// ---- piece strength (StaticEval.piece_strength) ----
__gshared int[13] PS_PIECEVAL = [0, 0, 8, 12, 24, 36, 44, 0, 0, 0, 0, 0, 0];
__gshared int[16] PS_DISTVAL = [100, 100, 95, 90, 85, 80, 40, 35, 30, 20, 1, 1, 1, 1, 0, 0];
__gshared int PS_MAX_POWER;  // the elephant's value at distance 0
__gshared int PS_MIN_POWER;

// ---- frozen pieces (StaticEval.frozen_pieces) ----
__gshared int[13] FROZEN_PENALTY = [0, -6, -9, -12, -18, -33, -88, 0, 0, 0, 0, 0, 0];
/// The penalty's multiplier by the number of pieces on the board, in
/// five levels: up to 8, 9 to 16, 17 to 24, 25 to 28 and 29 to 32.
__gshared real[5] FROZEN_POP_LEVEL = [0.8L, 0.9L, 1.0L, 1.1L, 1.2L];
__gshared real[33] POPULATION_MUL;

// ---- hostages, frames and blockades (StaticEval.mobility) ----
__gshared real HOSTAGE_DIV = 2.0L;
__gshared real HOLDER_DIV = 9.4L;
__gshared real FROZEN_HOLDER_DIV = 4;
__gshared real HOSTAGE_POWER_MUL = 0.8L;  // when the hostage's power is on its side
__gshared real[4] MOBILE_MUL = [1.0L, 0.3L, 0.1L, 0.05L];
__gshared real EON_TRAP = 0.92L;
__gshared real EN_OF_TRAP = 0.95L;
__gshared real ENN_OF_TRAP = 0.98L;
__gshared real FRAMED_DIV = 4.0L;
__gshared real PINNED_DIV = 34.0L;
__gshared real FRAMER_DIV = 120.0L;
__gshared real BLOCKADE_DIV = 3;
__gshared real[4] MOBILITY_MUL = [1.0L, 0.75L, 0.5L, 0.25L];
__gshared real CLOSE_BLOCKADER_DIV = 80.0L;
__gshared real FAR_BLOCKADER_DIV = 100.0L;
__gshared real BLOCKADER_TRAP_DIV = 10.0L;
__gshared real[5] BLOCK_STRONGER_CL = [1.0L, 0.6L, 0.4L, 0.2L, 0.1L];
__gshared real[5] BLOCK_STRONGER_FAR = [1.0L, 0.7L, 0.5L, 0.3L, 0.2L];
__gshared real[3] BLOCK_EVEN_CL = [1.0L, 0.75L, 0.55L];
__gshared real[3] BLOCK_EVEN_FAR = [1.0L, 0.9L, 0.8L];
__gshared real[7] BLOCK_WEAK_CL = [1.0L, 1.0L, 1.0L, 0.95L, 0.9L, 0.85L, 0.8L];
__gshared real[9] BLOCK_WEAK_FAR = [1.0L, 1.0L, 1.0L, 1.0L, 0.98L, 0.95L, 0.92L, 0.9L, 0.88L];
__gshared int[4] MOBILE_VAL = [0, 20, 8, 2];
__gshared real MOBILE_SIDE = 0.1L;
__gshared real[2] MOBILE_SIDE_MUL;

// ---- threats (StaticEval.mobility) ----
__gshared real NK_TOUCH_DIV = 10;
__gshared real NK_CLOSE_DIV = 20;
__gshared real NK_FAR_DIV = 40;
__gshared real KEPT_DIV = 60;
__gshared real THREAT_COVER_DIV = 2;      // a covered touch, close or kept threat
__gshared real THREAT_COVER_FAR_DIV = 4;  // a covered far threat

// ---- static capture threats (StaticEval.static_trap_eval) ----
__gshared real[3] VICTIM_PER = [0.65L, 0.75L, 0.85L];
__gshared real FROZEN_PER = 0.2L;
__gshared real MULTIVIC_PER = 0.4L;
__gshared real MULTITRAP_PER = 1.5L;
__gshared real[13] LENGTH_PER = [1.0L, 1.0L, 1.0L, 0.9L, 0.9L,
      0.3L, 0.3L, 0.2L, 0.1L, 0.05L, 0.05L, 0.01L, 0.01L];
__gshared real[5] DEFENSE_PER = [1.0L, 0.9L, 0.8L, 0.6L, 0.4L];
__gshared real MAX_VICTIM_PER = 0.9L;

// ---- goal threats (StaticEval.goal_threat) ----
__gshared int[18] GOAL_THREAT = [10000, 800, 750, 650, 600,
      100, 100, 80, 80, 40, 40, 30, 30, 10, 10, 5, 5, 0];
__gshared real[5] DEFENSE_STEPS = [1.0L, 0.8L, 0.66L, 0.5L, 0.33L];
__gshared real[9] DEFENSE_NUM = [1.0L, 0.8L, 0.7L, 0.4L, 0.2L, 0.1L, 0.05L, 0.01L, 0.01L];

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
    real initial;

    real get() const
    {
        return is_int ? *cast(int*) ptr : *cast(real*) ptr;
    }

    void set(real v) const
    {
        if (is_int)
            *cast(int*) ptr = cast(int) lround(v);
        else
            *cast(real*) ptr = v;
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

private void add(string name, real* p)
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

/// Sets the tables derived from the tuned halves.
void derive()
{
    BOTH_SAFE = [-TSAFE_BOTH, TSAFE_BOTH];
    WHITE_SAFE = [TSAFE_HOME, TSAFE_AWAY];
    BLACK_SAFE = [-TSAFE_AWAY, -TSAFE_HOME];
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

    add("norabbit_file", NORABBIT_FILE[0][], 0, 6);
    add("norabbit_adj", NORABBIT_ADJ[0][], 0, 6);
    add("open_file", OPEN_FILE[0][], 0, 6);
    add("open_adj", OPEN_ADJ[0][], 0, 6);

    add("rhome_first_row", &RHOME_FIRST_ROW);

    add("rs_pieceval", RS_PIECEVAL[], 2, 6);
    add("rs_distval", RS_DISTVAL[], 0, 15);
    add("rs_rankval", RS_RANKVAL[0][], 1, 6);
    add("rs_weak_mul", RS_WEAK_MUL[0][], 1, 6);
    foreach (r; 1 .. 7)
        foreach (f; 0 .. 4)
            add("rs_sq_" ~ to!string(r) ~ "_" ~ to!string(f), &RS_SQ[r * 8 + f]);
    add("rs_init_balance", &RS_INIT_BALANCE);
    add("rs_defender_balance", &RS_DEFENDER_BALANCE);
    add("rs_weak_span", &RS_WEAK_SPAN);
    add("rs_strong_span", &RS_STRONG_SPAN);
    add("rs_strong_val", &RS_STRONG_VAL);
    add("rs_strong_trap_mul", &RS_STRONG_TRAP_MUL);
    add("rs_strong_unsafe_mul", &RS_STRONG_UNSAFE_MUL);

    add("ps_pieceval", PS_PIECEVAL[], 2, 6);
    add("ps_distval", PS_DISTVAL[], 0, 15);

    add("frozen_penalty", FROZEN_PENALTY[], 1, 6);
    add("frozen_pop_level", FROZEN_POP_LEVEL[], 0, 4);

    add("hostage_div", &HOSTAGE_DIV);
    add("holder_div", &HOLDER_DIV);
    add("frozen_holder_div", &FROZEN_HOLDER_DIV);
    add("hostage_power_mul", &HOSTAGE_POWER_MUL);
    add("mobile_mul", MOBILE_MUL[], 0, 3);
    add("eon_trap", &EON_TRAP);
    add("en_of_trap", &EN_OF_TRAP);
    add("enn_of_trap", &ENN_OF_TRAP);
    add("framed_div", &FRAMED_DIV);
    add("pinned_div", &PINNED_DIV);
    add("framer_div", &FRAMER_DIV);
    add("blockade_div", &BLOCKADE_DIV);
    add("mobility_mul", MOBILITY_MUL[], 0, 3);
    add("close_blockader_div", &CLOSE_BLOCKADER_DIV);
    add("far_blockader_div", &FAR_BLOCKADER_DIV);
    add("blockader_trap_div", &BLOCKADER_TRAP_DIV);
    add("block_stronger_cl", BLOCK_STRONGER_CL[], 0, 4);
    add("block_stronger_far", BLOCK_STRONGER_FAR[], 0, 4);
    add("block_even_cl", BLOCK_EVEN_CL[], 0, 2);
    add("block_even_far", BLOCK_EVEN_FAR[], 0, 2);
    add("block_weak_cl", BLOCK_WEAK_CL[], 0, 6);
    add("block_weak_far", BLOCK_WEAK_FAR[], 0, 8);
    add("mobile_val", MOBILE_VAL[], 1, 3);
    add("mobile_side", &MOBILE_SIDE);

    add("nk_touch_div", &NK_TOUCH_DIV);
    add("nk_close_div", &NK_CLOSE_DIV);
    add("nk_far_div", &NK_FAR_DIV);
    add("kept_div", &KEPT_DIV);
    add("threat_cover_div", &THREAT_COVER_DIV);
    add("threat_cover_far_div", &THREAT_COVER_FAR_DIV);

    add("victim_per", VICTIM_PER[], 0, 2);
    add("frozen_per", &FROZEN_PER);
    add("multivic_per", &MULTIVIC_PER);
    add("multitrap_per", &MULTITRAP_PER);
    add("length_per", LENGTH_PER[], 1, 12);
    add("defense_per", DEFENSE_PER[], 0, 4);
    add("max_victim_per", &MAX_VICTIM_PER);

    add("goal_threat", GOAL_THREAT[], 1, 4);
    add("defense_steps", DEFENSE_STEPS[], 0, 4);
    add("defense_num", DEFENSE_NUM[], 0, 8);

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
    registry[*ix].set(to!real(value));
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
