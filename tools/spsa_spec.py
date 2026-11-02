#!/usr/bin/env python3
"""Writes an SPSA spec for OpFor's tunables, for howdah-tourney
(https://github.com/Janzert/howdah).

  spsa_spec.py --program PATH [--rev REV] [--iterations N] [--pairs P]
               [--time-control TC] [--name NAME] > spec.toml

The 129 parameters: the 54 shape values of OpFor's tables, 59 raw
scalars and small tables, and the 16 eval_* weights. Every start is
OpFor's default at REV (read from that commit, so build the engine from
the same one). The search integers and eval_goalest, which would only
duplicate the goal_est values, are left out. PATH is the engine, relative
to the spec file.

Ranges are centred on the start: shape values keep the width they had
in the previous tuning run, most scalars go from a third to three times
their value (inside the limits given below), and the rest have a fixed
range. Terms tuned before get c_end = range / 40, half its size then,
since they start near their optimum; NEW ones, never tuned, get
range / 20 (OpenBench's rule of thumb). Add a new tunable here when it
goes into tunables.d or staticeval.d.
"""
import argparse
import math
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]

# Never tuned in a game run.
NEW = {"tune_hostage_power_slope", "tune_blockader_trap_own_mul",
       "tune_blockader_trap_total_mul", "tune_now_victim_per", "tune_root_margin_scale"} | {
    f"tune_goal_est_{i}" for i in range(6)}

# (name, start, min, max, int?, c_end)
P = []
DEFAULTS = {}


def read_defaults(rev):
    def show(path):
        return subprocess.check_output(
            ["git", "-C", str(REPO), "show", f"{rev}:source/{path}"], text=True)

    src = show("tunables.d")
    for m in re.finditer(r"__gshared (?:int|double) (\w+) = (-?[\d.]+);", src):
        DEFAULTS["tune_" + m[1].lower()] = float(m[2])
    for m in re.finditer(r"__gshared (?:int|double)\[\d+\] (\w+) = \[([^\]]*)\];", src):
        for i, v in enumerate(re.findall(r"-?[\d.]+", m[2])):
            DEFAULTS[f"tune_{m[1].lower()}_{i}"] = float(v)
    for m in re.finditer(r"double (\w+)_w = (-?[\d.]+)", show("staticeval.d")):
        DEFAULTS["eval_" + m[1]] = float(m[2])


def add(name, lo, hi, is_int=False, c_end=None):
    """A fixed range."""
    start = DEFAULTS[name]
    if c_end is None:
        c_end = (hi - lo) / (20 if name in NEW else 40)
    P.append((name, start, lo, hi, is_int, c_end))


def scaled(name, is_int=False, lo=None, hi=None):
    """A third to three times the start, inside lo and hi."""
    v = DEFAULTS[name]
    a, b = sorted((v / 3, v * 3))
    if is_int:
        a, b = math.floor(a), math.ceil(b)
    add(name, a if lo is None else max(a, lo), b if hi is None else min(b, hi), is_int)


def shapes():
    # Rank tables: an added curve, in fractions of the table's largest default.
    def centred(name, half):
        v = DEFAULTS[name]
        add(name, v - half, v + half)

    for t in ["norabbit_file", "norabbit_adj", "open_file", "open_adj", "rs_rankval", "rs_weak_mul"]:
        for k in range(3):
            centred(f"tune_{t}_shape_{k}", 2.0)
    for k in range(4):
        centred(f"tune_rs_sq_shape_{k}", 4.0)
    # Decaying tables: a factor 1 + s0 x + s1 x^2 (stopping at 0).
    for t in ["rs_distval", "ps_distval", "mobile_mul", "mobility_mul",
              "block_stronger_cl", "block_stronger_far", "block_even_cl", "block_even_far",
              "block_weak_cl", "block_weak_far", "victim_per", "length_per", "defense_per",
              "goal_threat", "defense_steps", "defense_num"]:
        for k in range(2):
            centred(f"tune_{t}_shape_{k}", 1.0)


def scalars():
    scaled("tune_tsafe_home", True)
    scaled("tune_tsafe_away", True)
    add("tune_tsafe_both", -20, 30, True)
    scaled("tune_rhome_first_row", True)
    for i in range(2, 7):
        scaled(f"tune_rs_pieceval_{i}", True)
    add("tune_rs_init_balance", -6000, 2000, True)
    for name in ["rs_defender_balance", "rs_weak_span", "rs_strong_span"]:
        scaled(f"tune_{name}", True)
    scaled("tune_rs_strong_val")
    scaled("tune_rs_strong_trap_mul", hi=1.5)
    scaled("tune_rs_strong_unsafe_mul", hi=1.5)
    for i in range(2, 7):
        scaled(f"tune_ps_pieceval_{i}", True)
    for i in range(1, 4):
        scaled(f"tune_mobile_val_{i}", True)
    scaled("tune_mobile_side")
    for name, lo, hi in [
        ("hostage_div", None, None), ("holder_div", None, None),
        ("frozen_holder_div", None, None), ("hostage_power_mul", 0.4, 1.0),
        ("eon_trap", 0.7, 1.0), ("en_of_trap", 0.8, 1.0),
        ("enn_of_trap", 0.9, 1.0), ("framed_div", None, None),
        ("pinned_div", None, None), ("framer_div", None, None),
        ("blockade_div", None, None), ("close_blockader_div", None, None),
        ("far_blockader_div", None, None),
        ("nk_touch_div", None, None), ("nk_close_div", None, None),
        ("nk_far_div", None, None), ("kept_div", None, None),
        ("threat_cover_div", 1.0, None), ("threat_cover_far_div", 1.0, None),
        ("frozen_per", None, None), ("multivic_per", None, 1.0),
        ("multitrap_per", 1.0, None), ("max_victim_per", 0.5, 1.0),
    ]:
        scaled(f"tune_{name}", lo=lo, hi=hi)
    add("tune_hostage_power_slope", 0.0, 0.3)
    add("tune_now_victim_per", 0.5, 2.0)
    add("tune_blockader_trap_own_mul", 0.0, 3.0)
    # Small start, wide range: at range / 20 the early steps would hit 0.
    add("tune_blockader_trap_total_mul", 0.0, 1.5, c_end=0.03)
    for i, (lo, hi) in enumerate([(100, 800), (0, 450), (-60, 240),
                                  (-100, 250), (-100, 100), (-150, 100)]):
        add(f"tune_goal_est_{i}", lo, hi, True)
    # The margins are hand values in eval units, never tuned.
    add("tune_root_margin_scale", 0.4, 2.5)


def weights():
    for w in ["static_otrap", "static_strap", "tsafety", "pstrength", "mobility", "threat",
              "rstrong", "rwall", "ropen", "rhome", "map_e", "goal", "hostage", "frame"]:
        scaled(f"eval_{w}")
    # Near 0 or below it, so free to change sign.
    add("eval_rweak", -3.0, 3.0)
    add("eval_ontrap", -2.0, 3.0)


def fmt(x, is_int):
    return str(int(x)) if is_int else repr(float(x))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rev", default="HEAD")
    ap.add_argument("--iterations", type=int, default=2000)
    ap.add_argument("--pairs", type=int, default=8)
    ap.add_argument("--time-control", default="1s/30s/100/0/100t")
    ap.add_argument("--program", required=True,
                    help="the engine, relative to the spec file")
    ap.add_argument("--name", default=None)
    a = ap.parse_args()
    sys.stdout.reconfigure(newline="\n")
    rev = subprocess.check_output(
        ["git", "-C", str(REPO), "rev-parse", "--short", a.rev], text=True).strip()
    read_defaults(rev)
    shapes()
    scalars()
    weights()
    for name, start, lo, hi, is_int, c in P:
        first = max(c * a.iterations ** 0.101, 0.5 if is_int else 0)
        assert lo <= start - first and start + first <= hi or is_int and lo <= start <= hi, name
    assert len({p[0] for p in P}) == len(P)
    name = a.name or f"OpFor SPSA {len(P)} params from {rev}"
    print(f"""# Generated by OpFor tools/spsa_spec.py --rev {rev} --iterations {a.iterations} --pairs {a.pairs}
# ({len(P)} parameters: OpFor's shape values, raw scalars and eval_* weights,
# starting at its defaults at that commit). Paths are relative to this
# file. Submit with:
#   howdah-tourney submit <this file> --priority 1
name = "{name}"
time_control = "{a.time_control}"
concurrency = 8

[spsa]
iterations = {a.iterations}
pairs_per_iteration = {a.pairs}
alpha = 0.602
gamma = 0.101
a_ratio = 0.1
""")
    for name, start, lo, hi, is_int, c in P:
        print("[[spsa.params]]")
        print(f'name = "{name}"')
        print(f"start = {fmt(start, is_int)}")
        print(f"min = {fmt(lo, is_int)}")
        print(f"max = {fmt(hi, is_int)}")
        print(f"c_end = {c!r}")
        if is_int:
            print("int = true")
        print()
    print(f"""[[engines]]
name = "OpFor"
program = "{a.program}"

[engines.options]
hash = 64

[memory]
growth = 3.0
limit_mb = 2000""")


if __name__ == "__main__":
    main()
