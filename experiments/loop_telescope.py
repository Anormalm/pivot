#!/usr/bin/env python3
"""
Direct stress test of the aggregate loop-telescope inequality proposed for
C-HD's BM.23 accounting.

Each pivot group is partitioned into:
  home 0     : parent-own/final vertices
  home i > 0 : vertices returned by child i

Children are processed in order. For each group at each child:
  meeting := current group intersects U_i
  marked  := current pivot is in U_i AND residual group is nonempty
  emptied := current group is nonempty AND residual group is empty

After a marked event, the next pivot may be chosen by an arbitrary policy.
This script uses random pivot choices to exercise the loop state transitions.

It checks the two exact structural facts needed by the proposed Lean proof:

  (1) per iteration:
        marked_count + emptied_count <= meeting_count

  (2) over the whole full-call child loop:
        total_marked + p <= total_meetings + own_groups

Here own_groups is the number of original groups containing a home-0 member.
After every child home is processed, final_nonempty == own_groups exactly in
this abstract home model.

This experiment tests the loop-level bookkeeping directly. It is not a proof
of the C-HD theorem.
"""

from dataclasses import dataclass
import argparse
import json
import random
from pathlib import Path


@dataclass
class GroupState:
    homes: tuple[int, ...]
    live: set[int]
    pivot: int


def make_group(homes, rng):
    live = set(range(len(homes)))
    pivot = rng.choice(tuple(live))
    return GroupState(tuple(homes), live, pivot)


def step_group(g, child, rng):
    if not g.live:
        return 0, 0, 0

    removed = {v for v in g.live if g.homes[v] == child}
    meeting = int(bool(removed))
    if not removed:
        return meeting, 0, 0

    residual = g.live - removed
    pivot_removed = g.pivot in removed

    marked = int(pivot_removed and bool(residual))
    emptied = int(bool(g.live) and not residual)

    g.live = residual
    if marked:
        # Deliberately arbitrary residual pivot; C-HD uses a minimum-label pivot.
        g.pivot = rng.choice(tuple(residual))

    return meeting, marked, emptied


def run_trial(rng, max_groups=24, max_group_size=16, max_children=8):
    p = rng.randint(1, max_groups)
    H = rng.randint(1, max_children)

    groups = []
    own_groups = 0
    for _ in range(p):
        n = rng.randint(1, max_group_size)
        homes = tuple(rng.randint(0, H) for _ in range(n))
        if 0 in homes:
            own_groups += 1
        groups.append(make_group(homes, rng))

    init_nonempty = sum(bool(g.live) for g in groups)
    assert init_nonempty == p

    total_meetings = 0
    total_marked = 0
    total_emptied = 0

    for child in range(1, H + 1):
        m_i = r_i = e_i = 0
        for g in groups:
            m, r, e = step_group(g, child, rng)
            m_i += m
            r_i += r
            e_i += e

        if r_i + e_i > m_i:
            return {
                "ok": False,
                "failure": "per_iteration",
                "child": child,
                "meeting": m_i,
                "marked": r_i,
                "emptied": e_i,
            }

        total_meetings += m_i
        total_marked += r_i
        total_emptied += e_i

    final_nonempty = sum(bool(g.live) for g in groups)

    if final_nonempty + total_emptied != p:
        return {
            "ok": False,
            "failure": "emptying_telescope",
            "p": p,
            "final_nonempty": final_nonempty,
            "total_emptied": total_emptied,
        }

    if final_nonempty != own_groups:
        return {
            "ok": False,
            "failure": "own_groups",
            "final_nonempty": final_nonempty,
            "own_groups": own_groups,
        }

    if total_marked + p > total_meetings + own_groups:
        return {
            "ok": False,
            "failure": "aggregate",
            "total_marked": total_marked,
            "p": p,
            "total_meetings": total_meetings,
            "own_groups": own_groups,
        }

    return {
        "ok": True,
        "p": p,
        "children": H,
        "own_groups": own_groups,
        "total_meetings": total_meetings,
        "total_marked": total_marked,
        "total_emptied": total_emptied,
        "final_nonempty": final_nonempty,
        "slack": total_meetings + own_groups - (total_marked + p),
    }


def run(trials=200_000, seed=20260923):
    rng = random.Random(seed)
    slacks = []
    marked = []
    meetings = []

    for t in range(trials):
        r = run_trial(rng)
        if not r["ok"]:
            r["trial"] = t
            return {
                "seed": seed,
                "requested_trials": trials,
                "completed_trials": t + 1,
                "violations": 1,
                "counterexample": r,
            }
        slacks.append(r["slack"])
        marked.append(r["total_marked"])
        meetings.append(r["total_meetings"])

    return {
        "seed": seed,
        "requested_trials": trials,
        "completed_trials": trials,
        "violations": 0,
        "mean_aggregate_slack": sum(slacks) / len(slacks),
        "max_aggregate_slack": max(slacks),
        "tight_fraction": sum(s == 0 for s in slacks) / len(slacks),
        "mean_marked_events": sum(marked) / len(marked),
        "mean_child_group_meetings": sum(meetings) / len(meetings),
        "checked_properties": [
            "marked_i + emptied_i <= meetings_i for every child",
            "final_nonempty + total_emptied == p",
            "final_nonempty == own_groups",
            "total_marked + p <= total_meetings + own_groups",
        ],
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--trials", type=int, default=200000)
    ap.add_argument("--seed", type=int, default=20260923)
    ap.add_argument(
        "--summary",
        type=Path,
        default=Path("results/loop_telescope_summary.json"),
    )
    args = ap.parse_args()

    summary = run(args.trials, args.seed)
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    args.summary.write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2))
    if summary["violations"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
