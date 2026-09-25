#!/usr/bin/env python3
"""Concrete bounded-FindPivots scan-reuse experiment.

This is a numeric simplification of FH.4--FH.24. It keeps the algorithmic
features relevant to repeated failed-search work:

- bounded local Dijkstra heap;
- K / val distinction;
- exact/equal relaxations count as valid;
- failed searches have H empty and |K| < k;
- dormant cache stores a closed outgoing scan keyed by the tail label value.

Two synthetic families are included:

stable:
  many roots enter the same downstream tight region with the same labels.
  The first failed search closes that region; later searches can reuse its
  scans because the cached tail labels are unchanged.

decreasing:
  each later root supplies a strictly better path into the shared region.
  Tail labels change, invalidating the cache and forcing re-scans.

The model is intended to test the proposed cache mechanism, not reproduce the
full walk-label order or prove C-HD correctness.
"""

import argparse
import csv
import heapq
from dataclasses import dataclass
from math import inf
from pathlib import Path


@dataclass
class Stats:
    searches: int = 0
    skipped_roots: int = 0
    extracts: int = 0
    edge_scans: int = 0
    cache_hits: int = 0
    strict_decreases: int = 0


def relax(d, u, v, w, B, stats):
    cand = d[u] + w
    if cand >= B:
        return False
    if cand <= d[v]:
        if cand < d[v]:
            d[v] = cand
            stats.strict_decreases += 1
        return True
    return False


def run(adj, labels, roots, k, B, reuse=False):
    d = dict(labels)
    st = Stats()
    dormant_regions = []
    cache_label = {}

    # Current implementation-style successful marking; these experiments are
    # configured so all searches fail.
    marked = set()

    for x in roots:
        if x in marked:
            continue

        if reuse:
            owner = next((V for V in dormant_regions if x in V), None)
            if owner is not None:
                st.skipped_roots += 1
                continue

        st.searches += 1
        H = [(d[x], x)]
        in_heap = {x}
        K = {x}
        val = {x}
        done = set()

        while H and len(K) < k:
            key, u = heapq.heappop(H)
            if u not in in_heap or key != d[u]:
                continue
            in_heap.remove(u)
            done.add(u)
            st.extracts += 1

            if reuse and cache_label.get(u) == d[u]:
                # Closed.grows-style reuse: tail key unchanged, heads only
                # move downward, so the old outgoing closure remains valid.
                st.cache_hits += 1
                continue

            for v, w in adj.get(u, []):
                cand = d[u] + w
                if cand >= B:
                    break
                st.edge_scans += 1

                ok = relax(d, u, v, w, B, st)

                if v not in K:
                    K.add(v)
                    if ok:
                        val.add(v)
                        heapq.heappush(H, (d[v], v))
                        in_heap.add(v)
                    if len(K) >= k:
                        break
                elif ok and v not in done:
                    val.add(v)
                    heapq.heappush(H, (d[v], v))
                    in_heap.add(v)

            if reuse:
                cache_label[u] = d[u]

        if len(K) >= k:
            marked.update(K)
        else:
            # Failure: H exhausted, retain final val as dormant.
            dormant_regions.append(set(val))
            if reuse:
                for u in done:
                    cache_label[u] = d[u]

    return st


def shared_chain(q, h, changing):
    """q roots feeding the same h-vertex tight chain."""
    roots = [f"r{i}" for i in range(q)]
    common = [f"v{j}" for j in range(h)]
    adj = {}
    labels = {}

    # Common chain starts at 100,101,...
    for j, v in enumerate(common):
        labels[v] = 100.0 + j
        adj[v] = []
        if j + 1 < h:
            adj[v].append((common[j + 1], 1.0))

    for i, r in enumerate(roots):
        labels[r] = 0.0
        # Stable: every root reconfirms v0 at 100.
        # Decreasing: later roots improve v0 by one, propagating through chain.
        w = 100.0 if not changing else 100.0 - i
        adj[r] = [(common[0], w)]

    # Keep each adjacency list sorted by weight/head, matching prefix scans.
    for u in adj:
        adj[u].sort(key=lambda x: (x[1], x[0]))

    return adj, labels, roots


def experiment():
    rows = []
    for h in [8, 16, 32, 64]:
        q = min(h, 32)
        k = h + 2
        B = 1000.0
        for mode, changing in [("stable", False), ("decreasing", True)]:
            adj, labels, roots = shared_chain(q, h, changing)
            base = run(adj, labels, roots, k, B, reuse=False)
            cached = run(adj, labels, roots, k, B, reuse=True)
            rows.append({
                "mode": mode,
                "q": q,
                "h": h,
                "k": k,
                "baseline_searches": base.searches,
                "cached_searches": cached.searches,
                "baseline_edge_scans": base.edge_scans,
                "cached_edge_scans": cached.edge_scans,
                "cache_hits": cached.cache_hits,
                "strict_decreases": cached.strict_decreases,
                "scan_reduction_factor":
                    base.edge_scans / max(1, cached.edge_scans),
            })
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path,
        default=Path("results/dormant_findpivots_sim.csv"))
    args = ap.parse_args()

    rows = experiment()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=rows[0].keys())
        w.writeheader()
        w.writerows(rows)

    for row in rows:
        print(row)


if __name__ == "__main__":
    main()
