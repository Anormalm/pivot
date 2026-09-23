# Pivot: tightening C-HD pivot re-selection accounting

This repository investigates a possible tightening of the cost analysis in
[C-HD](https://github.com/spicylemonade/c-hd-proof), the formally verified
directed SSSP construction discussed by Vals in
["We Found a Faster Shortest Path Algorithm"](https://vals.ai/blogs/faster-shortest-path-algorithm).

## Status

**Research hypothesis, not a proved improved SSSP theorem.**

The upstream C-HD result remains unchanged. This repository isolates two
places where its current cost accounting appears deliberately coarse:

1. full-call BM.23 pivot re-selections are charged using
   `g_j <= 1 + c_j`; the executable semantics only re-select when the
   residual group is nonempty, suggesting a `g_j <= c_j` refinement;
2. BM.6 initial pivots are charged using the generic insertion cost even
   though they are inserted into a fresh one-block data structure and
   `Insert` does not split.

If both refinements are proved in the C-HD cost model, the parameter balance
changes from

```text
k = Theta(sqrt(t))
t = Theta((N log N / m)^(2/3))
```

to the candidate choice

```text
k = 4
t = Theta(sqrt(N log N / m))
```

and the core term would change from

```text
m^(1/3) (N log N)^(2/3)
```

to

```text
sqrt(m N log N).
```

At `m = n log^(3/4) n`, this is the conditional exponent change

```text
n log^(11/12) n  ->  n log^(7/8) n.
```

See [`notes/analysis.md`](notes/analysis.md) for the derivation and the exact
remaining proof obligations.
See [`notes/lean_patch_plan.md`](notes/lean_patch_plan.md) for the file-by-file Lean patch plan.
See [`notes/prior_work.md`](notes/prior_work.md) for the dated prior-work audit.
See [`notes/proof_status.md`](notes/proof_status.md) for a strict separation between established combinatorics, source-level overcharges, and the remaining Lean obligations.
The first uncompiled source-aligned proof sketch is in [`drafts/loop_cost_refinement.md`](drafts/loop_cost_refinement.md).

## Why the `+1` looks removable

C-HD's executable semantics define a group as needing BM.23 re-selection only
when

```text
current pivot is in U_i
AND
P_j \ U_i is nonempty.
```

For a **full** call, the upstream formal invariant `RecFacts.full_S` says the
original frontier `S` is contained in the returned set `U`. Every nonempty
pivot group is contained in `S`. Consequently, the final represented
"home" of a group empties the group and causes no BM.23 insertion.

This suggests

```text
actual reselections for P_j
    <= (# homes represented in P_j) - 1.
```

The upstream `Reselect.lean` machinery already proves the tree-colour fact

```text
(# homes in a containing PT piece) - 1
    <= (# bichromatic parent edges in that piece).
```

Because MakePivots associates nonempty groups with distinct pieces, the
candidate full-call charge is cross-edge-only, without a once-per-group term.

## Local experiments

All results below were generated locally from the scripts in
[`experiments/`](experiments/).

### Exhaustive group/home check

Command:

```bash
python experiments/reselection_exhaustive.py
```

The committed run exhaustively checked **123,004** group/home states under a
model *more permissive than C-HD*: after every re-selection, the next pivot
may be chosen adversarially from any residual member rather than being the
minimum-label member.

Observed:

```text
actual reselections <= represented homes - 1
```

in every tested state.

### Exhaustive rooted-tree colour check

The same script enumerated parent-first rooted trees up to 7 vertices and all
3-colourings: **1,668,504** cases.

Observed:

```text
#colours - 1 <= #bichromatic parent edges
```

in every case. This is only an independent sanity check; C-HD already
formalizes the relevant combinatorial inequality.

### Random stress test

Command:

```bash
python experiments/random_reselection.py \
  --trials 50000 \
  --seed 20260923
```

Committed summary: [`results/random_summary.json`](results/random_summary.json).

Result:

```text
trials:      50,000
violations:  0
max n:       24
max homes:   8
```

For each trial the experiment samples a parent-first tree, a home assignment,
and a pivot group, then compares:

```text
actual maximum BM.23 reselections
current generic charge:  1 + bichromatic_edges
candidate charge:        bichromatic_edges
```

The candidate charge was never violated in the run.

### Direct loop-telescope stress test

Command:

```bash
python experiments/loop_telescope.py \
  --trials 200000 \
  --seed 20260923
```

Committed summary: [`results/loop_telescope_summary.json`](results/loop_telescope_summary.json).

Result:

```text
trials:      200,000
violations:  0
```

This test exercises the aggregate bookkeeping needed by the proposed Lean
patch, checking on every sampled full-call loop:

```text
marked_i + emptied_i <= meetings_i
final_nonempty + total_emptied = p
final_nonempty = own_groups
total_marked + p <= total_meetings + own_groups
```

Unlike the single-group stress test, this directly tests the telescope that
would replace the current coarse child-meeting charge.

These experiments are **falsification tests, not a proof**.

## Reproduce

No third-party Python packages are required.

```bash
git clone https://github.com/Anormalm/pivot.git
cd pivot

python experiments/reselection_exhaustive.py
python experiments/random_reselection.py --trials 50000 --seed 20260923
python experiments/loop_telescope.py --trials 200000 --seed 20260923
python experiments/exponent_sweep.py
```

Python 3.10+ is recommended.

## Exact upstream locations audited

The analysis was checked against the C-HD snapshot at commit
`98c53accb47a505482a1781597ae14bf67e81cec`, especially:

- `paper/PAPER.md`, §5.3--§6
- `formal/lean/Frontier/CHD/BM.lean`
  - `Reselect`
  - `reselected`
- `formal/lean/Frontier/CHD/BMCost.lean`
  - `markedGroups`
  - `iterCost`
  - `initCost`
- `formal/lean/Frontier/CHD/BMTrace.lean`
  - `RecFacts.full_S`
- `formal/lean/Frontier/CHD/Reselect.lean`
  - `colors_le_measure`
  - `pieces_colors_le`
  - `groups_colors_le`
- `formal/lean/Frontier/CHD/CrBe.lean`
  - `bich_le_crbe`
  - `mkOf`
  - `mkOf_full_le`
- `formal/lean/Frontier/CHD/RamPiv.lean`
- `formal/lean/Frontier/CHD/BMLazy.lean`

## Prior work

The relevant predecessor is:

- Ran Duan, Xiao Mao, Xinkai Shu, Longhui Yin,
  **A Faster Directed Single-Source Shortest Path Algorithm**, ICALP 2026.
  <https://doi.org/10.4230/LIPIcs.ICALP.2026.81>

Its pivot re-selection analysis carries an exceptional once-per-group charge.
The question here is whether C-HD's richer `home` accounting plus its exact
BM.23 semantics makes that exception unnecessary for full calls.

## Next proof target

The useful theorem is not "the experiments pass." It is a refinement of the
actual loop cost:

```text
Full-call marking lemma:
sum over children i of |markedGroups(sigma_i, U_i)|
    <= total bichromatic FindPivots tree edges.
```

A proof should inject every actual BM.23 marking into a non-final represented
home, then reuse C-HD's existing PT-piece and `Cr/Be` charging lemmas.

Only after that should the master-cost algebra be retuned to `k = 4`.
