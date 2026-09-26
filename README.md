# Pivot: tightening C-HD pivot re-selection accounting

This repository investigates a possible tightening of the cost analysis in
[C-HD](https://github.com/spicylemonade/c-hd-proof), the formally verified
directed SSSP construction discussed by Vals in
["We Found a Faster Shortest Path Algorithm"](https://vals.ai/blogs/faster-shortest-path-algorithm).

## Status

**Research hypothesis, not a proved improved SSSP theorem.**

The upstream C-HD result remains unchanged. The strongest finding so far is
a tightening of the full-call BM.23 accounting:

1. C-HD charges pivot re-selections using `g_j <= 1 + c_j`; the executable
   semantics only re-select when the residual group is nonempty, and the
   candidate Lean chain supports the sharper `g_j <= c_j` accounting.
2. BM.6 raw insertion into a fresh one-block DLazy structure is O(1) per
   pivot, but the current DLazy **amortized potential** can increase by
   Theta(t) per pivot. Therefore BM.6 still carries a Theta(t p)-scale
   deferred-work term in the existing end-to-end proof.

If the BM.6 amortized preload term can also be removed or bypassed, the
parameter balance
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
See [`notes/new_parameter_route.md`](notes/new_parameter_route.md) for the square-root parameter retuning argument.
See [`notes/prior_work.md`](notes/prior_work.md) for the dated prior-work audit.
See [`notes/proof_status.md`](notes/proof_status.md) for a strict separation between kernel-checked local accounting results and the remaining integration obligations.
See [`notes/fresh_init_amortization_blocker.md`](notes/fresh_init_amortization_blocker.md) for the current main obstacle to the square-root retuning.

The main candidate Lean modules are checked in GitHub Actions against the pinned upstream C-HD snapshot. The current checked chain includes:
- exact marked/emptied finite-set accounting;
- the refined one-step insertion-credit inequality;
- the loop insertion-credit telescope;
- the final residual-group/W' bound;
- the refined own-home colour inequality;
- the full-call terminal credit theorem;
- full-call cost assembly under a cheap BM.6 initialization bound;
- the final natural-number cancellation of the expensive `I * p` term.

The latest green candidate workflow is run `36231171985`. All 31
candidate modules in that workflow compile successfully against the pinned
upstream snapshot.

The checked chain now includes not only the N4-side accounting and recursive
credit transport, but also the first batched-FindPivots correctness/cost
building blocks:

- one failed final `val` region can serve multiple Q roots;
- complete closed cores remain stable under later monotone label updates;
- scanned-edge certificates survive when the tail label is unchanged;
- canonical dormant contacts create/identify complete targets;
- geometric repair epochs admit a logarithmic count;
- pairwise-disjoint final component vertex sets have total outgoing-edge count
  at most `m`.

The N4-side local accounting is therefore no longer the active bottleneck.
The main asymptotic blocker remains BM.6 for the original constant-`k`
route: cheap raw insertion still creates Theta(t p)-scale DLazy potential.

The active second route keeps that BM.6 term, takes `k = Theta(t)`, and
tries to replace one-local-search-per-root FindPivots by shared dormant
components.  The current conditional cost target is roughly

```text
O((N log N / t + m t) polylog t),
```

which would still beat the current `11/12` showcase exponent if the
remaining strict-label-change / incremental-repair work can be given the same
event-based global charge.

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

### Exhaustive own-home colour check

Command:

```bash
python experiments/own_home_colour.py --max-n 6 --num-homes 3
```

Committed summary: [`results/own_home_colour_summary.json`](results/own_home_colour_summary.json).

Result:

```text
group subsets checked: 5,699,730
violations:             0
```

For every nonempty group subset of every parent-first tree up to 6 vertices
with 3 home colours, the checker verifies

```text
child homes represented + own-home indicator
    = distinct homes represented

distinct homes represented - 1
    <= bichromatic parent edges of the containing piece.
```

This directly falsification-tests the proposed
`mkOf + ownGroupsOf <= p + bich` bridge.

The refined one-step cost algebra was also exhaustively checked on 85,293
small natural-number assignments; see
[`results/iter_cost_arithmetic_summary.json`](results/iter_cost_arithmetic_summary.json).

These experiments are **falsification tests, not a proof**.

## Reproduce

No third-party Python packages are required.

```bash
git clone https://github.com/Anormalm/pivot.git
cd pivot

python experiments/reselection_exhaustive.py
python experiments/random_reselection.py --trials 50000 --seed 20260923
python experiments/loop_telescope.py --trials 200000 --seed 20260923
python experiments/own_home_colour.py --max-n 6 --num-homes 3
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

The N4-side full-call cancellation is represented by kernel-checked candidate
lemmas. The next research target is no longer just cost-interface plumbing:

1. keep integrating the N4 credit through `CostLog/CostLe` so the local
   improvement is formally reusable;
2. resolve the BM.6 preload potential identified in
   `notes/fresh_init_amortization_blocker.md`;
3. investigate a bulk initialization / alternative priority structure, or a
   second FindPivots improvement that permits larger `k`;
4. only after that revisit the constant-`k`,
   `t = Theta(sqrt(N log N / m))` retuning.

The `O(sqrt(m N log N))` expression is a conditional target, not a theorem
supported by the current DLazy amortized analysis.


## Important BM.6 caveat

The repository originally separated the raw BM.6 insertion cost from the generic evolved-structure insertion cost. That direct-operation observation is correct, but it is not enough for the master bound.

The existing Layer-A proof charges:

```text
actual insertion work + increase in DLazy potential
```

and that fresh one-block potential contains a logarithmic `S_M` term. When the initial pivot block is much larger than its local block parameter `M`, the amortized charge can be `Theta(t)` per pivot even though the physical insertion is constant-time.

See:
- [`notes/fresh_init_potential_blocker.md`](notes/fresh_init_potential_blocker.md)
- [`experiments/fresh_potential_growth.py`](experiments/fresh_potential_growth.py)
- [`results/fresh_potential_growth_summary.json`](results/fresh_potential_growth_summary.json)

Accordingly, the `O(sqrt(m N log N))` / `11/12 -> 7/8` consequence remains a research target, not a consequence of the already-green N4 accounting patch alone.
