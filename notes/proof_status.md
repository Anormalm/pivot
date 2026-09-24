# Proof status

Date: 2026-09-24

This note separates what is already elementary/source-level from what still
has to be proved inside the upstream C-HD formal cost chain.

## Established / locally compiled against the upstream snapshot

### 1. Exact one-group re-selection combinatorics

For a nonempty group whose members are partitioned into child homes plus the
parent-own/final home, the adversarial maximum number of expensive BM.23
re-selections is exactly

```text
#child homes                  if the own/final home is represented
#child homes - 1              otherwise
```

equivalently

```text
max reselections = #represented homes - 1.
```

This is an elementary case analysis and is independently checked by
`experiments/exact_characterization.py` on 585,978 states.

### 2. Fresh BM.6 insertion is linear in the number of pivots

The upstream DLazy source already proves that:

- `newC` creates a one-block structure;
- `Insert` does not split blocks;
- the list insertion cost is bounded by
  `length * (log2(#blocks) + 4)`.

Therefore BM.6 insertion into the fresh structure is `O(p)`, not
`O(t p)`. See `notes/fresh_insert_audit.md`.

### 3. Loop telescope holds in the abstract home model

For the actual marked/emptied definitions abstracted at the home level:

```text
marked_i + emptied_i <= meetings_i
final_nonempty + total_emptied = p
final_nonempty = own_groups
```

hence

```text
total_marked + p <= total_meetings + own_groups.
```

A 200,000-trial direct loop-state stress test produced zero violations.
See `experiments/loop_telescope.py` and
`results/loop_telescope_summary.json`.

These experiments are falsification tests, not formal proof objects.

### 4. Own-home colour bridge survives exhaustive finite checking

The proposed per-group strengthening

```text
#children meeting P + [P contains an own/none home]
    <= #distinct homes(P)
```

combined with the existing upstream colour lemma was checked on
**5,699,730** nonempty group subsets of parent-first trees up to 6 vertices,
with zero violations.

A generic source-aligned candidate strengthening of
`Ranges.card_children_meeting_le` is in
`drafts/HomeOwnColourCandidate.lean`.

## Already available upstream and intended to be reused

The C-HD snapshot already proves the tree-colour side:

```text
#distinct homes in a containing PT piece - 1
    <= #bichromatic parent edges in the piece.
```

It also already charges bichromatic tree edges to `Cr` / `Be`, and for
full calls proves `S_X subset U_X`.

The proposed refinement should therefore be a cost-accounting patch, not a
new shortest-path correctness argument.

## Kernel-checked candidate chain

GitHub Actions checks the candidate modules against the exact audited C-HD snapshot
`98c53accb47a505482a1781597ae14bf67e81cec` using Lean 4.34.0.

The latest green run is:

```text
workflow: Lean candidate checks
run:      35956298994
branch:   loop-telescope
result:   success
```

The following modules compiled successfully in that run:

- `LoopCostFiniteCandidates.lean`
  - exact nonempty/emptying partition;
  - emptied groups meet the child;
  - marked/emptied disjointness;
  - marked + emptied <= meetings.
- `IterCostRefinedCandidate.lean`
  - refined one-step cost with `I * emptied` credit.
- `LoopCostInsertCreditCandidate.lean`
  - telescopes the `I`-weighted emptying potential through the actual loop.
- `FinalResidualCandidate.lean`
  - bounds final nonempty groups by original groups meeting `W'`.
- `HomeOwnColourCandidate.lean`
  - adds the distinct own/`none` home colour.
- `MkOwnColourCandidate.lean`
  - aggregate `mkOf + ownGroups <= p + |Cr| + |Be|` bridge.
- `FullTerminalCreditCandidate.lean`
  - converts the loop-final nonempty potential into terminal own-group credit.
- `CallCostFullCreditCandidate.lean`
  - assembles a full-call record-cost inequality with `+ I * p` on the left,
    assuming a cheap BM.6 initialization bound.
- `RecCostCreditCandidate.lean`
  - generic record-local credit predicate.
- `LoopRecCostCreditCandidate.lean`
  - structural transport of record-local credit through shifted/appended child logs.
- `FreshInsertCandidate.lean`
  - fresh one-block insertion cost bound.
- `FullCreditCancellationCandidate.lean`
  - arithmetic cancellation of the expensive `I * p` term using the refined
    `mk + own` bound.

A direct audit of these 12 files found:

```text
sorry: 0
admit: 0
```

So the central N4-side local accounting result is no longer merely an uncompiled
sketch. It is represented by kernel-checked, hole-free candidate lemmas against
the pinned upstream source.

## What is still not proved

### P1. Recursive root-record credit integration

The structural `RecCostCredit` and loop transport lemmas compile, and the
full-call root cost theorem compiles, but they still need to be joined into a
replacement for upstream:

```text
callC_reccost
bmsspC_reccost
```

that preserves the full-call `I * p` credit all the way to `CostLe`.

This is now primarily proof plumbing rather than a missing combinatorial idea.

### P2. BM.6 fresh-insertion interface integration

The concrete fresh insertion lemma is compiled:

```text
fresh one-block BM.6 insertion = O(p)
```

but upstream `BMCost.initCost` still definitionally uses the ordinary
evolved-structure field `DC.ins`.

The attempted `DCost.initIns` interface experiment correctly exposed the
patch radius:

- named `DCost` constructors;
- four positional zero-cost constructors;
- `callC_cost`;
- `budOf / callC_reccost / bmsspC_reccost`;
- ultimately the master instantiation.

The first experiment failed because those downstream constructors/theorems had
not yet been updated, not because the fresh-insertion lemma failed.

### P3. Refined global `CostLe` theorem

The local arithmetic cancellation theorem compiles, but upstream
`tracedCounters_cost_le` still consumes the old `RecCost/budOf` shape with
an unconditional expensive `t * p` term.

A refined version must consume the credit-carrying record facts and use:

```text
mkOf + ownGroups <= p + |Cr| + |Be|
```

to cancel the full-call insertion credit.

Partial calls can retain the existing `t * |S|` absorption.

### P4. New master parameter layer

Only after P1--P3 are integrated should the frozen parameter program be changed.

Candidate choice:

```text
k = 4
t = Theta(sqrt(N log N / m))
L = Theta(log N / t)
```

The target core expression is

```text
O(N log N / t + m t)
  = O(sqrt(m N log N)).
```

The repository already contains a source-level parameter audit showing that the
visible lower-order terms remain below this candidate envelope on the current
C-HD density branch, but the corresponding Lean master theorem has not yet
been rebuilt.

At `m = n log^(3/4) n`, the conditional exponent change remains:

```text
11/12 -> 7/8
```

## Claim discipline

At the current checkpoint it is accurate to say:

- the proposed N4 tightening is supported by a direct paper-level argument;
- the local full-call accounting/cancellation lemmas are kernel-checked against
  the pinned C-HD snapshot;
- the fresh BM.6 one-block insertion bound is kernel-checked;
- the final improved SSSP complexity theorem is **not** yet proved.

The repository should still avoid claiming a completed
`O(sqrt(m N log N))` directed SSSP theorem until the recursive cost-log,
fresh-init interface, global CostLe, and parameter/master layers are integrated.
