# A weaker pull contract appears sufficient for BMSSP correctness

Date: 2026-09-24

This note separates the **correctness requirement** of the BMSSP loop from
the stronger generic D-structure interface currently used by C-HD.

## Current PullSpec

Upstream `PullSpec` requires exact threshold semantics:

```text
y in S0  <->  D[y] = some k and k < Bi.
```

So every stored key below the returned separator must be pulled.

That exact prefix property creates the ordered-bucket comparison barrier for
the initial pivot set.

## What BM.lean actually uses

Auditing every use of `hpull.pulled` in the recursive correctness proof
shows two logically different directions.

### Selected-key soundness

For `x in S0`, `Si_facts` only needs:

```text
exists k:
  D[x] = k
  and k < Bi.
```

This proves every explicitly selected seed lies in the valid A-set/range.

### Certificate coverage

The reverse direction is used only in `certified_mem_expand`.

A certified unresolved vertex y has one of two witnesses:

1. direct exact key:
   ```text
   D[y] = dis(y);
   ```

2. group certificate:
   ```text
   y in P_j
   D[piv_j] = k
   k <= dis(y).
   ```

If `dis(y) < Bi`, correctness needs y itself in S0 in case (1), or the
group pivot in S0 in case (2).

It does **not** use the statement that every arbitrary non-certifying stored
key below Bi is selected.

## Candidate contract

The branch now contains:

`drafts/CertPullSpecCandidate.lean`

with:

```text
selected:
  selected y -> some stored k < Bi

coverExact:
  Complete(y)
  and D[y]=dis(y)
  and dis(y)<Bi
  -> selected y

coverPivot:
  y in P_j
  and Complete(y)
  and D[piv_j]=k <= dis(y)<Bi
  -> selected piv_j

rest:
  selected keys are removed; all others retained

bound:
  Bi <= B

nonempty:
  nonempty D -> nonempty selection
```

The original exact PullSpec implies this contract immediately.

## Source-aligned proof replay

`drafts/CertPullCorrectnessCandidate.lean` replays:

- `Si_facts`
- `certified_mem_expand`
- `UKi_sub`
- `step_pre`
- the two pull-rest lemmas

under the weaker contract.

`drafts/CertPullStepPostCandidate.lean` mechanically replays the complete
`step_post` loop-invariant theorem using the same weaker facts.

These are checked in the pinned Lean workflow.

## Why this matters

If the weaker contract can be implemented without exact rank-partitioning all
low D keys, then the current `PullSpec` ordering cost is stronger than
shortest-path correctness itself requires.

This is the first identified route that could bypass the BM.6 ordered-pivot
barrier **without changing FindPivots or the frontier theorem**.

## Major remaining obstacle: observability

The new contract is semantic.

The algorithm does not know `dis(y)` or `Complete(y)` directly.  A stored
key may be a certificate in the proof even if the implementation cannot
recognize that fact locally.

So weakening the proof interface is only half of the problem.  We still need
a computable data structure / metadata scheme that guarantees coverage of all
semantic certificates more cheaply than returning every low key.

Possible directions:

1. expose certificate provenance explicitly in the state;
2. strengthen FindPivots/sub-call outputs with computable witness metadata;
3. find a sufficient observable superset of certifying keys that has less
   ordering entropy than all D entries;
4. prove that no such observable subset exists under the current state, which
   would turn the ordered-pull heuristic into a stronger architectural
   barrier.

The current result should therefore be read as a **correctness-interface
opening**, not yet a faster algorithm.
