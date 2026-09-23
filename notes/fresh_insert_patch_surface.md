# Fresh-insert interface patch surface

Upstream snapshot: `98c53acc...`.

## Current interface

`BMCost.DCost` exposes one generic insertion cost:

```lean
ins : Nat -> Nat
```

and `initCost` uses it for BM.6:

```lean
DC.new lv + sum_j |P_j| + p * (2 + DC.ins lv)
```

This is the source of the artificial `O(t p)` initialization charge.

## Candidate interface change

Add one field:

```lean
initIns : Nat -> Nat
```

with the meaning:

> cost of one insertion during BM.6 into the newly-created level structure.

Then change only the initialization formula:

```lean
initCost DC lv p P :=
  DC.new lv
  + sum_j |P_j|
  + p * (2 + DC.initIns lv)
```

All later insertions continue to use `DC.ins lv`.

## C-HD instantiation

The audited DLazy facts and the compiled
`fresh_insManyC_cost_le_candidate` give a constant abstract cost on a fresh
one-block structure:

```text
insManyC fresh <= 4 * number_of_pivots.
```

So the natural C-HD setting is

```lean
initIns := fun _ => 4
```

(up to a slightly larger fixed constant if the surrounding RAM charge wants
one).

The evolved insertion cost remains

```lean
ins := chdIns t k delta L0
```

and is still `O(t)`.

## Constructor surface found

The audit found the C-HD cost constructors at:

- `Frontier/CHD/BMTeleChd.lean`
  - `chdDC (t k delta L0) DCb : DCost`
- `Frontier/CHD/L6/DCap.lean`
  - the L6 `chdDC` wrapper used for capacity/cost plumbing.

The first gets the real constant fresh-insert cost.  The L6 dummy/capacity
wrapper should receive the corresponding bookkeeping value (its current
ordinary `ins` fields are zero in that layer).

## Proof sites affected

The semantic `CallC` record stores

```text
cost := cfp + initCost DC ... + loop + merge + finCost ...
```

so the record shape does not change.

The main proof updates are:

1. `BMCost.initCost`: use `initIns`.
2. concrete DLazy simulation / `BMTeleLoop`: discharge the new init charge
   using the compiled fresh-list bound.
3. `LoopCost.callC_cost`: replace
   `p * (2 + I)` with `p * (2 + initI)`, where `initI=O(1)`.
4. RAM prologue: no algorithm change is required; `RamBodyPro` already
   exposes the exact `insManyC` cost for the initial pivot list.

## Why this is preferable to a special-case theorem only

Leaving `DCost.ins` unchanged in `initCost` means the abstract `CallC`
log continues to record the larger `O(t p)` cost even if the concrete RAM
execution is cheaper.  The later master proof cannot recover the lost
factor.

Separating `initIns` at the cost-interface level ensures the improved
accounting survives all the way into `CostLog` and `CostLe`.
