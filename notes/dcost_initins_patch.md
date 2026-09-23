# DCost fresh-initialization interface patch experiment

## Proposed minimal semantic change

Add one field to `BMCost.DCost`:

```lean
initIns : ℕ → ℕ
```

Interpretation: cost of an insertion during BM.6 into the newly-created level structure.

Keep the existing

```lean
ins : ℕ → ℕ
```

for all evolved-structure insertions (BM.23, BM.25, BM.27--28, etc.).

Change only recursive-call initialization:

```lean
initCost DC lv p P =
  DC.new lv + sum_j |P_j| + p * (2 + DC.initIns lv).
```

## C-HD instantiation

For the concrete DLazy C-HD instance, use a constant fresh insertion bound. The compiled candidate theorem

```text
fresh_insManyC_cost_le_candidate <= 4 * list.length
```

supports `initIns l = 4` at the Layer-A DLazy operation-cost level.

The ordinary evolved insertion field remains

```text
ins l = chdIns t k delta L0 l = O(t).
```

## Explicit constructors found in the frozen snapshot

Only the named `DCost where` constructors found by code search need a new field:

1. `Frontier/CHD/BMTeleChd.lean` — real C-HD amortized DLazy costs.
2. `Frontier/CHD/L6/DCap.lean` — L6 placeholder/capacity cost object.

Any other uses are parameterized by `DCost` and should elaborate once the field is added.

Suggested values:

```lean
-- BMTeleChd
initIns := fun _ => 4

-- L6/DCap placeholder
initIns := fun _ => 0
```

## Expected proof obligations

1. Update `initCost`.
2. In the DLazy-to-BMSSPC simulation, replace the generic insertion-cost bound for BM.6 by the existing fresh-list theorem.
3. The RAM prologue already exposes the exact `insManyC ... (newC ...)` cost, so discharge it with the one-block bound.
4. Base-case heap/conversion accounting remains on `bins` / ordinary `ins 0`; it need not use `initIns` for this refinement.

## Why this field is preferable to changing the algorithm

The executable program already performs the cheap operation. The current abstraction merely prices it with the worst-case evolved insertion cost. `initIns` makes the cost interface reflect the existing phase distinction without changing data-structure semantics.