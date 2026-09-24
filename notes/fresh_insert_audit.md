# Fresh BM.6 insertion audit

**Status:** source-level conclusion supported directly by existing upstream Lean lemmas.  
**Upstream snapshot:** `98c53accb47a505482a1781597ae14bf67e81cec`.

## Conclusion

The BM.6 pivot insertions into the newly created DLazy structure have

```text
O(p)
```

**raw operation cost** at the concrete/Layer-A insertion level.

This does **not** imply O(p) amortized cost in the existing full proof.
`BMTeleLoop` uses a family potential to pre-pay the lazy splitting work
created by a large unsplit block. For `p/M = 2^t`, that potential can grow
as Theta(p t).

Therefore the generic O(t) BM.6 charge is coarse as a statement about raw
insertion time, but its asymptotic scale is not currently removable from the
end-to-end amortized proof. See
`notes/fresh_init_amortization_blocker.md`.

## 1. New structure has one block

`BMLazy.lean`:

```lean
def newC (M : ℕ) (Bd : WLab G s) : DStrM G s :=
  ⟨M, Bd, [⟨⊥, []⟩]⟩
```

Therefore

```text
(newC M Bd).blocks.length = 1.
```

## 2. Insert never changes block count

`DLazyFacts.lean` proves:

```lean
theorem insertL_blocks ... :
  (DL.insertL ... D ...).2.2.1.blocks.length = D.blocks.length
```

and its list form:

```lean
theorem insManyC_blocks ... :
  (insManyC ... l g D).2.1.blocks.length = D.blocks.length
```

Thus every BM.6 insertion starting from `newC` sees exactly one block.

This is also the implementation design documented in `DInsertL.lean` and
the paper: `Insert` never splits; splitting is lazy and occurs only during
front preparation for `Pull`.

## 3. Existing cost lemma immediately gives <= 4 per insert

`DLazyFacts.lean`:

```lean
theorem insManyC_cost_le (T0) (f) (NB) :
  ...
  D.blocks.length ≤ NB ->
  (insManyC ... l g D).2.2
    ≤ l.length * (Nat.log 2 NB + 4)
```

Instantiate

```text
D  = newC M B
NB = 1.
```

Since `Nat.log 2 1 = 0`,

```text
insManyC_cost <= 4 * l.length.
```

For the BM.6 pivot list `lpiv`, the existing prologue invariants give one
pivot per nonempty group and `lpiv.length = p`. Hence

```text
BM.6 abstract DLazy insertion cost <= 4p.
```

The exact single-insert definition is consistent with this.
`RelaxIns.lean` proves:

```lean
insC_dl_cost :
  (insC ... Dc ...).2.2 =
    if skipIns ... then 2
    else DL.bsCost Dc.blocks.length + 3
```

With one block, the non-skipped branch is constant.

## 4. Concrete RAM prologue already exposes the exact list cost

`RamBodyPro.lean` contains the bound

```lean
r7.cost ≤ r1.cost
  + (DL.K + 28 + (DL.K + 53) * p + 41 * ∑ j, (P j).card)
  + DL.K *
      (BM.insManyC (dlOps G s) ... (List.ofFn piv) g
        (newC (Mf (l + 1)) B)).2.2
```

Substituting the existing `insManyC_cost_le` result gives

```text
RAM prologue cost
  <= O(p + Σ_j |P_j|)
```

with constants depending only on the fixed RAM refinement factor `DL.K`,
not on the asymptotic block parameter `t`.

Since the pivot groups are pairwise disjoint subsets of `S`,

```text
Σ_j |P_j| <= |S|.
```

So BM.5--8 are already concretely bounded by

```text
O(|S| + p)
```

apart from fixed per-call constants.

## 5. Where the overcharge enters

`BMCost.lean` defines:

```lean
noncomputable def initCost (DC : DCost) (lv p : ℕ)
    (P : Fin p → Finset (Fin G.n)) : ℕ :=
  DC.new lv + ∑ j, (P j).card + p * (2 + DC.ins lv)
```

The same `DC.ins lv` is used for later inserts into an evolved multi-block
structure.

For C-HD, that generic evolved insertion bound is `O(t)`, so the abstract
trace turns the concretely linear BM.6 phase into

```text
O(t p).
```

This is exactly one of the terms preventing constant `k`.

## 6. Earlier interface-only repair and why it is insufficient

The clean generic repair is to distinguish fresh insertion from ordinary
insertion in the cost interface.

For example:

```lean
structure DCost where
  M       : ℕ → ℕ
  new     : ℕ → ℕ
  initIns : ℕ → ℕ
  ins     : ℕ → ℕ
  ...
```

and

```lean
initCost DC lv p P :=
  DC.new lv
  + ∑ j, (P j).card
  + p * (2 + DC.initIns lv)
```

At the raw-cost interface one can set `initIns(l)=4`, and this patch was
successfully threaded through the abstract cost stack. The full telescoping
proof then fails in `BMTeleLoop`, because the post-initialization potential
cannot be bounded by `4p`.

So a separate `initIns` field is not sufficient unless accompanied by a new
potential theorem or a changed initialization/data structure.

## 7. Why this matters to the candidate exponent

Even if full-call BM.23 re-selection is improved to remove its once-per-group
`O(t p)` charge, leaving `initCost` unchanged would still contribute

```text
O(t p).
```

Since the full-call pivot mass is roughly `O(N/k)` per layer, that term
recreates

```text
O(N t / k)
```

and forces the old `k ≈ sqrt(t)` balance.

The N4 refinement removes one source of O(t p), but the existing BM.6
amortization still leaves another. A new exponent therefore needs an
additional algorithmic/amortized insight beyond the N4 accounting fix.
