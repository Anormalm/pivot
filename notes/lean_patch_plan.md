# Lean patch plan

This note maps the candidate refinement to the existing C-HD proof structure.
It is a patch plan, not compiled Lean.

Upstream snapshot audited: `98c53accb47a505482a1781597ae14bf67e81cec`.

## Goal

Replace the full-call expensive pivot-group charge

```text
I * (p + |Cr| + |Be|)
```

by

```text
O(k) * p + I * (|Cr| + |Be|)
```

where `I = DC.ins(l) = O(t)` and group size `g = O(k)`.

Separately, re-price the BM.6 insertions into the fresh level structure at
`O(1)` each rather than the generic `I = O(t)` evolved-structure insert cost.

Together these remove the `t * p` contribution that becomes the `t/k` term
in the paper's master bound.

---

## A. Loop-cost refinement

File: `formal/lean/Frontier/CHD/LoopCost.lean`

### A1. Emptying is exact

The current theorem is one-sided:

```lean
card_nonempty_next :
  nonempty(next) + emptied <= nonempty(now)
```

For `P' j = P j \ Ui`, the sets

```text
{j | (P j \ Ui).Nonempty}
{j | P j is nonempty and P j ⊆ Ui}
```

partition the currently nonempty groups.

Add:

```lean
theorem card_nonempty_next_eq (Ui) :
  (Finset.univ.filter (fun j => (σ.P j \ Ui).Nonempty)).card
    + (emptiedGroups σ Ui).card
  =
  (Finset.univ.filter (fun j => (σ.P j).Nonempty)).card
```

No shortest-path facts are needed.

### A2. Empty groups also meet the child

`marked_sub_meeting` already proves this for `markedGroups`.

Add:

```lean
theorem emptied_sub_meeting
    (hsub : ∀ j, σ.P j ⊆ P0 j)
    (Ui) :
  emptiedGroups σ Ui
    ⊆ Finset.univ.filter (fun j => (P0 j ∩ Ui).Nonempty)
```

Proof: choose a member of the nonempty current group; `hsub` puts it in
`P0 j`, and `P j ⊆ Ui` puts it in `Ui`.

`markedGroups` and `emptiedGroups` are disjoint because the first requires
`(P j \ Ui).Nonempty` and the second requires `P j ⊆ Ui`.

Hence:

```lean
theorem marked_emptied_card_le_meeting ... :
  (markedGroups σ Ui).card + (emptiedGroups σ Ui).card
  <=
  (Finset.univ.filter (fun j => (P0 j ∩ Ui).Nonempty)).card
```

### A3. One-step insertion credit

The group-dependent part of `iterCost` is bounded by

```text
g * (marked + emptied)          -- pulled-group expansion
+ (g + 1 + I) * marked         -- BM.23 scan + insertion
```

Therefore

```text
iterCost + I * emptied
```

is bounded by the same ordinary terms plus

```text
(2*g + 1 + I) * meeting.
```

Reason:

```text
g(marked+emptied)
+ (g+1)marked
+ I(marked+emptied)
<= (2g+1+I) meeting.
```

Add a theorem alongside `iterCost_le`, e.g.

```lean
iterCost_le_with_empty_credit
```

with `I * (emptiedGroups σ Ui).card` on the left.

### A4. Telescope the emptying credit

Using `card_nonempty_next_eq`, the sum of `emptiedGroups` over a loop is

```text
nonemptyCount(initial) - nonemptyCount(final).
```

Strengthen/add a loop theorem of the form

```lean
loopC_cost_with_credit :
  c
  + I * (nonemptyCount σ - nonemptyCount σ')
  <=
  1
  + childSum
      (childCharge P0 C0 C1 (2*g + 1 + I))
      lg
  + (1 + I) * J.card
```

up to the same non-group terms already present in `loopC_cost`.

At call entry every `P0 j` is nonempty, so `nonemptyCount(initial) = p`.

---

## B. Convert final residual groups into the missing home colour

Files:
- `formal/lean/Frontier/CHD/CrBe.lean`
- `formal/lean/Frontier/CHD/CostLe.lean`
- possibly `BMTrace.lean` for one child-disjointness transport fact

### B1. Residual group -> own (`none`) home

At the final loop state, `LInv.Pmem` states that every `y ∈ σ.P j` satisfies
`y ∉ σ.U`.

For a full call:

```lean
RecFacts.full_S : r.B' = r.B -> r.S ⊆ r.U
```

and every group is a subset of `S`.

Thus every final residual group vertex is returned by the parent but not by
the loop's accumulated child-return set. Each child `U_Y` is contained in
that accumulated set (`LoopLog.root`), so such a vertex is in no child
`U_Y`.

By the definition of `Ranges.home`:

```text
home_X(y) = none.
```

The clean record-level proxy for final residual groups is:

```lean
ownGroupsOf k r :=
  (groupsOf k r).countP
    (fun g => decide (g.toFinset ∩ r.W').Nonempty)
```

For a full call, every final residual group meets `W'`:
`Pmem` gives `y ∉ σ.U`, while `full_S` and the call result
`U = σ.U ∪ W'` force `y ∈ W'`.

A small additional traced-log fact may be useful:

```text
parent.W' is disjoint from every child.U
```

It follows immediately from `W' ⊆ U_parent \ σ.U` and the loop log's fact
that each child return is accumulated into `σ.U`.

If transporting this through `LogInv` is awkward, prove it as a separate
fact over the traced `BMSSPC` derivation, analogous to `RecFPLog`.

### B2. Refined colour count

Current `mkOf_full_le` proves

```text
mkOf X <= p + |Cr X| + |Be X|.
```

Strengthen it to account for the own colour:

```lean
theorem mk_own_full_le ... :
  mkOf hL k X + ownGroupsOf k (lg.recOf X)
    <=
  (groupsOf k (lg.recOf X)).length
    + (crOf hL X).card
    + (beOf hL X).card
```

Per group:

```text
# children meeting g
+ [g has an own/final member]
<= # distinct home colours of g.
```

Why:
- every meeting child injects as `some Y` via `home_of_mem`;
- an own/final member contributes `none`;
- `none` is distinct from every `some Y`.

Then reuse unchanged:

```lean
Reselect.groups_colors_le
bich_le_crbe
```

to get the RHS.

### B3. Full-call BM.23 insertion charge

The loop credit gives conceptually

```text
loop_cost
<= cheap_child_terms
 + I * (mkOf + residual_groups - p).
```

`residual_groups <= ownGroupsOf`, and `mk_own_full_le` implies

```text
mkOf + ownGroupsOf - p <= |Cr| + |Be|.
```

So the expensive `I` factor is charged only to `Cr/Be`, not `p`.

The `O(k)` scan/expansion part may continue using the old

```text
mkOf <= p + |Cr| + |Be|
```

bound. With constant `k`, the surviving `O(k p)` term is harmless.

For partial calls, retain the current `|S| < |U|/t` charge.

---

## C. Fresh BM.6 pivot insertion cost

Files:
- `formal/lean/Frontier/CHD/BMCost.lean`
- `BMTeleChd.lean`
- `BMTeleLoop.lean` / the initialization simulation
- `RamPiv.lean`
- `DLazy.lean` / `DInsert*` lemmas as needed

### C1. Refine the DCost interface

`DCost` has only a generic evolved-structure `ins`.

Add a separate cost:

```lean
initIns : ℕ -> ℕ
```

meaning insertion into the fresh level structure during BM.6.

Then change:

```lean
initCost DC lv p P =
  DC.new lv + Σ_j |P_j| + p * (2 + DC.initIns lv)
```

Ordinary BM.23/BM.25/BM.28 insertions continue to use `DC.ins`.

Search of the upstream snapshot shows only a small number of explicit
`DCost where` constructors (`chdDC` and the L6 cost wrapper), so this field
addition is mechanically contained.

### C2. Prove `initIns = O(1)` for DLazy

`newC` has exactly one block:

```lean
def newC ... := <..., [<bottom, []>]>
```

and the paper/implementation states `Insert NEVER splits`.

During BM.6:
- every insert starts from the same one-block fresh structure;
- insertion prepends to that block;
- no split occurs;
- the separator-stack search has `#blocks = 1`;
- pivots are distinct because FindPivots groups are disjoint.

Therefore the `bsCost(#blocks)` part is constant for all BM.6 inserts.

Use the existing RAM insert bound from the theorem map:

```text
<= 40 * (c + 1)
c = bsCost(#blocks) + 3
```

and instantiate `#blocks = 1` to get an explicit constant `initIns`.

The exact constant is unimportant asymptotically; use whatever value closes
the current RAM inequality without delicate optimization.

### C3. Why this change is necessary

Even after removing the `+p` from expensive BM.23 re-selection accounting,
the old `initCost` still contributes

```text
p * DC.ins(l) = O(t p).
```

Since full-call pivot mass is `p = O(N/k)` per layer, that recreates

```text
O(N t / k)
```

and forces the old `k = sqrt(t)` balance.

Fresh insertion must therefore be separated from generic insertion for the
exponent to move.

---

## D. Retune parameters only after A--C close

Current:

```text
k = ceil(sqrt(t))
t ~ (N log N / m)^(2/3)
```

After A--C, the target core expression is

```text
O(
  (L+1) N k
  + k^2 (m + N L / t)
  + m t
  + lower-order logarithms
).
```

Set `k = 4`, `t >= 16`.

With `L = Theta(log N / t)`:

```text
T_core =
O(
  N log N / t
  + m t
  + lower-order terms
).
```

Balance at

```text
t = Theta(sqrt(N log N / m))
```

to obtain the candidate

```text
T_core = O(sqrt(m N log N)).
```

For `m = n log^alpha n`:

```text
old exponent:       (2 + alpha) / 3
candidate exponent: (1 + alpha) / 2
```

and at `alpha = 3/4`:

```text
11/12 -> 7/8.
```

## Recommended implementation order

1. Prove A1/A2 as standalone finite-set lemmas.
2. Add A3 without changing the global proof.
3. Prove the loop telescope A4.
4. Prove the own-home group inequality B2.
5. Wire B3 into `CostLe`.
6. Only then change `DCost` / BM.6 pricing in C.
7. Re-run the master algebra with symbolic `k,t`.
8. Retune `k,t`.
9. Finally update the RAM/Lean parameter instantiation.

This order gives early failure points before touching the large RAM spine.
