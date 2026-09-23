# Exact re-selection combinatorics

**Status:** elementary combinatorial lemma + exhaustive validation.  
**Lean integration:** not yet compiled.

## 1. One pivot group

Fix one nonempty pivot group `P_j` in a full parent call.

Partition its members by their parent-level home:

- positive/home-child classes: vertices returned by child calls;
- own/final class: vertices returned by the parent itself after the child loop.

Let:

```text
c_j = number of child homes represented in P_j
o_j = 1 if the own/final home is represented, else 0
h_j = c_j + o_j
```

Children are processed once, in order.

BM.23 performs an expensive re-selection only when:

```text
the current pivot is returned by this child
AND
the residual group is nonempty.
```

### Case 1: an own/final member exists

Then the group remains nonempty after every child-home class is removed,
because at least one own member survives the child loop.

At most one re-selection can be caused by each represented child home, hence

```text
g_j <= c_j = h_j - 1.
```

### Case 2: no own/final member exists

Because the parent call is full, every group member must be returned by some
child.

Let the last represented child home be `Y_last`. When that child is
processed, every remaining group member is removed, so the residual group is
empty. BM.23 therefore does **not** re-select after this last home.

Only the preceding child homes can cause re-selection:

```text
g_j <= c_j - 1 = h_j - 1.
```

Thus in all cases,

```text
g_j <= h_j - 1.
```

Equivalently, in natural-number form:

```text
g_j + 1 <= h_j.
```

This statement is independent of the minimum-label pivot rule.

## 2. The relaxed adversarial maximum is exact

If after every re-selection the next pivot may be chosen arbitrarily from the
residual group, the upper bound is achievable.

- With an own/final member, choose the pivot successively from each child-home
  class. The own member keeps the residual group nonempty after the final
  child class.
- Without an own/final member, choose the pivot successively from every child
  class except the last represented one.

Therefore the relaxed model has the exact optimum

```text
max g_j =
  #child homes             if own/final home is present
  #child homes - 1         otherwise
```

or simply

```text
max g_j = #represented homes - 1.
```

C-HD's minimum-label pivot policy can only realize a value no larger than
this adversarial maximum.

## 3. Exhaustive check

Run:

```bash
python experiments/exact_characterization.py
```

Committed run:

```text
max group size:          8
max child-home labels:   4
states checked:          585,978
violations:              0
```

See `results/exact_characterization_summary.json`.

The exhaustive checker computes the adversarial optimum by dynamic
programming over

```text
(processed child index, residual-member mask, current pivot)
```

and compares it to the closed-form expression above.

The experiment is useful as a bug detector for the model; the proof itself
is the case analysis in §1--§2.

## 4. Aggregate form for a full call

Let:

```text
G = total number of actual BM.23 re-selection events
p = number of nonempty original pivot groups
M = total child/group meetings across all groups
O = number of groups containing an own/final-home member
```

Summing `g_j + 1 <= h_j` gives

```text
G + p <= M + O.
```

In C-HD terminology,

```text
M = mkOf(X)
```

and a candidate record-level definition is

```lean
ownGroupsOf k r :=
  (groupsOf k r).countP
    (fun g => decide (g.toFinset ∩ r.W').Nonempty)
```

for a full call, because the paper's R8 decomposition is

```text
U_X = W'_X ⊔ U_{Y_1} ⊔ ... ⊔ U_{Y_f}.
```

So the target loop/counting inequality is

```text
G + p <= mkOf(X) + ownGroupsOf(k, r).
```

## 5. Home-colour inequality

For one group, every child meeting contributes a distinct home `some Y`.
If the group meets `W'`, that contributes the additional distinct colour
`none`.

Hence

```text
childMeetCount(g) + ownIndicator(g)
    <= # distinct home colours in g.
```

Summing over groups and reusing the existing PT-piece proof gives the target

```text
mkOf(X) + ownGroupsOf(k,r)
    <= p + total_bichromatic_piece_edges.
```

The existing `bich_le_crbe` theorem then supplies

```text
total_bichromatic_piece_edges
    <= |Cr(X)| + |Be(X)|.
```

Combining:

```text
G + p
  <= mkOf + ownGroups
  <= p + |Cr| + |Be|
```

and therefore

```text
G <= |Cr| + |Be|.
```

This is the desired removal of the once-per-group exception **for the
expensive actual BM.23 re-selection events**.

## 6. How to obtain `G + p <= M + O` from existing loop machinery

The upstream loop already defines:

- `markedGroups σ Ui`: groups that actually re-select;
- `emptiedGroups σ Ui`: nonempty groups completely consumed by this child;
- `nonemptyCount σ`.

Per iteration:

```text
|markedGroups| + |emptiedGroups|
    <= # original groups meeting Ui.
```

The exact emptying identity is

```text
nonemptyCount(next) + |emptiedGroups|
    = nonemptyCount(now).
```

At loop entry, `FPContract.groups` gives every `P_j` nonempty, so

```text
nonemptyCount(initial) = p.
```

Telescoping gives

```text
total_marked + p
    <= total_meetings + nonemptyCount(final).
```

For a full call, every final nonempty residual group contains a member of
`W'`, so

```text
nonemptyCount(final) <= ownGroupsOf.
```

Therefore

```text
total_marked + p <= mkOf + ownGroupsOf.
```

This route avoids introducing a new per-group event log.
