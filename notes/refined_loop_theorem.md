# Refined loop-cost theorem skeleton

**Status:** algebra/source alignment checked; Lean proof not compiled.

## Desired theorem shape

The existing upstream theorem is

```text
c + g * nonempty(final)
<= 1 + g * nonempty(initial)
   + childSum(meeting charge)
   + (1+I)|J|.
```

For the expensive BM.23 insertion term, the useful additional inequality is

```text
c + I * nonempty(initial)
<= 1
   + childSum(refined charge)
   + (1+I)|J|
   + I * nonempty(final).
```

The coefficient `I` here is the generic evolved-structure insertion bound
`DC.ins(l+1)`.

## Step case

For one child let

```text
M = |markedGroups sigma Ui|
E = |emptiedGroups sigma Ui|
R = |{j : P0_j intersects Ui}|.
```

The candidate finite-set lemmas give

```text
M + E <= R
nonempty(now) = nonempty(next) + E.
```

The group-dependent iteration work is at most

```text
g(M+E) + (g+1+I)M.
```

After adding the insertion potential:

```text
g(M+E) + (g+1+I)M + I*nonempty(now)
=
g(M+E) + (g+1+I)M + IE + I*nonempty(next)
<=
(2g+1+I)R + I*nonempty(next).
```

So the induction should be structurally almost identical to upstream
`loopC_cost`; the change is the orientation and weight of the potential.

## Important split in the eventual call bound

We should **not** replace the current loop theorem wholesale.

There are two conceptually different costs:

1. cheap group expansion/scanning, coefficient `O(g)=O(k)`;
2. expensive re-selected-pivot insertion, coefficient `I=O(t)`.

The current child charge

```text
(2g + 1 + I) * meetings
```

mixes them.

For the final master analysis, retain a safe `O(g) * (p+Cr+Be)` charge for
cheap meeting work, but use the refined emptying/home cancellation only for
the `I * marked` part.

A clean implementation may therefore introduce a split child charge:

```text
cheapChildCharge  ~ (2g+1) * meeting
insertChildCharge ~ I * meeting
```

and carry the `I * nonempty` potential only through the second component.

This is the most important formal-design point found in the source audit so
far.

## Entry

From `FPContract.groups` every original group is nonempty, hence

```text
nonemptyCount(initState) = p.
```

A candidate Lean theorem for this is in
`drafts/IterCostRefinedCandidate.lean`.

## Full-call exit

The remaining semantic lemma is

```text
nonemptyCount(final state) <= ownGroupsOf,
```

where `ownGroupsOf` counts original groups meeting parent `W'`.

For a full call:
- every original group lies in `S`;
- `S subset U_parent`;
- final residual group members are outside accumulated child `U`;
- the call result decomposes as accumulated child `U union W'`.

Thus every final nonempty residual group must meet `W'`.

## Colour closure

Then prove

```text
mkOf + ownGroupsOf <= p + |Cr| + |Be|.
```

The existing `groups_colors_le` and `bich_le_crbe` should remain unchanged.

Combining gives

```text
loopCost + I p
<= cheap + I(mkOf + ownGroupsOf)
<= cheap + I(p + |Cr| + |Be|)
```

and cancellability of `I p` yields

```text
loopCost <= cheap + I(|Cr| + |Be|).
```

No natural-number subtraction is required.


## Algebraic simplification: no split child-charge interface is required

A closer look at the call-level algebra shows that the existing child-charge
coefficient can remain

```text
C2 = 2g + 1 + I.
```

Let

```text
X = |Cr| + |Be|.
```

After the refined loop telescope and the final-residual bound, the relevant
full-call term has the shape

```text
C2 * mk + I * own.
```

Rewrite it exactly as

```text
C2*mk + I*own
  = (2g+1)*mk + I*(mk+own).
```

Now use two bounds:

```text
mk       <= p + X        -- already available upstream
mk + own <= p + X        -- new refined home-colour lemma
```

to get

```text
C2*mk + I*own
  <= (2g+1)(p+X) + I(p+X)
  = C2(p+X).
```

The refined loop theorem has `I*p` on its left at call entry:

```text
loopCost + I*p
  <= cheap + C2*mk + I*own
  <= cheap + C2*p + C2*X.
```

Since

```text
C2*p = (2g+1)*p + I*p,
```

cancelling the common `I*p` yields

```text
loopCost
  <= cheap
   + (2g+1)*p
   + (2g+1+I)*X.
```

So:

- the per-group term keeps only the cheap `O(g)=O(k)` coefficient;
- the expensive `I=O(t)` coefficient is attached only to `Cr/Be`;
- **no new split field in `childCharge` is necessary**.

This materially reduces the proposed Lean patch: the main interface change
still needed is the separate BM.6 fresh-insertion pricing, not a redesign of
the loop child-charge record.
