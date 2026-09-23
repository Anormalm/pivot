# Tonight proof checkpoint

Date: 2026-09-23

## What is now concrete

The upstream `LoopCost.lean` already contains all objects needed for the
first cancellation step:

- `markedGroups σ Ui`
- `emptiedGroups σ Ui`
- `nonemptyCount σ`
- `childCharge`
- the existing one-sided `card_nonempty_next`
- `loopC_cost`

The branch now contains an uncompiled source-aligned Lean draft for the three
finite-set lemmas that strengthen this bookkeeping.

## Immediate target

The next real theorem should have the schematic form

```text
loop cost
+ I * nonemptyCount(initial)
<=
ordinary child/edge charges
+ I * nonemptyCount(final)
+ I * total meeting groups
```

where `I = DC.ins(l+1)`.

For a full call:

```text
nonemptyCount(initial) = p
nonemptyCount(final) <= ownGroups
```

and the home-colour argument should give

```text
mkOf + ownGroups <= p + |Cr| + |Be|.
```

Substituting and cancelling `I p` leaves the expensive insertion charge

```text
I (|Cr| + |Be|)
```

with no `I p` term.

## Why the email can be useful tonight even before full Lean closure

We can now send the authors something falsifiable and source-specific:

1. exact upstream definitions where the overcharge occurs;
2. an elementary one-group lemma;
3. an aggregate loop-telescope identity;
4. 585,978 exhaustive exact-characterization states;
5. 1,668,504 tree/colour exhaustive cases;
6. 50,000 random tree/group trials;
7. 200,000 direct loop-telescope trials;
8. a concrete candidate Lean patch location;
9. a clearly labelled conditional complexity consequence.

The email should **not** state that `O(sqrt(m n log n))` has been proved.
The right wording is that we found a candidate tightening that appears to
remove the `t p_X` charge, and we would like the authors' view on whether a
hidden invariant blocks the cancellation.

## Best question for the authors

> Is there a reason the full-call BM.23 analysis must count one exceptional
> expensive re-selection per pivot group, rather than charging only actual
> marked events and using the final residual group as the missing `none`
> home?

That is much easier for them to evaluate than a broad claim that the final
exponent is wrong.
