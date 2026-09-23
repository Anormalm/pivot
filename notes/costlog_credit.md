# Preserving the I*p credit through CostLog

## Why this is the main formal-engineering issue

The strengthened loop telescope naturally gives, for a call with p initially nonempty pivot groups,

    loopCost + I*p
      <= ordinary + (2g+1)*mkOf + I*mkOf + I*finalNonempty.

For a full call, finalNonempty is bounded by the own/final-home group count, and the refined colour lemma gives

    mkOf + ownGroups <= p + |Cr| + |Be|.

Therefore

    loopCost + I*p
      <= ordinary + (2g+1)*mkOf + I*p + I(|Cr|+|Be|),

so the I*p terms cancel.

Algorithmically this is clean. The current Lean logging architecture makes it less direct.

## Where upstream loses the credit

`CostLog.RecCost` stores only a scalar inequality

    r.cost <= bud r (childSum ...).

`budOf` is nonnegative and currently contains an unconditional `p*(2+I)` initialization charge plus the loop child sum whose meeting coefficient also includes I.

If the strengthened loop theorem is immediately weakened back to an ordinary upper bound on `r.cost`, the useful `+I*p` term on the left disappears before `CostLe` sees the global `Cr/Be` counters. Then the old `I*p` term reappears.

## Patch options

### Option A: credit-carrying RecCost

Introduce a strengthened record-cost relation for recursive calls, schematically:

    r.cost + credit(r) <= budCredit r childStats.

For full calls use `credit(r)=I*r.p`; for partial calls use zero and retain the existing `I*|S|` charge.

`RecCost.shift` and `loopC_reccost` are structural transport lemmas, so carrying an extra record-local left-hand credit should be mechanical.

At `CostLe`, combine the full-call credit inequality with

    mkOf + ownGroups <= p + |Cr| + |Be|

and cancel `I*p` before converting to `CostAggregate.Valid.cost_le`.

### Option B: record-local truncated subtraction

Keep ordinary `RecCost`, but define a full-call budget with

    I * (mkOf + ownGroups) - I*p

represented using natural subtraction.

This keeps the credit inside a nonnegative RHS. It avoids changing the shape of RecCost but makes arithmetic and child-sum decomposition less transparent.

### Option C: preserve two child counters

Split child aggregation into:

- cheap child/group meeting work, coefficient O(k);
- expensive actual BM.23 marking work, coefficient I=O(t).

This most closely reflects the algorithm, but requires a wider rewrite of `chgOf`, `childSumAt`, and the record budget interface.

## Recommended route

Option A is the cleanest formalization.

It mirrors the mathematical proof directly, keeps the existing child-sum machinery largely intact, and postpones cancellation until `CostLe`, where the full call forest, home colouring, `Cr`, and `Be` are already available.

## Consequence for project status

This is a formal proof-architecture task, not a newly discovered asymptotic term. Nothing here invalidates the candidate `O(sqrt(m n log n))` accounting, but it means the final Lean patch is more than three local lemmas.