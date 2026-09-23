# Credit-carrying CostLog design

## Goal

Preserve the full-call `I*p` credit from the refined loop theorem until global home/Cr/Be information is available in `CostLe`, without changing `CallRec` or `LogInv`.

Let `I` be the generic evolved-structure insertion bound and let `I0=O(1)` be the fresh BM.6 insertion bound.

## Refined record inequality

For a recursive record `r`, target:

    r.cost + [full(r)] * I * r.p
      <= budCredit(r, childSum)
         + [full(r)] * I * ownGroupsOf(r).

`budCredit` differs from the current `budOf` in two places:

1. BM.6 initialization uses `I0` instead of `I`: `p * (2 + I0)`.
2. The child charge still contains the current meeting coefficient `(2g+1+I)` because the I-credit loop telescope turns actual marked-event insertion work into `I * meetings`, while carrying `I * nonempty_final` to the right.

For partial calls, the indicator is zero and the existing `t|S|` route is retained.

## Why this transports through CostLog cleanly

The existing `RecCost.shift`, `loopC_reccost`, and `childSumAt` machinery only transports a pointwise inequality attached to each record. It does not depend on the left side being exactly `r.cost`.

So define a sibling predicate conceptually:

    RecCostCredit(lg):
      for every recursive record r,
      r.cost + fullCredit(r)
        <= bud(r, childSum) + ownCredit(r).

with

    fullCredit(r) = if r.B'=r.B then I*r.p else 0
    ownCredit(r)  = if r.B'=r.B then I*ownGroupsOf(k,r) else 0.

The shift/append proofs are structurally identical to `RecCost.shift` because both credits depend only on the record.

## Cancellation in CostLe

For a full record, after rewriting the child sum:

    cost + I p
      <= cheap
       + (2g+1) mkOf
       + I mkOf
       + I ownGroups
       + other terms.

The refined home-colour bound gives:

    mkOf + ownGroups <= p + |Cr| + |Be|.

Hence:

    I mkOf + I ownGroups <= I p + I(|Cr|+|Be|).

Substitution yields:

    cost + I p
      <= cheap + I p + I(|Cr|+|Be|) + other.

Natural-number arithmetic can cancel `I p`, leaving:

    cost <= cheap + I(|Cr|+|Be|) + other.

The surviving `(2g+1) mkOf` is cheap. The old `mkOf <= p+Cr+Be` bound is sufficient there; with constant `k`, its `O(kp)` contribution is absorbed by the existing full-pivot mass bound.

## Why this is preferable to adding an actual-mark counter

Adding the total number of actual BM.23 marked events to `CallRec` would require changing record constructors, trace theorems, and counter projections.

The credit design reuses existing `mkOf`, `W'`, groups, and `Cr/Be` data and adds only a parallel cost predicate/budget theorem.

## Remaining formal pieces

- prove `loopC_cost_I_credit`;
- prove final `nonemptyCount <= ownGroupsOf` for full calls;
- add `initIns` or equivalent fresh initialization pricing;
- define/prove `RecCostCredit` transport;
- replace the full-call branch of `tracedCounters_cost_le` with the cancellation above;
- keep the partial-call branch essentially unchanged.