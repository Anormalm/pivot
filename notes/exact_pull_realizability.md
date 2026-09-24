# Toward a realizability lower bound for exact PullSpec

The ordered-bucket argument in `notes/ordered_pull_barrier.md` is currently
an information-theoretic statement about the abstract D interface.  To turn
it into an architectural obstruction for BMSSP, one should exhibit valid
calls in which:

1. there are p pivot groups with essentially arbitrary distinct pivot labels;
2. all p groups remain relevant;
3. a full execution consumes them through successive exact Pull operations;
4. no unrelated relaxation/delete event reveals their order for free.

## Candidate branch family

Consider p disjoint branches under one call.  For group j, create a connected
PT-sized branch with k frontier vertices and a distinguished minimum pivot
p_j.

Choose the branch offset a_j independently from a set of distinct real
values.  Internal branch increments are fixed and much smaller than the
spacing between offsets, so:

  d[p_j] = a_j

and all other members of P_j lie just above a_j.

The branch topology / MakePivots piece order is independent of the values
a_j.  Thus the permutation of pivot labels can be arbitrary while the
structural output of the partition is unchanged.

The intended recursive behavior is:

- when p_j is included in a pull batch, the expansion step adds the relevant
  low members of P_j;
- its sub-call returns/completes that branch;
- no other branch is affected;
- the group then empties;
- repeat until all branches have been consumed.

If this behavior can be realized by a concrete FindPivots-HD execution, then
the sequence of exact Pull sets identifies the ordered M-sized buckets of the
arbitrary values a_j.

That would yield an information lower bound

  Omega(log(p!/(M!)^(p/M)))
    = Omega(p log(p/M))

comparisons for the exact-pull architecture.

## What still has to be checked

This is not yet a formal lower bound for released C-HD.  The hard part is
realizability through the **concrete FindPivots-HD** rather than an arbitrary
FPContract implementation.

Need to verify:

- [ ] FindPivots-HD can output p disjoint successful PT pieces on this family
      rather than classifying the roots into Q/W.
- [ ] Each produced group stays within one independent branch.
- [ ] Pivot minima can be assigned arbitrary relative order without changing
      the search success/contact pattern.
- [ ] Child calls can be made full and branch-local.
- [ ] Window relaxations do not introduce cross-branch keys that reveal/order
      the a_j values.
- [ ] The call remains inside the claimed C-HD density/degree regime after
      padding/degree reduction.

## Why this matters

If the realizability checklist closes, then simply replacing DLazy with a
different comparison-based data structure cannot remove the BM.6
p log(p/M) term while retaining exact PullSpec.

A faster algorithm would have to weaken the pull semantics, expose extra
certificate structure, or change how the frontier groups are represented.

If the checklist fails for a structural reason, that failure itself may
identify exploitable structure in the concrete C-HD pivots.
