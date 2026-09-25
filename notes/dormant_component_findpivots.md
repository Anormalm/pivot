# Dormant-component FindPivots

## Motivation

The candidate N4 tightening is now kernel-checked through the local/global
candidate cost chain, but the remaining BM.6 preload term prevents the
constant-k square-root retuning.

The second asymptotic route keeps BM.6 and instead targets FindPivots:

- choose k = Theta(t), so the unavoidable full-call BM.6 term
  N log N / k becomes N log N / t;
- reduce the current FindPivots coefficient A(k)=Theta(k).

A heap alone is insufficient because the current Search.cost proof also pays
Theta(k) relevant scans per extracted member.

Naive version-tagged scan caching is also insufficient: a strict decrease of
d[u] changes every candidate d[u] + e, so an old scanned prefix may need to
be replayed.

## Stronger design: retain failed searches as components

Current FH.24 discards the structural search object when a search fails:

    H = empty, |K| < k
    W_x := val
    Q.append(x)

The proposed variant keeps the K-tree as a **dormant component** for the rest
of the FindPivots invocation.

Each discovered vertex belongs to exactly one component.

A component stores:

- its discovered tree/forest K;
- the subset of S-roots currently represented by the component;
- current labels and valid/explored seeds;
- a heap of pending propagation work;
- status: active, dormant, or successful.

### Root processing

For a new x in S:

1. if x already belongs to a successful component, skip it;
2. if x already belongs to a dormant component, register x as another root of
   that component rather than restarting a local search;
3. otherwise create a singleton component and run the local search.

### Contact

If an active component reaches a vertex owned by another component:

- union the two disjoint component trees through the contact edge;
- if the combined discovered mass reaches k, freeze it as a successful tree;
- otherwise retain it as one sub-k component and continue/queue whatever label
  propagation is actually required.

This differs from current C-HD only in that **failed** search objects are not
forgotten. Successful/contact trees are already globally retained by fmark.

## Why this is compatible with the abstract BMSSP interface in principle

BMSSP itself only consumes FPContract, which requires:

- labels decrease soundly;
- W plus the output pivot groups form a frontier;
- Q and the pivot groups partition S;
- W lies inside Utilde(B,S).

It does **not** require one independent failed search per q in Q.

Therefore a batched FindPivots implementation may output:

- Q = all S-roots belonging to final dormant components;
- W = the union of the completed/closed regions of those components;
- tree vertices of successful components to MakePivots.

The main new correctness lemma is a multi-root analogue of
Search.failed_complete:

> If a final dormant component is closed, then for every q in its root set,
> whenever q is complete, every canonical descendant of q below B is complete
> and belongs to the component's W-region.

If this can be proved from one shared closure condition, the same failed work
serves multiple Q roots.

## Why union-by-size alone is not yet a proof

A tempting claim is that component merges cost O(log k) per vertex by always
moving the smaller component.

That is true for **ownership metadata**: every time a vertex is on the moved
side, its component size at least doubles, so it moves O(log k) times before
the component reaches size k.

But label propagation is directional.

If an incoming contact decreases a vertex in the larger component, correctness
may require revisiting work in that larger component. Ownership union-by-size
does not by itself bound that repair cost.

So the safe conclusion is:

- union-by-size controls component bookkeeping;
- it does not yet control shortest-path repropagation.

## Better batching idea

Instead of rebuilding immediately after every merge, keep a component dirty.

Accumulate:

- newly merged vertices;
- vertices whose labels strictly decreased because of contacts.

Perform a closure rebuild only when:

1. the dirty/new mass is a constant fraction of the clean component size; or
2. the component must be finalized as failed.

If the component reaches size k first, it can become a successful tree without
paying for a full failed-region closure.

This gives a geometric number of full rebuilds with respect to component
growth. The unresolved issue is the cost of a rebuild itself: a dense sub-k
component may contain Theta(k^2) relevant internal edges.

Therefore the next theorem must charge **distinct edge work**, not just moved
vertices.

## Exact target

A useful replacement for the current HD1 cost would have the shape

    cost
      <= O(log k) * (#component bookkeeping / heap events)
       + O(1)      * (#distinct relevant edge events)
       + deletion charge.

To yield A(k)=polylog(k), those distinct edge events must then admit a global
charge across overlapping roots/components rather than being repaid per root.

This is the main open technical point.

## What has been ruled out

1. Heap-only replacement: extract-min improves, scan term remains Theta(k).
2. Cursor-only reuse: label decreases invalidate old relaxations.
3. "Every failed root is complete": false; upstream failed_complete is
   conditional on a complete root.
4. Pure union-by-size: controls ownership movement, not label-repair direction.

## What remains plausible

A shared component closure is still promising because it changes the unit of
work from

    one local search per root

to

    one evolving closure object per overlapping region.

That is exactly the kind of change needed to remove the repeated-root factor
without contradicting the ordered-pull or dense-local-edge barriers.
