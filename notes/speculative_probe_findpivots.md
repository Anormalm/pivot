# Speculative-probe FindPivots

## Motivation

The current HD1 coefficient contains a Theta(k) scan factor because an extracted tail can inspect up to k edges whose heads are already in the local K set. Those internal/repeated edges are needed for exact local Dijkstra closure, but successful searches do not need that closure.

This suggests splitting FindPivots into:

1. a cheap structural ownership/discovery probe;
2. exact closure repair only for components that remain dormant and must contribute Q/W.

## Speculative probe rule

Maintain a global owner map for the current FindPivots invocation.

For an active component and a scanned edge (u,v):

- keep the existing FH.8 bound break and FH.9 permanent deletion;
- if v is unowned:
  - assign v to the active component;
  - record the first-discovery parent edge;
  - perform at most the first relax needed to obtain a sound label;
  - if valid, put v in the local heap; otherwise it is a leaf;
- if v is already owned by any component, including the current component:
  - treat this as a speculative collision;
  - record/defer the contact candidate in the pending map;
  - union components if the owner is different;
  - stop this probe instead of scanning/relaxing further internal edges.

If the component reaches k owned vertices, freeze a successful structural tree.

## Speculative scan bound

Ignore the globally charged FH.9 deletions.

Every other scanned edge in the speculative phase either:

- creates a previously unowned vertex; or
- is the one collision edge terminating that probe; or
- is the one range-stop edge.

Hence the scan count has the target shape

    O(#first discoveries + #probes + #range stops + #deletions)

instead of

    O(k * #extracted vertices).

A standard binary heap then makes local heap work O(log k) per valid newly-owned vertex.

## Why stopping on same-component edges is allowed only speculatively

Skipping an internal relaxation is not enough to certify a failed Q/W region. The component is therefore marked dirty/dormant, not output as failed.

Before a dormant component contributes to Q/W, it must run an exact repair/closure phase. The checked failed-val/multi-Q frontier lemmas are designed for this final phase.

Successful components are different: BMSSP correctness only needs their S vertices to appear in pivot groups. Their tree object is structural; it does not require every internal relaxation that exact failed closure would need.

## Dense-region effect

The current worst case for a local search is a sub-k dense region: many scanned edges point back into K, creating Theta(k^2) work per root.

Under the speculative collision rule, the first repeated/owned target ends the probe. Once a dense region has been claimed by one component, later roots in that region are already owned and need no independent probe.

This turns the motivating dense-overlap family from repeated quadratic local work into essentially one ownership pass plus one eventual exact repair.

## Remaining proof obligations

1. Show speculative label writes remain sound/monotone and confined.
2. Show contact/ownership union preserves a spanning tree suitable for MakePivots.
3. Prove roots already owned by a dormant component may be attached without a new probe.
4. Define exact repair from the component's roots + pending map.
5. Prove a dormant component is never emitted to Q/W before exact repair.
6. Bound exact repair globally (current target: geometric/event-based O(m log k) style charge).

The speculative phase alone is not an improved SSSP theorem, but it removes the specific HD1 internal-K scan pattern from all searches that become successful before exact repair.