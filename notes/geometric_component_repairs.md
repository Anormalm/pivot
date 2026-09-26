# Batched finalization route: geometric repairs + disjoint ownership

## Core idea

The dormant-component design becomes more promising if closure is not maintained eagerly after every component contact.

Maintain permanent vertex ownership during one FindPivots invocation:

- an unowned discovered vertex is assigned to the active component;
- discovering an already-owned vertex is a component contact;
- components union structurally on contact;
- a vertex is never independently owned by two components.

This eliminates duplicate K-membership across active/dormant components.

## Deferred closure repair

A contact or strict label improvement can invalidate old local closure. Do not immediately rescan the whole component.

For a component keep baseSize (size at last full repair), current size, and a dirty set/heap.

Run a full closure repair only when:

    size >= 2 * baseSize

or once at finalization if the component is still sub-k. After a full repair set baseSize := size.

Therefore a component that always stays below k has only O(log k) full repair epochs. The existing RepairChain candidate formalizes:

    2^r * initialSize <= finalSize < k.

## Why this may solve the scan term

A full repair may rescan every relevant outgoing edge of every vertex currently owned by the component.

For a fixed vertex u, once u enters a component it remains in that component through unions. Hence each outgoing edge of u is scanned at most once per full-repair epoch after u arrives.

A coarse bound is:

    scans(component) <= (#repair epochs + 1) * outEdges(final vertex set).

If final component vertex sets are pairwise disjoint, their outgoing edge sets are disjoint by tail, so:

    sum_components outEdges(component) <= m.

Thus geometric repair gives the target global envelope O(m log k) for full-repair edge scans.

With k = Theta(t), log k = O(log log n), which is exactly the scale needed by the second route.

## Initial / incremental work

The full-repair argument is only part of the cost. We also need to charge incremental work that discovers new vertices between repairs.

Permanent ownership gives natural charges:

- first discovery of a vertex: once per invocation;
- first scan of an edge from a newly settled vertex: once before that vertex enters a repaired core;
- component ownership changes: O(log k) per vertex under small-to-large union.

The intended total is O((#owned vertices + m) log k) plus heap bookkeeping.

## Final failed components

A final failed component needs only one shared closure object for all of its Q roots.

The candidate theorem frontier_from_failed_val_qroots_candidate already shows that if all those roots lie in one final failed val region, the same region discharges every Q-root frontier obligation. Runtime does not need to know which Q roots are complete.

This is what makes one final repair per component sufficient in principle.

## Successful components

If a repair/growth phase reaches k owned vertices, the component can stop being a failed-region candidate and become a successful tree object for MakePivots.

The structural tree construction still needs a precise rule ensuring a parent edge for every non-root owned vertex, contact unions preserve a spanning tree, and successful trees remain pairwise vertex-disjoint.

## Remaining hard correctness issue

Deferred repair means labels inside a dirty component may be stale relative to paths entering through newly merged pieces.

A safe protocol is:

- dirty components are never output as failed;
- before failed finalization, run closure to exhaustion;
- successful output depends on discovered mass and structural ownership, not completeness of every tree vertex.

## Cost theorem target

Target an invocation-level theorem:

    FindPivotsBatchedCost
      <= O(log k) * (
           distinct owned vertices
         + distinct relevant edges
         + component merge events)
       + permanent deletion charge.

The exact global scope of the distinct-edge charge is the next point to prove.