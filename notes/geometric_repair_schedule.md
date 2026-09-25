# Geometric repair schedule for dormant components

## Goal

Turn strict decreases of cached tail labels into polylogarithmic replay rather than one immediate rescan per decrease.

The operational rule is simple: strict decreases mark a component dirty, but do not immediately repair its closure. A component is rebuilt only after enough structural growth has accumulated.

## State

For each dormant/active component C keep:

    size(C)        current owned discovered vertices
    base(C)        size at the most recent full closure rebuild
    dirty(C)       tails whose labels changed since that rebuild
    roots(C)       S roots assigned to C
    closed(C,u,e)  reusable edge certificates for clean tails

with base(C) <= size(C) < k.

## Repair trigger

A full repair occurs only when

    size(C) >= 2 * base(C)

or when FindPivots needs to finalize C as a failed component.

After repair:

    base(C) := size(C)
    dirty(C) := empty

If repair/growth reaches size >= k, C becomes a successful tree and no failed closure is needed.

## Geometric accounting

If all outgoing work of a tail u is replayed only during full repairs, then between two successive replays the component base size doubles. Before reaching k there are O(log k) such epochs, plus at most one final failed repair.

Thus each tail's adjacency work is replayed O(log k) times. If ownership is disjoint, charging edges to their tails gives the ideal invocation-level target O(E_rel log k). With a binary local heap, requeueing vertices at rebuilds gives O(V_rel log^2 k) heap work.

## Why label decreases alone do not trigger repair

A component may receive many strict improvements while its size is unchanged. Immediate repair would allow (#decreases * outgoing_degree) work and recreates the version-cache blocker. The geometric policy intentionally lets those improvements accumulate and propagates only the final label at the next growth epoch.

Roots assigned to a dirty component are pending; they are not discharged into Q until final closure. FPContract is required only at FindPivots return.

## Merge rule

When components A and B contact, union ownership. Use small-to-large for metadata, but keep the larger component's base until the combined size reaches the doubling threshold.

Example:

    base = 32, size = 32
    +1 +1 ... +31  -> no rebuild
    size = 64       -> one rebuild

rather than 32 separate repairs.

## Finalization

At the end of Phase 1, every remaining dirty component gets one final repair.

If repair exhausts below k, its final heap is empty and done-edge closure is restored. Assigned roots lying in final val may be placed in Q, and the candidate multi-Q failed-val theorem supplies shared canonical closure.

If repair reaches k, emit/freeze a successful tree/component instead.

## Unresolved correctness issue

A full repair can contact another component. That merge may introduce newly lowered labels into vertices processed earlier in the same repair.

Possible semantics:

1. allow label-correcting reopenings but prove they remain in the same geometric epoch;
2. abort on cross-component merge and restart only after a size doubling;
3. repair components in a globally compatible source order;
4. run repair multi-source over all roots/dirty seeds known at epoch start and defer new contacts to the next epoch.

Options 2 and 4 currently look easiest to amortize.

## Conditional cost target

    FindPivots scan work = O(E_rel log k)
    FindPivots heap work = O(V_rel log^2 k)
    component metadata   = O(V_rel log k)

The next global proof must bound E_rel and V_rel across calls without introducing an extra recursion-depth factor that dominates the second-route bound.