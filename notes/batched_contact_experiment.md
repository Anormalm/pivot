# Batched contact experiment

The existing version-cache simulator has a deliberately adversarial family where every later root supplies a strictly better path into the same dormant chain. In that family, eager cache invalidation gives no scan reduction: every improvement rescans the whole chain.

This experiment batches those incoming candidates before reactivating the shared region.

For q roots and a shared chain of h vertices:

    eager sequential propagation: q + q(h-1) = Theta(qh)
    batched pending-min propagation: q + (h-1) = Theta(q+h)

The largest committed case q=h=128 changes 16,384 scanned edges to 255, a 64.25x reduction.

This is a graph-realizable witness that the bad version-cache case is specifically an eager-repair problem rather than an unavoidable need to rescan after every incoming improvement.

It is not yet a general FindPivots theorem. The remaining problem is to show that arbitrary dormant-component contacts can be accumulated safely until a repair point without losing the FPContract frontier/closure guarantees.