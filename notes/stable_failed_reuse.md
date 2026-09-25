# Stable failed-search reuse experiment

## Purpose

The second-route target needs to reduce FindPivots' O(k) local scan factor.
Before designing a general cache, this experiment asks whether duplicate work
can actually be large on a valid state where cache stability is not an issue.

## Construction

Take a complete directed component on h vertices with exact/canonical labels.
Put q roots from this component in the FindPivots frontier and choose k>h.

Every local search fails because it can discover fewer than k vertices.
Failed searches are not globally fmarked, so later roots can explore the same
component again.

Because all tail labels are already complete in this toy subclass, scan reuse
is semantically safe: the same outgoing edge candidate will not change later.

## Result

For a complete directed h-vertex component:

    internal edges = h(h-1)
    baseline scans = q h(h-1)
    ideal stable-cache scans = h(h-1).

So the duplicate factor is exactly q.

In the largest committed case:

    h = 64
    q = 64
    k = 65
    baseline scans = 258048
    unique scans = 4032
    reduction factor = 64x
    duplicate fraction = 98.4375%.

## What this establishes

It demonstrates that the repeated failed-search scan term is not merely an
artifact of loose analysis: the current control flow can repeat an entire
small region once per failed root.

It also shows that a shared-search/cache mechanism has genuine upside on a
legitimate stable subclass.

## What it does not establish

It does not justify a general persistent cursor. In ordinary executions, a
failed-search vertex may not be complete and its label can decrease before
the next root reaches it.

The next target is therefore a version-aware experiment/model: count how much
duplicate scanning remains when cache entries are invalidated on tail-label
changes.