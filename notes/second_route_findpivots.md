# Second asymptotic route: keep BM.6, make FindPivots cheaper

## Why this route matters

The N4 re-selection tightening is kernel-checked at the candidate level, but BM.6 still carries a genuine Theta(t p) amortized preload term under the current DLazy potential / exact ordered-pull interface.

So the original constant-k route to O(sqrt(m N log N)) is blocked.

There is another route that does not require eliminating BM.6.

## Start from the current master structure

Ignoring fixed constants and lower-order terms, C-HD's core accounting has the shape

    L N k
  + L N t/k
  + k^2 (m + N L/t)
  + m t.

Interpretation:
- L N k: FindPivots local-search work on successful/contact trees;
- L N t/k: per-pivot work such as BM.6, using p = O(N/k) per full layer;
- k^2(...): failed-search / local-search work;
- m t: evolved D-structure / global edge terms.

The N4 patch removes one expensive t*p source, but BM.6 leaves the L N t/k term intact.

With L = Theta(log N / t), that term is N log N / k.

## Key observation: choose k = Theta(t), not constant

The current side condition is 3k <= t, so asymptotically take k = Theta(t) (for example floor(t/3)).

Then the unavoidable BM.6 term becomes

    L N t/k = Theta(L N) = Theta(N log N / t).

That is exactly compatible with the square-root balance.

The problem is that current FindPivots becomes too expensive at k = Theta(t).

## Exact FindPivots bottleneck

Upstream proves

    fpC cost
      <= deleted-edge charge
       + fpA(k) * (#tree vertices + k |Q|)
       + O(|S|),

with fpA(k) = O(k) for the current local search.

The O(k) is not only the unsorted-array ExtractMin. The search proof also allows O(k) relevant outgoing scans per extracted vertex.

## Sufficient improvement

Suppose a new FindPivots implementation or amortization proves the same contract but replaces fpA(k)=O(k) by A(k).

With k = Theta(t), the relevant terms become

    A(t) * (N log N / t + m t)
    + N log N / t
    + m t.

If A(k)=O(1), this gives O(N log N / t + m t), hence after balancing t = Theta(sqrt(N log N / m)):

    O(sqrt(m N log N)).

If A(k)=O(log k), this gives

    O((N log N / t + m t) log t)

and therefore

    O(sqrt(m N log N) log t).

In the Gate-C regime log t = O(log log n). At m = n log^(3/4) n this becomes

    O(n log^(7/8) n log log n),

still asymptotically below C-HD's n log^(11/12) n.

## Why a heap alone is insufficient

The exact upstream formula is

    fpA(k,hins,hext)
      = scanC + hins
        + (scanC+hins)(1+k)
        + hext + O(1).

Even if hext becomes O(log k), the scan term remains O(k).

The real target is therefore to amortize or share repeated edge scans of overlapping local searches while using a standard comparison heap for ExtractMin.

## Why the naive failed-region cache is not yet sound

Failed regions are tempting because they are not globally marked and can be revisited by later roots.

However, the upstream proof does not say every failed root is complete. Search.failed_complete is conditional on a complete root.

Therefore labels of vertices from an arbitrary failed search may still decrease later, and a persistent edge cursor based only on the previous search is not automatically valid.

A correct reuse mechanism must either:
1. attach cache validity to label versions;
2. prove stronger completeness/stability for the reused subset;
3. merge overlapping failed searches into a shared multi-source search state;
4. or change FindPivots so failed work itself becomes a globally owned object.

## Next experiment

Instrument repeated failed-search extraction and record:
- how many times the same vertex is extracted across roots;
- how many times its label version changes between extractions;
- how many outgoing edges are rescanned with an unchanged tail label;
- what fraction of current local-search work is exact duplicate work.

If unchanged-version rescans dominate, versioned scan reuse is promising. If version changes dominate, the route likely needs a genuinely shared multi-source search.

## Current target hierarchy

1. Proved candidate improvement: N4, g_j <= c_j.
2. Blocked route: constant k + cheap BM.6 preload.
3. New route: k = Theta(t) + cheaper FindPivots.
4. Conditional outcomes:
   - A(k)=O(log k): O(sqrt(m N log N) log log n) in Gate-C;
   - A(k)=O(1): O(sqrt(m N log N)).