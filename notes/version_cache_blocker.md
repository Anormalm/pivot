# Version-aware scan reuse: blocker audit

## Why version tags are sound but insufficient

C-HD walk labels carry a tail version. A strict label decrease writes the new
label and increments `ver[u]`; equality re-confirmations do not increment it.
So a cached outgoing scan for tail `u` can be tagged by `ver[u]` and is
logically reusable while that version remains unchanged.

However, a version change is not a cheap "continue from the old cursor" event.

For fixed `u`, the candidate on edge `e=(u,v)` is built from the entire
current label `d[u]`. If `d[u]` strictly decreases then:

- every old candidate `d[u] + e` may strictly decrease;
- an edge already scanned under the old version may now improve `d[v]`;
- therefore the old prefix cannot in general be skipped.

The prefix fact only says edges below a bound form a prefix for a *fixed*
tail label. It does not make old relaxations final after the tail label
changes.

## Worst-case accounting shape

Suppose a tail `u` participates in `q` overlapping local searches and
receives a strict improvement before each later extraction. Suppose each
extraction has `r` relevant outgoing edges whose heads are already in the
local K-set.

A version-tagged cache then permits:

    work(u) = Theta(q r)

because every new version can require replaying the old relevant prefix.

With `q = Theta(k)` and `r = Theta(k)`, this is still Theta(k^2).

This is exactly the scale hidden by the current Search.cost bound

    out(u).countP(dst in K) <= |K|.

Therefore "memoize the scan cursor by ver[u]" is not by itself an
asymptotic improvement.

## When reuse *is* safe

There are useful stable subclasses:

1. `ver[u]` is unchanged between extractions;
2. `u` is known complete, so its label cannot later decrease;
3. all previously scanned heads are already provably final relative to u.

The first case gives an engineering win but no worst-case theorem.
The second is theoretically attractive, but the current FindPivots contract
does not make every failed-search root or every failed-region vertex complete.
`Search.failed_complete` is conditional on a complete root.

## Consequence

The next asymptotic target should be stronger than a per-root cache:

> share the search state across roots so that a decrease of u is processed once
> globally, rather than invalidating q independent local searches.

That suggests a batched / multi-source FindPivots formulation.

The desired cost is in terms of *events*:

- first discovery of a vertex;
- strict label decrease;
- permanent edge deletion;
- tree contact / ownership merge;

rather than "k work per root-local member".

A useful theorem target would replace the current

    fpA(k) * (#tree vertices + k |Q|)

with something closer to

    polylog(k) * (#distinct search vertices + #strict decreases)
      + O(#distinct scanned/deleted edges).

Whether strict decreases themselves admit a global O(m) or O(tree-size)
charge is the next question.
