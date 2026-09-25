# Stable contact into a dormant failed region

## Safe contact case

Suppose a new local search scans an edge e=(u,z) into a vertex z belonging
to an old dormant failed-val region V.

The old cache is immediately reusable if z's tail-side state is unchanged,
but the more interesting question is whether the NEW search may stop at z.

For the canonical-path case, there is a clean sufficient condition.

Assume:

1. u is complete;
2. e is the canonical successor edge toward z, so
   `ext(dis(u),e) = dis(z)`;
3. z's current label is already at most the candidate from u.

Because labels are sound,

```
dis(z) <= d[z] <= ext(d[u],e) = dis(z).
```

Hence z is complete.

If z belongs to the final val set of a dormant failed region, the generalized
failed-val closure theorem then covers every below-B canonical descendant of
z inside that same region.

Therefore an unchanged/non-improving contact on the canonical path is a valid
**cut point**: the new search does not need to repeat the old region's
outgoing scans to prove frontier coverage.

## Why the runtime test is computable

The implementation does not know whether e is canonical.

It does know whether Relax strictly decreases z:

- if the version of z is unchanged, the old outgoing closure remains valid by
  upstream `Closed.grows`;
- if the version changes, z is dirty and cannot blindly reuse its old closure.

The correctness proof can condition semantically:

- if the incoming root is a complete frontier witness and the relevant
  canonical path first enters V at an unchanged contact z, the argument above
  proves z complete, so the dormant closure cuts the path;
- noncanonical contacts need not certify canonical coverage.

This suggests a safe operational rule:

```
contact dormant V at z
Relax(u,z)

if ver[z] unchanged:
    allow the old closed region to stand
else:
    mark z/component dirty
```

A later proof must still show that dirty contacts are eventually repaired or
absorbed into a successful size-k component.

## Remaining hard case

Strict-decrease contacts are the only source of cache invalidation.

Thus the asymptotic problem can now be stated more sharply:

> Bound the total edge work caused by strict-decrease contacts into dormant
> components.

Stable contacts cost O(1) metadata/heap work and reuse the old closure.

The simulator in `experiments/dormant_findpivots_sim.py` illustrates the
two extremes:

- stable shared tails: large scan savings;
- a strict decrease before every revisit: no savings.

The next theoretical target is to exploit component merging/batching so that
strict-decrease contacts do not force one complete rescan per incoming root.
