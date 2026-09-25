# Dormant failed-val reuse: exact reusable contract

## 1. What a failed search leaves behind

For a failed local search, upstream `Search.inv` gives:

- `H = empty`;
- `|K| < k`;
- every vertex in final `val` lies in `done` because
  `val subset done union H`;
- every outgoing scanned edge of every `done` vertex satisfies
  `Closed`.

Thus final `val` is not just a bag of labels.  It is a closed explored
region under the final search state.

## 2. Closure is reusable under an unchanged tail label

Upstream already proves:

```
Closed.grows :
  Closed c sigma u e ->
  Grows sigma sigma' ->
  sigma'.d u = sigma.d u ->
  Closed c sigma' u e
```

This is exactly the source-level theorem needed by a version-tagged dormant
cache.

A cached outgoing scan of u is therefore reusable while the version/label of
u is unchanged.  Decreases of head labels do not invalidate the closure; they
only make the inequality

```
d[head] <= candidate(u,e)
```

easier to satisfy.

Only a change of the **tail** label invalidates the old scan certificate.

## 3. The initial-root restriction in failed_complete is unnecessary

Upstream `Search.failed_complete` is stated for a complete vertex x that was
already in the initial search `val` (normally the root).

The actual path induction after the search has failed uses only:

- x is in the **final** val set;
- x is complete under the final labels;
- final H is empty;
- final done-edge closure;
- Dinv for deleted edges.

The candidate theorem

```
failed_state_complete_from_val_candidate
```

extracts this stronger final-state statement.

Consequently, for every complete x in final val:

```
OnPath x v
and dis(v) < B
  =>
v in final val
and v is complete.
```

## 4. Why this matters for batching Q roots

Suppose a later frontier root x belongs to an already-retained dormant
region's final val.

We can add x to that region's Q-root set **without running another local
search**.

The implementation does not need to determine whether x is complete.

The BMSSP frontier proof only needs the Q-root closure implication when x is
in fact a complete incoming frontier witness.  In that case the generalized
failed-val theorem supplies exactly the required closure.

The candidate corollary

```
failed_val_qroots_candidate
```

states this for an arbitrary finite set of Q roots contained in one final
val region.

The candidate

```
frontier_from_failed_val_qroots_candidate
```

then plugs the shared region directly into the BMSSP-facing frontier
contract.

## 5. Minimal dormant-region cache

A safe cache record can therefore contain:

```
V       := final val vertices
version := tail-label version saved for each u in V
closed  := outgoing closure certificates from the failed state
roots   := all S roots assigned to this region
```

Root handling:

```
if x belongs to V:
    roots.add(x)
    Q.add(x)
    do not rerun a local search
else:
    start/continue ordinary search
```

Vertex reuse:

```
if u belongs to cached V and ver[u] unchanged:
    reuse old Closed certificates
else:
    mark u dirty / rescan when required
```

This modification is correctness-motivated by existing or candidate Lean
lemmas; it is not merely an empirical cache heuristic.

## 6. What this does NOT solve yet

Worst-case asymptotics are still open.

A later root can lie outside all prior V regions while its search repeatedly
enters their vertices.  Also, a strict decrease of a cached tail label can
invalidate its old closure.

So the remaining cost quantity is roughly:

```
sum over u of
  (# distinct label versions of u that are actually reactivated)
  * (# relevant outgoing edges processed for that version).
```

A version tag makes this quantity explicit but does not bound it.

## 7. Two stronger routes now under investigation

### A. Complete-core retirement

If u becomes complete, its label is permanently stable.  After one relaxation
of an outgoing edge e, that edge can never improve again under any later sound
monotone labels.

Candidate lemmas:

- `complete_stable_candidate`
- `complete_closed_region_stable_candidate`
- `complete_tail_edge_retired_candidate`

This suggests growing a monotone permanent complete core inside dormant
components.

### B. Global-min settling

Upstream `IsFrontier.complete_of_min` proves that a global minimum of the
current frontier is complete.  `IsFrontier.step` then preserves the frontier
after settling it.

The candidate `global_min_frontier_step_candidate` packages that route.

The potential payoff is strong: outgoing edges scanned from globally settled
complete vertices can be retired permanently.

The concern is comparison cost: extracting too many exact global minima may
simply reintroduce a sorting barrier.  A useful algorithm must arrange that
global ordering is paid per component/batch rather than once per original
frontier root.

## 8. Current most concrete safe improvement

Even before the stronger cost theorem, dormant final-val reuse gives an
instance-sensitive improvement:

```
current:
  one failed search per Q root

dormant-val variant:
  one failed search per Q root not already covered by a retained final val
```

The worst-case number can still equal |Q|, so this is not yet the desired
asymptotic theorem.  But it is a correct, testable intermediate algorithm and
provides the state needed for stronger shared-repair accounting.
