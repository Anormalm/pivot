# Ownership route: use the existing forest notion, not W' as a new log field

The cleanest formal route now appears to be:

1. keep `CallRec` and `LogInv` unchanged;
2. prove a separate provenance theorem that every recorded `W'` vertex is
   **owned** by its call;
3. define the extra group counter from the existing call forest's ownership
   predicate.

## Existing upstream notion

`Frontier.CostAggregate.CallCounters.Own X v` is already:

```text
v ∈ U_X
and
for every direct child Y of X, v ∉ U_Y.
```

The same predicate can be written directly over `BM.Log.forest hL`.

For any owned vertex, `Ranges.home` is automatically `none`:

- the direct-child membership branch fails;
- the foreign-range branch requires `v ∉ U_X`, which is false.

## Why W' vertices are owned

Upstream already proves the exact local argument inside `BMTrace.callC_log`
when discharging the existing `wr` field for W' relaxation edges:

```lean
have hsW : G.src e ∈ W' := ...
refine ⟨Finset.mem_union_right _ hsW, fun a r' h' => ?_⟩
have h'' := mem_cons_nonempty h' (by simp)
obtain ⟨hU, -⟩ := hll.root a r' h''
intro hsrc
exact ((hW' _).mp hsW).1.2 (hU hsrc)
```

Nothing in this argument depends on the vertex being the source of an edge.
So it generalizes verbatim from `G.src e ∈ W'` to arbitrary `v ∈ W'`.

This is strong evidence that the ownership bridge is bookkeeping rather than
a new graph-theoretic obligation.

## Candidate provenance interface

Add a separate theorem/property:

```text
WPrimeOwn(lg):
  for every record (q,r) in lg,
  for every v in r.W',
    v in r.U
    and v is in no direct child record's U.
```

It can be proved by induction over `BMSSPC`, structurally like
`RecFPLog.bmsspC_recall`.

No new field is needed in:
- `CallRec`;
- `RecFacts`;
- `LogInv`.

## Own-group counter

Once WPrimeOwn is available, define

```text
ownGroupsOf(X)
  = # original pivot groups containing an owned vertex.
```

For a full call, final residual groups meet W', hence

```text
nonemptyCount(final) <= ownGroupsOf(X).
```

At the colour layer, each own group contributes the distinct home colour
`none`.

This gives the desired log-level inequality

```text
mkOf(X) + ownGroupsOf(X)
  <= p_X + |Cr(X)| + |Be(X)|.
```

This route is preferable to changing the record schema.
