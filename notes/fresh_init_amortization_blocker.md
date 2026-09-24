# BM.6 fresh initialization: raw cost vs amortized potential

**Status:** genuine blocker for the square-root retuning with the current DLazy potential.

## Correction to the earlier audit

It is true that BM.6 inserts all pivots into a fresh one-block DLazy structure,
and `Insert` does not split. Therefore the **raw operation cost** of the
initial insertion list is O(p).

That is not enough for the existing end-to-end cost proof.

`BMTeleLoop.callD_tele` uses the amortized theorem `insMany_tele`, which
charges

```
raw insertion cost + potential_after - potential_before.
```

The current DLazy potential intentionally stores work that will later pay for
lazy splitting during Pull. A large unsplit initial block therefore creates
substantial potential even though the insertions themselves are cheap.

## Exact upstream potential

For one live, non-stale block with p entries and block parameter M:

```
bw(M,p) =
  3
  + 420 * max(0, p-M)
  + 210 * Ssum(M,p)

epot =
  floor(12p/M)

Ssum(M,p) =
  sum_{i=1}^p log2_floor(floor(i/M)).
```

Thus the fresh structure has

```
potM =
  3
  + 420 * max(0,p-M)
  + 210 * Ssum(M,p)
  + floor(12p/M).
```

## Why this can be Theta(t p)

Take `p/M = 2^t`. For a constant fraction of the final entries,
`floor(i/M)` is at least `2^(t-1)`, so their `ell` value is at least
`t-1`. Hence

```
Ssum(M,p) = Omega(p t),
```

and therefore the potential created by initialization is also

```
Omega(p t).
```

The committed numerical audit in
`experiments/fresh_init_potential.py` reproduces the exact definitions.
With `M=1024` and `p/M=2^16`, the potential increase is about

```
3360.01 per pivot ~= 210 * 16 per pivot.
```

## Consequence

The current DLazy amortized proof cannot simply replace BM.6's O(t) insertion
charge by O(1). The `t*p` scale reappears as deferred splitting potential.

Therefore:

- the N4 tightening `g_j <= c_j` remains valid and useful;
- raw BM.6 execution is indeed linear in p;
- but the proposed `k=4`, square-root parameter retuning is **not justified
  for the current DLazy structure/potential**.

A genuine exponent improvement now needs one of:

1. a different global potential argument that shows this preload potential is
   already paid elsewhere and can be cancelled without double counting;
2. a bulk-initialization / priority structure that creates the required
   ordering state with asymptotically less deferred work; or
3. a second algorithmic improvement that permits larger k, so the unavoidable
   `t*p = O(N t/k)` term becomes lower-order.

This is the current main research blocker.
