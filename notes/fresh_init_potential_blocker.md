# Fresh BM.6 potential blocker

Date: 2026-09-24

## What remains true

The raw BM.6 insertion operation into the freshly-created one-block DLazy
structure is cheap:

- `newC` starts with one block;
- `Insert` does not split;
- the concrete list insertion cost on that one-block structure is O(1) per
  pivot.

That source-level observation is still correct.

## What the previous accounting missed

C-HD does not analyze DLazy using raw operation cost alone.  The Layer-A
telescope pays

```text
actual cost + potential after <= potential before + amortized charge.
```

For insertion, upstream defines

```text
insCharge(D)
  = bsCost(#blocks)
    + 438
    + 210 * ell(M, entries(D)+1)
    + 2,
```

where

```text
ell(M,i) = log_2 floor(i/M).
```

The structural block potential also contains

```text
210 * S_M(s),
S_M(s) = sum_{i=1}^s ell(M,i).
```

Thus a single one-block structure can have a large potential even though the
physical insert itself is constant-time.

## Exact place this enters the proof

`BMTeleLoop.lean` initializes the pivot structure using
`insMany_tele`:

```text
actual_init
+ potential(after BM.6)
+ other-potential
<=
potential(newC)
+ other-potential
+ lpiv.length * DC.ins(l+1).
```

After changing the abstract `initCost` to a separate constant
`DC.initIns`, the full patched build fails exactly here: the existing
amortization still produces `lpiv.length * DC.ins(l+1)`.

So the remaining O(t p) term is not merely an interface overcharge.  It is
currently paying for deferred future work encoded in the lazy-structure
potential.

## Why the potential can be O(t) per pivot

For C-HD,

```text
M_0 = 1
M_{l+1} = t * 2^(l t).
```

For a block containing s entries,

```text
ell(M,s) = Theta(log(s/M)).
```

A call frontier / pivot set can be much larger than the call's local block
parameter M.  In the relevant recursive ranges the ratio can contain a
factor exponential in t, making

```text
log(s/M) = Theta(t).
```

Hence the existing potential can assign Theta(t) amortized cost to a fresh
pivot insertion even though the raw insertion itself is O(1).

## Consequence for the proposed 7/8 exponent

The direct N4 sharpening

```text
g_j <= c_j
```

is unaffected.

However, deleting the second O(t p) term from BM.6 is **not yet justified**.

Therefore the candidate

```text
O(sqrt(m N log N))
```

and the showcase

```text
11/12 -> 7/8
```

remain conditional on a genuinely new amortized initialization argument,
not just a fresh-insert interface field.

## Promising next route: carry initialization potential as credit

The child structure created by a recursive call is not thrown away: its
resulting D structure participates in the later merge back into the parent,
and the existing merge telescope explicitly uses the child's potential.

This suggests a more principled refinement:

1. do not pay the entire newly-created pivot potential at BM.6;
2. carry that potential as a call-level credit/debt through the recursive
   cost record;
3. discharge it when the child structure is consumed/merged or when its
   entries are returned/deleted;
4. leave only genuinely unpaired potential at the root/final boundary.

This would be analogous in spirit to the successful BM.23 `I*p` credit
argument, but applied to the DLazy potential itself.

This is now the main technical question for the second half of the project.
