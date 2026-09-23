# New parameter route for the candidate bound

**Status:** arithmetic derivation / formalization target, not compiled Lean.  
**Date:** 2026-09-23.

This note addresses the main obstacle found after the local cost refinements:
the frozen parameter layer uses

```text
(lgN)^2 <= t^3 * dd^2,
```

which forces the old
`t ~ (lgN/dd)^(2/3)` scale.

That inequality is not a BMSSP correctness requirement. It is the defining
property of the old `tpar/tF` choice and is used to fit the old master terms
inside the old `m^(1/3)(n log n)^(2/3)` envelope.

For the refined cost expression, replace it by

```text
lgN <= t^2 * dd.
```

This corresponds to

```text
t ~ sqrt(lgN/dd).
```

The key question is whether the other parameter lemmas, especially the
recursive DLazy insertion charge `I = O(t)`, still hold. They do
asymptotically on the same Gate-C density branch.

---

## 1. Candidate parameter definitions

Conceptually:

```text
t_new = max(16, ceil_sqrt(ceil(lgN / dd)))
k_new = 4
L_new = floor(lgN / t_new) + 1
```

Choose the integer implementation so that the kernel-friendly specification is

```text
lgN <= t_new^2 * dd.
```

The exact rounding implementation can use the existing natural-number
arithmetic library; it does not need to match this pseudocode literally.

Keep the existing level scales:

```text
M_l   = t * 2^((l-1)t)
tau_l = t^3 * 2^(lt).
```

With `k=4` and `t>=16`, all of the current easy side conditions remain true:

```text
2 <= k
k <= t
3k <= t
k(k+1) = 20 <= 2t.
```

The current stronger condition `3k <= t` is more than enough for

```text
3k * M_(l+1) <= tau_l.
```

---

## 2. Top-level recursion depth remains valid

Keep

```text
L = floor(lgN/t) + 1.
```

The existing proof of

```text
lgN + 1 <= L*t
```

uses only `t>0`, not the old cube-root parameter specification.

Therefore the existing top-cap argument still gives

```text
tau_L = t^3 * 2^(Lt) > 2N
```

for `t>=16`.

So recursion termination / top coverage does not require
`(lgN)^2 <= t^3 dd^2`.

---

## 3. Density branch gives a polynomial bound on `lgN` in the new `t`

The frozen Gate-C branch has

```text
dd <= F + 1
F^4 <= (log_2 N)^3 <= lgN^3.
```

Assume the new parameter specification

```text
lgN <= t^2 * dd.
```

Then

```text
F^4
<= lgN^3
<= (t^2 * dd)^3
<= (t^2 * (F+1))^3.
```

If `F>0`, then `F+1 <= 2F`, so

```text
F^4 <= 8 * t^6 * F^3
```

and cancellation gives

```text
F <= 8 * t^6.
```

If `F=0`, the bound is trivial.

Thus uniformly, for `t>=1` we may use a loose bound such as

```text
F + 1 <= 16 * t^6.
```

Hence

```text
dd <= 16 * t^6
```

and the new parameter specification gives

```text
lgN <= t^2 * dd <= 16 * t^8.
```

This is the direct new analogue of the current theorem

```lean
mc_lgN_le : lgN <= 16 * tF^6
```

with exponent 8 instead of 6.

The exponent 8 is completely adequate for the logarithmic block-search
analysis.

---

## 4. Recursive DLazy insertion remains O(t)

The current insertion proof uses

```text
rho = (3(L+1) + 3 delta) * 2 t^2 * 2^t
```

and then bounds

```text
log_2(8 rho + 8) = O(t).
```

Under the new parameter facts:

```text
L <= lgN + 1 <= 16 t^8 + 1,
delta <= 5 dd <= 80 t^6.
```

Therefore for `t>=16`,

```text
3(L+1) + 3delta = O(t^8),
rho = O(t^10 * 2^t).
```

Since

```text
t < 2^t
```

for positive `t`,

```text
t^10 < 2^(10t).
```

Any fixed multiplicative constant is at most `2^(O(t))` for `t>=16`.
Therefore

```text
rho < 2^(C t)
```

for an absolute constant `C` (a loose `C=13` or `C=18` is enough after
checking the additive 8).

Hence

```text
log_2(8rho+8) = O(t),
```

and the existing insertion charge

```text
211 * log_2(8rho+8) + 441
```

remains

```text
O(t).
```

So the new smaller `t` does **not** asymptotically break the evolved
multi-block insertion bound on the current density branch.

A new Lean theorem should mirror `MasterCost.mc_ins_le`, replacing the old
`mc_lgN_le` input by

```text
mc_lgN_le_new : lgN <= C8 * t^8.
```

No data-structure redesign is needed for this step.

---

## 5. Refined master expression

After both local accounting fixes:

1. BM.6 fresh pivot insertion is `O(p)`, not `O(tp)`;
2. full-call actual BM.23 insertions are charged to `Cr/Be` only, not
   `p + Cr + Be`;

the §5.6 expression becomes

```text
T_core =
O(
  (L+1) N k
  + k^2 (m + 1 + N L/t)
  + m (t + log(t delta))
  + lower-order terms already present
).
```

Set `k=4`. Since

```text
L = Theta(lgN/t),
```

we get

```text
T_core =
O(
  N lgN/t
  + N
  + m
  + N lgN/t^2
  + m t
  + m log(t delta)
).
```

The new parameter condition

```text
lgN <= t^2 dd
```

with `m ≍ N dd` implies

```text
N lgN/t^2 <= N dd = O(m),
```

so the failed-Q correction is lower order.

Thus the dominant balance is

```text
N lgN/t + m t.
```

Choosing

```text
t = Theta(sqrt(N lgN/m))
  = Theta(sqrt(lgN/dd))
```

gives

```text
T_core = O(sqrt(m N lgN))
```

plus the preprocessing / logarithmic terms.

---

## 6. Check the remaining lower-order terms in the formal density window

Take

```text
m = n log^alpha n,   1/2 <= alpha <= 3/4.
```

Then

```text
t = log^((1-alpha)/2) n.
```

The candidate dominant exponent is

```text
beta = (1+alpha)/2.
```

Other terms:

### Preprocessing

```text
m log delta
= n log^alpha n * O(log log n)
= o(n log^beta n)
```

because `beta-alpha=(1-alpha)/2>0`.

### Block-search logarithm

```text
m log(t delta)
= n log^alpha n * O(log log n)
= o(n log^beta n).
```

### Failed-search correction

```text
N lgN/t^2
= O(N dd)
= O(m).
```

### Constant-k search term

```text
k^2 m = O(m).
```

### The old A_M extra from the paper-level analysis

The paper's non-formal DS' case analysis gives

```text
O(N t + m log(t delta)).
```

Here

```text
N t = n log^((1-alpha)/2)n
```

which is strictly below
`n log^((1+alpha)/2)n`.

Thus no currently visible lower-order term overtakes the candidate square-root
term on the certified branch.

---

## 7. Formal changes required

This parameter change is not free. The frozen proof hardcodes `tF/kF/LF`
throughout L6.

Required work:

1. Define `tNew` with specification
   `lgN <= tNew^2 * dd`.
2. Define `kNew := 4`.
3. Keep `LNew := lgN/tNew + 1`.
4. Reprove the elementary parameter lemmas:
   - `k(k+1) <= 2t`;
   - `3k <= t`;
   - `lgN+1 <= L*t`;
   - `tau(L)>2n`.
5. Replace `mc_lgN_le` by the new `O(t^8)` lemma above.
6. Reprove `mc_ins_le` using the new exponent-8 polynomial bound.
7. Replace the old `CostSkeleton.core_gen` / `mainTerm` algebra with the
   square-root master term.
8. Update `Tnat` / preallocation comparison for the new time envelope.
9. Update `Params.lean`, `LevelTab`, `LevelRoute`, and the top-level
   dispatcher wiring to the new functions.
10. Rebuild and rerun the kernel/axiom audit.

The key point is that item 5--6 are a **parameter-proof rewrite**, not an
algorithmic obstruction.

---

## 8. Current confidence level

The chain now separates into three parts:

### Confirmed from upstream existing lemmas

- BM.6 fresh insertion has constant cost per pivot at the DLazy operation
  level.
- Insert never splits and the fresh structure remains one block.
- The actual BM.23 semantics do not re-select after a group becomes empty.
- Existing home/PT-piece machinery bounds colours by one plus bichromatic
  edges.

### Elementary but not yet kernel-checked in our patch

- exact emptying telescope;
- `total_marked + p <= mkOf + ownGroupsOf`;
- the strengthened home-colour inequality including the own/`none` colour;
- the new `lgN <= O(t^8)` density arithmetic.

### Still substantial formal engineering

- cost-record interface changes for fresh insertion;
- splitting cheap O(k) group work from expensive O(t) re-selection work;
- new parameter program and final master envelope;
- full RAM refinement rebuild.

So `O(sqrt(mN log N))` remains a candidate theorem, but the previously
identified `t^3 dd^2` condition no longer looks like a structural blocker.
