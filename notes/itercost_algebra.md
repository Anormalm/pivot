# Strengthened one-step cost algebra

Date: 2026-09-23

This note records the cleanest form of the cost refinement after reading the
complete upstream `LoopCost.lean`.

## 1. Current group-dependent iteration cost

Ignoring terms independent of pivot groups, upstream `iterCost` contains:

```text
pulled-group expansion
+ BM.23 residual scan
+ BM.23 insertion
```

For a child return `U_i`, let:

```text
M_i = # actual marked groups
E_i = # groups emptied by U_i
H_i = # original groups meeting U_i
I   = generic D insertion cost = O(t)
g   = max pivot-group size = O(k)
```

Upstream already proves the pulled-group expansion term is at most

```text
g (M_i + E_i)
```

and BM.23 costs at most

```text
(g + 1 + I) M_i.
```

Therefore the total group-dependent work is

```text
g(M_i+E_i) + (g+1+I)M_i.
```

Split this as

```text
[g(M_i+E_i) + (g+1)M_i] + I M_i.
```

The cheap bracket satisfies

```text
g(M_i+E_i) + (g+1)M_i
    <= (2g+1)(M_i+E_i).
```

The candidate finite-set lemmas give

```text
M_i + E_i <= H_i.
```

Hence

```text
group work <= (2g+1) H_i + I M_i.
```

This is the key separation missing from the current abstract cost proof:
the expensive `I` factor only needs to multiply **actual marked events**,
not every child/group meeting.

## 2. Add emptying credit

Because

```text
M_i + E_i <= H_i,
```

we also have

```text
I M_i + I E_i <= I H_i.
```

Therefore

```text
iterCost_i + I E_i
  <= ordinary terms + (2g+1+I) H_i.
```

This is exactly the form needed for telescoping.

## 3. Exact potential identity

The strengthened finite-set lemma is

```text
nonempty_{i+1} + E_i = nonempty_i.
```

Summing over the loop:

```text
sum_i E_i = nonempty_initial - nonempty_final.
```

Thus the one-step inequalities telescope to

```text
loopCost + I * nonempty_initial
  <= ordinary child/edge charges
     + I * total_meetings
     + I * nonempty_final.
```

At call entry all original pivot groups are nonempty:

```text
nonempty_initial = p.
```

For a full call, every final residual group contributes an own/final
`none` home, so

```text
nonempty_final <= ownGroups.
```

Also:

```text
total_meetings = mkOf.
```

Therefore

```text
loopCost + I p
  <= cheap + I (mkOf + ownGroups).
```

The proposed home-colour strengthening is

```text
mkOf + ownGroups <= p + |Cr| + |Be|.
```

Substitute:

```text
loopCost + I p
  <= cheap + I p + I(|Cr|+|Be|).
```

Cancel `I p`:

```text
loopCost <= cheap + I(|Cr|+|Be|).
```

This removes the expensive once-per-group charge while preserving the
existing cheap O(k) group-meeting charge.

## 4. Why this is stronger than simply proving g_j <= c_j

The per-group statement is intuitive, but the loop-level formulation above
matches the existing Lean architecture much better:

- no new event log is required;
- `markedGroups`, `emptiedGroups`, and `nonemptyCount` already exist;
- the child meeting count is already represented by `childCharge`;
- the proof can reuse the current `loopC_cost` induction structure almost
  verbatim;
- only the coefficient bookkeeping changes.

This is now the preferred formal route.
