# Proof status

Date: 2026-09-23

This note separates what is already elementary/source-level from what still
has to be proved inside the upstream C-HD formal cost chain.

## Established / locally compiled against the upstream snapshot

### 1. Exact one-group re-selection combinatorics

For a nonempty group whose members are partitioned into child homes plus the
parent-own/final home, the adversarial maximum number of expensive BM.23
re-selections is exactly

```text
#child homes                  if the own/final home is represented
#child homes - 1              otherwise
```

equivalently

```text
max reselections = #represented homes - 1.
```

This is an elementary case analysis and is independently checked by
`experiments/exact_characterization.py` on 585,978 states.

### 2. Fresh BM.6 insertion is linear in the number of pivots

The upstream DLazy source already proves that:

- `newC` creates a one-block structure;
- `Insert` does not split blocks;
- the list insertion cost is bounded by
  `length * (log2(#blocks) + 4)`.

Therefore BM.6 insertion into the fresh structure is `O(p)`, not
`O(t p)`. See `notes/fresh_insert_audit.md`.

### 3. Loop telescope holds in the abstract home model

For the actual marked/emptied definitions abstracted at the home level:

```text
marked_i + emptied_i <= meetings_i
final_nonempty + total_emptied = p
final_nonempty = own_groups
```

hence

```text
total_marked + p <= total_meetings + own_groups.
```

A 200,000-trial direct loop-state stress test produced zero violations.
See `experiments/loop_telescope.py` and
`results/loop_telescope_summary.json`.

These experiments are falsification tests, not formal proof objects.

### 4. Own-home colour bridge survives exhaustive finite checking

The proposed per-group strengthening

```text
#children meeting P + [P contains an own/none home]
    <= #distinct homes(P)
```

combined with the existing upstream colour lemma was checked on
**5,699,730** nonempty group subsets of parent-first trees up to 6 vertices,
with zero violations.

A generic source-aligned candidate strengthening of
`Ranges.card_children_meeting_le` is in
`drafts/HomeOwnColourCandidate.lean`.

## Already available upstream and intended to be reused

The C-HD snapshot already proves the tree-colour side:

```text
#distinct homes in a containing PT piece - 1
    <= #bichromatic parent edges in the piece.
```

It also already charges bichromatic tree edges to `Cr` / `Be`, and for
full calls proves `S_X subset U_X`.

The proposed refinement should therefore be a cost-accounting patch, not a
new shortest-path correctness argument.

## Still unproved in upstream Lean

### P1. Finite-set and one-iteration layer — COMPILED

GitHub Actions checks the candidates against the exact audited C-HD snapshot
`98c53acc...` using Lean 4.34.0.

The following modules compiled without errors in workflow run
`35839815618`:

- `drafts/LoopCostFiniteCandidates.lean`
  - exact nonempty/emptying partition;
  - emptied groups meet the child;
  - marked and emptied groups are disjoint;
  - `marked + emptied <= meetings`.
- `drafts/IterCostRefinedCandidate.lean`
  - refined one-step cost inequality with `I * emptied` credit;
  - exact loop-entry nonempty-group count.
- `drafts/HomeOwnColourCandidate.lean`
  - generic extra-`none` home colour lemma.
- `drafts/FreshInsertCandidate.lean`
  - fresh one-block insertion bound.

The same CI run localized the remaining failures to the aggregate loop
telescope and aggregate own-home colour theorem; no error was reported in
the four modules above.

### P1a. Refined loop insertion-credit telescope — IN CI

Strengthen the current one-sided nonempty-group lemma to an equality and
telescope `emptiedGroups` through the loop.

Target shape:

```text
total_marked + p <= mkOf(X) + ownGroupsOf(X).
```

### P2. Residual group -> own `none` home — SOURCE CLOSED / TRANSPORT OPEN

For a full call, every group still nonempty after the child loop meets the
parent's final `W'` region, and such a member is in the parent return but
in no direct child return.  The existing `Ranges.home` definition therefore
returns `none`.

Upstream `BMTrace.callC_log` already contains this exact ownership argument
locally for sources of `W'` relaxation edges.  The remaining work is to
export/generalize it for arbitrary `W'` vertices in the traced log.

### P3. Refined colour inequality with own groups — IN CI

The generic extra-`none` colour lemma already compiles.  The aggregate
`MkOwnColourCandidate` proof is being checked after repairing only the
bridge from `Finset.image home` to `(List.map home).toFinset`.

Target:

```text
mkOf(X) + ownGroupsOf(X)
    <= p + |Cr(X)| + |Be(X)|.
```

Combining P1 and P3 cancels the `p`:

```text
total_marked <= |Cr(X)| + |Be(X)|.
```

This is the key removal of the expensive once-per-group insertion charge.

### P4. Separate fresh and evolved insertion costs — LOCAL LEMMA COMPILED

The fresh one-block insertion lemma compiles against the upstream snapshot.
The remaining task is interface integration: refine `DCost/initCost` so
BM.6 consumes that constant bound while BM.23/BM.25/BM.28 retain the evolved
`DC.ins(l)` charge.

### P5. Preserve the `I*p` credit through CostLog — FORMAL ARCHITECTURE OPEN

The strengthened loop theorem naturally carries `cost + I*p` for full
calls.  Current `RecCost/budOf` discards that credit before `CostLe`
sees the global `Cr/Be` counters.

The current preferred patch is a generic
`RecCostCredit` relation, drafted in
`drafts/RecCostCreditCandidate.lean`, with a record-local full-call credit
`I*p`.  No change to shortest-path semantics, `CallRec`, or `LogInv`
is required.

### P6. Re-run master algebra and parameter arithmetic

Only after the remaining P1a/P2/P3/P4/P5 integration closes should the parameters be changed to the candidate

```text
k = 4
t = Theta(sqrt(N log N / m)).
```

The resulting candidate core expression is

```text
O(N log N / t + m t)
    = O(sqrt(m N log N)).
```

At `m = n log^(3/4) n`, this would change the dominant logarithmic exponent

```text
11/12 -> 7/8.
```

## Claim discipline

Until the aggregate lemmas, credit-carrying cost chain, and parameter layer are compiled and integrated into the upstream model, this
repository should say:

- "candidate refinement";
- "conditional bound";
- "source-level overcharge";
- "experimentally stress-tested combinatorial lemma".

It should **not** say that an improved SSSP theorem has been proved.
