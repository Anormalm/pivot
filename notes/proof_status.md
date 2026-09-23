# Proof status

Date: 2026-09-23

This note separates what is already elementary/source-level from what still
has to be proved inside the upstream C-HD formal cost chain.

## Established outside the upstream Lean build

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

### P1. Exact emptying telescope over `LoopC`

Strengthen the current one-sided nonempty-group lemma to an equality and
telescope `emptiedGroups` through the loop.

Target shape:

```text
total_marked + p <= mkOf(X) + ownGroupsOf(X).
```

### P2. Residual group -> own `none` home

For a full call, show that every group still nonempty after the child loop
meets the parent's final `W'` region, and that such members have
`home_X = none`.

### P3. Refined colour inequality with own groups

Prove:

```text
mkOf(X) + ownGroupsOf(X)
    <= p + |Cr(X)| + |Be(X)|.
```

Combining P1 and P3 cancels the `p`:

```text
total_marked <= |Cr(X)| + |Be(X)|.
```

This is the key removal of the expensive once-per-group insertion charge.

### P4. Separate fresh and evolved insertion costs

Refine `DCost.initCost` so BM.6 uses the source-level constant fresh-insert
bound while BM.23/BM.25/BM.28 retain the ordinary evolved `DC.ins(l)`
charge.

### P5. Re-run master algebra and parameter arithmetic

Only after P1--P4 close should the parameters be changed to the candidate

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

Until P1--P5 are compiled and integrated into the upstream model, this
repository should say:

- "candidate refinement";
- "conditional bound";
- "source-level overcharge";
- "experimentally stress-tested combinatorial lemma".

It should **not** say that an improved SSSP theorem has been proved.
