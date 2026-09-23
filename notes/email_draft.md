# Draft outreach email

Subject: Possible tightening in C-HD pivot re-selection accounting

Hi Geby,

I read your C-HD post and the proof package and spent some time tracing the
full-call pivot accounting through `LoopCost.lean`, `BMCost.lean`,
`Reselect.lean`, and `CrBe.lean`. I think there may be a removable
once-per-pivot-group **expensive** charge in BM.23.

The executable semantics only re-select group `P_j` when its current pivot
is returned by child `U_i` **and** `P_j \\ U_i` is nonempty. In a full
call, `RecFacts.full_S` gives `S subset U`, so the last represented home
of a group empties the group and causes no re-selection. This seems to give

```text
g_j <= #homes(P_j) - 1.
```

The existing PT-piece colour lemma already has

```text
#homes(piece) - 1 <= #bichromatic parent edges(piece),
```

so I am trying to replace the expensive part of the current
`g_j <= 1 + c_j` accounting by a cross-edge-only charge. The present
`LoopCost` abstraction counts all child/group meetings, which looks like
where the extra `+1` survives.

There is also a separate BM.6 accounting issue: the initial pivots are
inserted into a fresh one-block DLazy structure, and `Insert` does not split,
so those inserts appear to be O(1) each rather than the generic evolved
O(t) insertion charge used by `initCost`.

If both tightenings survive formalization, the symbolic balance looks like
`N log N / t + m t` with constant `k`, giving the **conditional** candidate
`O(sqrt(m N log N))` core term -- `n log^(7/8)n` at
`m = n log^(3/4)n`. I have not proved that final theorem in Lean.

I put the source audit, proof sketch, and falsification tests here:
https://github.com/Anormalm/pivot

So far the checks include 585,978 exhaustive single-group states, 1.67M
tree/colour cases, 50k random trials, and 200k direct loop-telescope trials,
with no violations. I also wrote source-aligned candidate finite-set lemmas
against the current `LoopCost.lean` definitions.

The main thing I wanted to ask: **is there a reason the full-call BM.23
analysis really needs one exceptional expensive re-selection per pivot
group, rather than using the final residual/own `none` home to eliminate
that exception?**

If there is no obvious blocker, I can keep pushing this toward a proper Lean
patch.

Best,
Lifan
