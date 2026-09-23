# Draft outreach email

Subject: C-HD N4: can the full-call +1 per pivot group be removed?

Hi Geby,

I read your C-HD post and the proof package and spent some time tracing the
full-call BM.23 accounting. I think there may be a small sharpening in the
paper's own N4 argument that matters asymptotically.

N4 currently defines `g_j` as the number of re-selections of group `j`
and `c_j` as the number of different-home edges in its containing PT piece.
The proof notes that deleting those `c_j` edges leaves `c_j+1`
monochromatic components, and that pivots removed at different iterations
have different homes, giving

```text
g_j <= c_j + 1.
```

But BM.23 only re-selects when the residual group is nonempty. That seems to
give one additional terminal home/component beyond the `g_j` re-selection
homes:

- if the group is eventually exhausted by a child, the final child removes
  the remaining vertices but causes no BM.23 re-selection;
- otherwise, because the parent call is full, a residual member ends in
  `W'_X`, whose home is 0.

So the same component argument appears to give

```text
g_j + 1 <= c_j + 1,
```

hence

```text
g_j <= c_j.
```

If that is right, the full-call re-selection total loses the current
once-per-group term: `sum g_j <= 2m` instead of `sum p + 2m`.

I also found a separate accounting issue at BM.6. The initial pivots are
inserted into a freshly created one-block DLazy structure, `Insert` does
not split, and the existing block-count/cost lemmas seem to give constant
cost per initial pivot. The current abstract `initCost` instead prices those
with the generic evolved-structure `O(t)` insertion bound.

If both tightenings survive the formal cost proof, the symbolic balance
appears to permit constant `k` and

```text
t ~ sqrt(N log N / m),
```

giving the **conditional** core term

```text
O(sqrt(m N log N)).
```

At the `m = n log^(3/4)n` profile from the post this would be
`n log^(7/8)n` rather than `n log^(11/12)n`.

I have not proved that final theorem in Lean. In particular, the main formal
engineering issue I have found is that the current `CostLog.RecCost`
interface discards the useful `+ I p` credit from the refined loop
telescope before the global `Cr/Be` charging is available, so the cost-log
interface needs to preserve that credit.

I put the source audit, direct N4 patch, candidate Lean lemmas, and
reproducible falsification tests here:

https://github.com/Anormalm/pivot

The main question I wanted to sanity-check with you is simply: **is there a
reason the terminal home above cannot be used to sharpen N4(i) from
`g_j <= c_j+1` to `g_j <= c_j`?**

If there is no obvious blocker, I will keep pushing the credit-carrying
CostLog patch and parameter retuning toward an actual Lean build.

Best,
Lifan
