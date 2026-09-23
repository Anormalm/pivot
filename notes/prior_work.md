# Prior-work audit

**Last checked:** 2026-09-23

This note records the closest results found for the proposed C-HD re-selection
accounting refinement. It is a dated search log, not a proof of novelty.

## 1. Duan–Mao–Mao–Shu–Yin 2025

**Breaking the Sorting Barrier for Directed Single-Source Shortest Paths**  
arXiv:2504.17033

Deterministic directed SSSP with nonnegative real weights in the
comparison-addition model:

```text
O(m log^(2/3) n).
```

This introduced the modern BMSSP / FindPivots framework on which the later
work builds.

Primary source:
<https://arxiv.org/abs/2504.17033>

## 2. Duan–Mao–Shu–Yin 2026

**A Faster Directed Single-Source Shortest Path Algorithm**  
ICALP 2026 / arXiv:2602.07868

Theorem 1 gives

```text
O(m sqrt(log n) + sqrt(m n log n log log n)).
```

Primary source:
<https://doi.org/10.4230/LIPIcs.ICALP.2026.81>

This is particularly relevant because its re-selection analysis explicitly
contains the once-per-group exception that the current project is trying to
remove.

In the ICALP HTML, the running-time analysis says that re-selection and
insertion cost O(t) per pivot group. For a full call, it injects re-selections
into vertices lying in distinct child-return sets and bounds those child
regions by one plus the number of cross-level tree edges. It then states:

> “Except once for each P_{X,j} ...”

and charges that exception as

```text
O(p_X t).
```

See the discussion around lines 470–480 in the HTML version:
<https://drops.dagstuhl.de/storage/00lipics/lipics-vol374-icalp2026/html/LIPIcs.ICALP.2026.81/LIPIcs.ICALP.2026.81.html>

That is the closest prior version of the `+1` currently inherited by C-HD's
generic colour-count argument.

## 3. C-HD, September 2026

Repository:
<https://github.com/spicylemonade/c-hd-proof>

The audited snapshot proves a density-regime directed comparison-addition
bound

```text
O(
  n + m
  + m log(2 + m/n)
  + m^(1/3) (n log n)^(2/3)
).
```

At

```text
m = n log^(3/4) n
```

the dominant term is

```text
n log^(11/12) n.
```

C-HD changes the local FindPivots accounting substantially relative to
DMSY26, including counted unexplored leaves, permanent deletion of
provably-invalid edges, foreign-leaf home accounting, and a new lazy block
structure.

The candidate in this repository is **not** “replace the local array by a
heap” and is **not** simply “cache failed searches”; those ideas overlap
existing work.

## 4. Kadria–Roditty 2026

**A Faster Undirected Single-Source Shortest Path Algorithm**  
arXiv:2609.15247

This improves the **undirected** problem. It is important context but does
not directly pre-empt a deterministic directed comparison-addition
improvement.

Primary source:
<https://arxiv.org/abs/2609.15247>

## 5. Cai 2026

**Beyond Distance Ordering: Resource Complexity and Universal Optimality of
Exact Labeled Directed Shortest Paths**  
arXiv:2609.04825

This studies resource complexity and universal optimality for exact labeled
directed shortest paths. It also uses the current deterministic directed SSSP
bound as an ingredient. It does not, from the result located in this audit,
supply the candidate `O(sqrt(m n log n))` directed comparison-addition upper
bound considered here.

Primary source:
<https://arxiv.org/abs/2609.04825>

## 6. Hair–Li–Li–Zhang 2026

**Bellman-Ford in Almost-Linear Time**  
arXiv:2607.19346

This gives an `m^(1+o(1))` result for directed SSSP with real, possibly
negative, edge weights. It belongs to a different algorithmic/model line
than the deterministic nonnegative comparison-addition bound being studied
here, so it should be discussed but not treated as the same claimed result.

Primary source:
<https://arxiv.org/abs/2607.19346>

## 7. Targeted search outcome

Queries run on 2026-09-23 included variants of:

```text
"directed" "single-source shortest path" "sqrt(mn log n)"
"directed SSSP" "sqrt(mn"
"pivot" "re-selection" shortest path "P_j"
"except once for each" "P_{X,j}" shortest path
"C-HD" shortest path 7/8
"n log^{7/8}" shortest path directed
"comparison-addition" directed SSSP 2026
```

The search did **not** surface a published deterministic directed
comparison-addition result with the exact candidate core term

```text
O(sqrt(m n log n))
```

or an analysis explicitly removing the once-per-pivot-group re-selection
exception.

The closest located primary upper bound remains DMSY26:

```text
O(m sqrt(log n) + sqrt(m n log n log log n)).
```

This is only evidence from a targeted web/arXiv-style search. Before making
a novelty claim to authors or in a paper, repeat the search through broader
bibliographic indexes and citation graphs.

## 8. Novelty claim we are *not* making yet

The repository should currently say:

> We found a candidate tightening of C-HD's cost accounting which, if its
> remaining proof obligations close, would permit a different parameter
> balance and yield an `O(sqrt(m n log n))` core term in the relevant
> density regime.

It should **not** yet say:

> We proved a new faster directed SSSP algorithm.

The latter requires the Lean/cost proof, parameter retuning, and a final
novelty audit.
