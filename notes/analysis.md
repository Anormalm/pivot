# C-HD Re-selection Accounting: Candidate \(11/12 \to 7/8\) Refinement

**Status:** research note / proof target, not yet a theorem.  
**Date:** 2026-09-23

## 1. Claim under investigation

C-HD currently proves/analyses

\[
T_{\rm core}
=
O\!\left(
(L+1)N(k+t/k)
+k^2\left(m+1+\frac{NL}{t}\right)
+m(t+\log(t\delta))
\right),
\]

then chooses \(k=\Theta(\sqrt t)\) and
\(t=\Theta((N\log N/m)^{2/3})\), yielding

\[
O\!\left(m^{1/3}(N\log N)^{2/3}\right).
\]

At \(m=n\log^{3/4}n\), this is \(O(n\log^{11/12}n)\).

The candidate refinement is that the \(t/k\) term is an artefact of two
coarse charges:

1. initial pivot insertions (BM.6) are charged as generic \(O(t)\) inserts,
   although they are made into a freshly-created one-block `D` structure; and
2. full-call BM.23 re-selections are bounded by
   \(g_j\le 1+c_j\), although the executable semantics re-select only when the
   residual group is nonempty.

If both charges are tightened, the same algorithmic framework can use a
constant \(k\) (e.g. \(k=4\)) and retune \(t\).

The resulting candidate bound in C-HD's certified density window is

\[
\boxed{
T =
O\!\left(
n+m+m\log\!\left(2+\frac mn\right)
+\sqrt{mn\log n}
\right)
}
\]

up to the existing lower-order block/search logarithms. In particular,

\[
m=n\log^{3/4}n
\quad\Longrightarrow\quad
\boxed{T=O(n\log^{7/8}n)}.
\]

This is conditional on the proof obligations in §7.

---

## 2. Exact source-level observation

### 2.1 BM.23 does **not** reinsert after the last removal

`formal/lean/Frontier/CHD/BM.lean` defines:

```lean
structure Reselect ... where
  resel : forall j,
    sigma.piv j in Ui ->
    (sigma.P j \ Ui).Nonempty ->
    ...
```

and `reselected` contains only groups satisfying both conditions.

`formal/lean/Frontier/CHD/BMCost.lean` agrees:

```lean
markedGroups sigma Ui =
  { j | sigma.piv j in Ui
        and (sigma.P j \ Ui).Nonempty }
```

Thus a child that consumes the final remaining part of a group causes **no**
expensive BM.23 insertion.

### 2.2 Full calls return every original frontier/group vertex

`formal/lean/Frontier/CHD/BMTrace.lean`, `RecFacts.full_S`:

```lean
full_S : r.B' = r.B -> r.S subset r.U
```

Every MakePivots group is a nonempty subset of `S`. Hence, for a full call,
every group vertex is eventually returned either by a child or by the
parent's own final region.

### 2.3 C-HD already has the right "own-home" representation

`formal/lean/Frontier/Homes.lean` defines a vertex's home as:

- `some Y` if it lies in child `Y`'s returned set;
- for a foreign leaf, `some Y` if its fixed value lies in child `Y`'s range;
- `none` otherwise.

For a **group vertex** in a full call, `none` therefore represents a vertex
returned by the parent but by no child (the paper's own/final \(W'\)-type
case).

This `none` colour is precisely the extra colour needed to account for the
case in which every child-home can cause a re-selection.

---

## 3. Proposed sharper lemma

Fix a full call \(X\) and a nonempty pivot group \(P_j\).

Let

\[
H_j=\{\operatorname{home}_X(v):v\in P_j\}.
\]

### Lemma A — actual re-selections

\[
\boxed{g_j\le |H_j|-1.}
\]

Reason:

- sibling child-return sets are disjoint;
- after child \(Y_i\), all \(P_j\cap U_{Y_i}\) vertices are removed;
- BM.23 is charged only if the current pivot is removed **and the group
  remains nonempty**;
- therefore every charged re-selection consumes a distinct child home while
  leaving at least one represented home behind.

Two cases make the `-1` explicit:

1. **No own (`none`) vertex.**  
   The final child home empties the group, so it is not re-selected.

2. **An own (`none`) vertex exists.**  
   Every child home may cause re-selection, but `none` is an additional
   represented home, so
   `#child homes = |H_j|-1`.

No shortest-path ordering assumption is needed for this counting inequality.

### Lemma B — existing tree machinery already pays for \(|H_j|-1\)

C-HD's existing `Reselect.lean` proves, for a PT piece \(F\),

\[
|\operatorname{homes}(F)|
\le
1+\operatorname{bich}(F),
\]

where `bich` counts parent edges whose endpoints have different homes.

`MakePivots` maps every nonempty group into a **distinct** PT piece.
Since \(P_j\subseteq F_j\),

\[
|H_j|-1
\le
|\operatorname{homes}(F_j)|-1
\le
\operatorname{bich}(F_j).
\]

Therefore,

\[
\boxed{
\sum_j g_j
\le
\sum_j \operatorname{bich}(F_j)
}
\]

instead of

\[
\sum_j g_j
\le
p_X+\sum_j\operatorname{bich}(F_j).
\]

The existing `CrBe.lean` machinery already injects/sums these bichromatic
tree edges into the globally charged crossing / foreign-leaf edge sets.
So the expensive \(t\,p_X\) full-call term should disappear.

---

## 4. A second independent tightening: BM.6 initial pivots

`RamPiv.lean` shows BM.5–6 as:

1. create a new `D`;
2. insert all initial pivots.

`BMLazy.lean` defines a new structure as one block:

```lean
def newC ... := <..., [<bottom, []>]>
```

The paper states `Insert NEVER splits`; an insertion searches the separator
stack and prepends to the owning block.

Therefore all BM.6 inserts into that fresh structure have

\[
\#\text{blocks}=1,
\]

so their block search is \(O(1)\), not \(O(t)\).

The current `initCost` instead charges every pivot using the generic
`DC.ins lv`, which is the worst-case insertion cost for an evolved
multi-block structure.

Hence initial pivot insertion should cost

\[
O(p_X)
\]

rather than \(O(t p_X)\).

This tightening is necessary in addition to Lemma A: otherwise the same
\(t/k\) term remains through BM.6.

---

## 5. Conditional new summation

After the two tightenings:

- successful/contact FindPivots work:
  \(O(k(L+1)N)\);
- failed-search work:
  \(O(k^2(m+NL/t))\);
- initial pivot work:
  \(O(p)\), absorbed for constant \(k\);
- full-call re-selection insertion:
  charged only to crossing / foreign-leaf edges, hence \(O(mt)\);
- partial-call re-selection:
  \(O(t|S_X|)=O(|U_X|)\);
- ordinary relaxation/data-structure insertion:
  \(O(mt)\) plus the existing logarithmic terms.

Thus

\[
T_{\rm core}
=
O\!\left(
(L+1)Nk
+k^2\left(m+\frac{NL}{t}\right)
+mt
+\text{lower-order logs}
\right).
\]

Take constant \(k=4\). Existing side conditions \(k\ge4\),
\(3k\le t\), and \(k^2=O(t)\) hold for \(t\ge16\).

Since \(L=\Theta(\log N/t)\),

\[
T_{\rm core}
=
O\!\left(
\frac{N\log N}{t}
+mt
+\text{lower-order terms}
\right).
\]

Balancing gives

\[
t=\Theta\!\left(\sqrt{\frac{N\log N}{m}}\right),
\]

hence

\[
\boxed{
T_{\rm core}
=
O(\sqrt{mN\log N}).
}
\]

At \(m=n\log^\alpha n\),

\[
T=O\!\left(n\log^{(1+\alpha)/2}n\right)
\]

for the dominant core term.

For \(\alpha=3/4\),

\[
(1+\alpha)/2=7/8,
\]

compared with C-HD's current

\[
(2+\alpha)/3=11/12.
\]

---

## 6. Prior work check

Duan–Mao–Shu–Yin (ICALP 2026) already analyze pivot re-selection using
cross-level tree edges, but retain an exceptional once-per-\(P_j\) charge:

> "Except once for each \(P_{X,j}\) ..."

That is exactly the source of the `+1` inherited by the C-HD-style colour
argument.

C-HD adds a more general `home` construction, including the `none`/own case
for vertices returned by the parent but not a child. This appears to provide
the missing colour needed to remove DMSY26's exceptional per-group charge.

Primary source:

- Ran Duan, Xiao Mao, Xinkai Shu, Longhui Yin,
  *A Faster Directed Single-Source Shortest Path Algorithm*,
  ICALP 2026, DOI 10.4230/LIPIcs.ICALP.2026.81.

---

## 7. Remaining proof obligations / possible failure modes

This should **not** be presented to the authors as a theorem until these are
closed.

### P1. Relate actual BM.23 markings to group homes

The current formal counter `mkOf` counts **all children meeting a group**.
It deliberately over-approximates actual `markedGroups`.

We need a new lemma/counter:

\[
\sum_i |\operatorname{markedGroups}(\sigma_i,U_i)|
\le
\sum_j (|H_j|-1).
\]

This should be proved by induction over the parent loop or by an injection
from each actual marking to a non-final represented home.

### P2. Preserve the existing cross/foreign-edge injection

After replacing `groups_colors_le` by its “minus one per nonempty group”
version, confirm that `bich_le_crbe` is unchanged. It appears reusable
verbatim.

### P3. Separate cheap and expensive group events in the cost proof

The current `CostLe` child coefficient combines:

- \(O(k)\) expansion/picking work for every group/child meeting; and
- \(O(t)\) insertion work for actual BM.23 markings.

The refined proof must keep the \(O(k)\) meeting count while applying the
cross-edge-only bound only to the \(O(t)\) insertion part.

For constant \(k\), retaining a `+p` term in the \(O(k)\) part is harmless.

### P4. Re-price BM.6 separately from generic `Insert`

Prove that the new structure has one block throughout BM.6 because `Insert`
does not split. Then replace `p * DC.ins lv` in the BM.6 accounting by
\(O(p)\).

### P5. Retune the parameter lemmas

The frozen program hardcodes \(k=\lceil\sqrt t\rceil\) and the old
\(t\approx(\log N/d)^{2/3}\).

A strengthened theorem needs:

\[
k=4,\qquad
t\approx\sqrt{\log N/d}.
\]

The combinatorial core is already mostly parameterized in \(k,t\), but the
master-cost and dispatcher arithmetic must be redone.

### P6. Data-structure logarithms

With the smaller \(t\), do not silently assume every separator-stack search
is \(O(t)\) for all densities.

For the currently certified window \(d\le\log^{3/4}n\),

\[
t\ge \log^{1/8}n,
\]

while \(\log d,\log L,\log t=O(\log\log n)=o(t)\), so the desired
absorption holds asymptotically.

For a wider density theorem, retain these logarithmic terms explicitly until
the range is re-derived.

---

## 8. Exhaustive sanity checks

`experiments/reselection_exhaustive.py` performs two independent finite
checks.

### Check A — actual re-selection bound

The checker allows **arbitrary adversarial pivot choices**, which is more
permissive than C-HD's minimum-label pivot rule.

For each group it assigns vertices to:

- child homes \(1,\ldots,H\), or
- home `0`, representing parent-own/final vertices.

When a child is processed, its entire home is removed. A re-selection is
charged exactly when the current pivot is removed and the residual group is
nonempty.

Result run for this note:

- **PASS**
- **123,004 exhaustive home/group states**
- no counterexample to
  \[
  g_j\le |\text{represented homes}|-1.
  \]

### Check B — tree colour bound

For every parent-first rooted tree up to 7 vertices and every 3-colouring,
the checker verifies

\[
|\text{colours}(T)|-1\le \#\text{bichromatic parent edges}.
\]

Result:

- **PASS**
- **1,668,504 tree/colour instances**
- no counterexample.

This second inequality is already formally proved in stronger form by the
upstream repository; the brute-force run is only an independent sanity check.

---

## 9. Recommended next move

Do **not** present the conditional complexity as an established theorem yet.

The next proof target should be a small standalone lemma/prototype:

> **Full-call marking lemma.**  
> For every full call \(X\), the total number of actual BM.23 marked-group
> events is at most the total number of bichromatic FindPivots tree edges.

If that lemma is proved on the abstract `LoopRel`/`LoopC` semantics, then:

1. re-run the master-cost algebra with the \(t p\) term deleted;
2. prove BM.6 fresh inserts are \(O(p)\);
3. substitute \(k=4\);
4. retune \(t\);
5. contact the C-HD authors with:
   - the lemma,
   - the changed summation,
   - exhaustive checks,
   - and a minimal patch/proof sketch.

That would be a materially stronger contribution than an implementation
micro-optimization.
