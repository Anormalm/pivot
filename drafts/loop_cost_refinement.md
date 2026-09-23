# Draft: first `LoopCost.lean` refinement lemmas

**Status:** source-aligned Lean sketch; **not compiled** in the current environment.

The current execution environment has no Lean/Lake toolchain and no outbound Git access, so this file is deliberately a patch sketch rather than a claimed checked proof. It targets upstream snapshot `98c53accb47a505482a1781597ae14bf67e81cec`.

The first three lemmas are purely finite-set bookkeeping. They are the earliest formal failure points for the proposed re-selection refinement.

## 1. Exact group emptying

The upstream theorem `card_nonempty_next` proves only `<=`. By definition the two sides actually partition the current nonempty groups.

Candidate replacement/addition in `formal/lean/Frontier/CHD/LoopCost.lean`:

```lean
/-- The nonempty residual groups and the groups emptied by `Ui` partition
    the currently nonempty groups. -/
theorem card_nonempty_next_eq {p : ℕ} (σ : LState G s p)
    (Ui : Finset (Fin G.n)) :
    (Finset.univ.filter (fun j => (σ.P j \ Ui).Nonempty)).card +
        (emptiedGroups σ Ui).card =
      (Finset.univ.filter (fun j => (σ.P j).Nonempty)).card := by
  classical
  have hdisj : Disjoint
      (Finset.univ.filter (fun j => (σ.P j \ Ui).Nonempty))
      (emptiedGroups σ Ui) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, emptiedGroups] at h1 h2
    obtain ⟨x, hx⟩ := h1
    exact (Finset.mem_sdiff.mp hx).2 (h2.2 (Finset.mem_sdiff.mp hx).1)
  have hunion :
      (Finset.univ.filter (fun j => (σ.P j \ Ui).Nonempty)) ∪
          emptiedGroups σ Ui =
        Finset.univ.filter (fun j => (σ.P j).Nonempty) := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, emptiedGroups]
    constructor
    · rintro (hres | hemp)
      · obtain ⟨x, hx⟩ := hres
        exact ⟨x, (Finset.mem_sdiff.mp hx).1⟩
      · exact hemp.1
    · intro hne
      by_cases hres : (σ.P j \ Ui).Nonempty
      · exact Or.inl hres
      · right
        refine ⟨hne, ?_⟩
        intro x hx
        by_contra hxU
        exact hres ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxU⟩⟩
  rw [← hunion, Finset.card_union_of_disjoint hdisj]
```

## 2. Empty groups also meet the child

`marked_sub_meeting` already proves the analogous fact for marked groups.

```lean
/-- A group emptied by `Ui` meets `Ui` through its original group `P0`. -/
theorem emptied_sub_meeting {p : ℕ} (σ : LState G s p)
    (P0 : Fin p → Finset (Fin G.n))
    (hsub : ∀ j, σ.P j ⊆ P0 j) (Ui : Finset (Fin G.n)) :
    emptiedGroups σ Ui ⊆
      Finset.univ.filter (fun j => (P0 j ∩ Ui).Nonempty) := by
  classical
  intro j hj
  simp only [emptiedGroups, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  obtain ⟨hne, hUi⟩ := hj
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, Finset.mem_inter.mpr ⟨hsub j hx, hUi hx⟩⟩
```

## 3. Marked + emptied groups fit inside the meeting budget

The two event types are disjoint: marked means a nonempty residual exists; emptied means the whole current group lies in `Ui`.

```lean
/-- Marked and emptied groups are disjoint event types, and together inject
    into original groups meeting `Ui`. -/
theorem marked_emptied_card_le_meeting {p : ℕ} (σ : LState G s p)
    (P0 : Fin p → Finset (Fin G.n))
    (hsub : ∀ j, σ.P j ⊆ P0 j)
    (hpiv : ∀ j, (σ.P j).Nonempty → σ.piv j ∈ σ.P j)
    (Ui : Finset (Fin G.n)) :
    (markedGroups σ Ui).card + (emptiedGroups σ Ui).card ≤
      (Finset.univ.filter (fun j => (P0 j ∩ Ui).Nonempty)).card := by
  classical
  have hd : Disjoint (markedGroups σ Ui) (emptiedGroups σ Ui) := by
    rw [Finset.disjoint_left]
    intro j hm he
    simp only [markedGroups, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    simp only [emptiedGroups, Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨_, hres⟩ := hm
    obtain ⟨x, hx⟩ := hres
    exact (Finset.mem_sdiff.mp hx).2 (he.2 (Finset.mem_sdiff.mp hx).1)
  have hsubu : markedGroups σ Ui ∪ emptiedGroups σ Ui ⊆
      Finset.univ.filter (fun j => (P0 j ∩ Ui).Nonempty) :=
    Finset.union_subset
      (marked_sub_meeting σ P0 hsub hpiv Ui)
      (emptied_sub_meeting σ P0 hsub Ui)
  calc
    (markedGroups σ Ui).card + (emptiedGroups σ Ui).card =
        (markedGroups σ Ui ∪ emptiedGroups σ Ui).card :=
      (Finset.card_union_of_disjoint hd).symm
    _ ≤ (Finset.univ.filter (fun j => (P0 j ∩ Ui).Nonempty)).card :=
      Finset.card_le_card hsubu
```

## 4. One-step cost inequality to prove next

Let

```text
M = |markedGroups σ Ui|
E = |emptiedGroups σ Ui|
R = |{j : P0 j meets Ui}|
```

From the lemmas above,

```text
M + E <= R.
```

The group-dependent terms in upstream `iterCost` are bounded by

```text
g(M + E)        -- pulled-group expansion
+ (g+1+I)M      -- residual scan + bookkeeping + BM.23 insertion
```

so adding an emptying credit `I E` gives

```text
g(M+E) + (g+1+I)M + I E
= (2g+1+I)M + (g+I)E
<= (2g+1+I)(M+E)
<= (2g+1+I)R.
```

The next Lean theorem should therefore be a sibling of `iterCost_le`:

```lean
iterCost_le_with_empty_credit :
  iterCost DC lv σ S0 Ui nL + I * (emptiedGroups σ Ui).card
    <=
  (1 + bp + bd)
  + (ap + ad + 4) * Ui.card
  + (1 + I) * nL
  + (2 * g + 1 + I) * meeting.card
```

with `meeting = Finset.univ.filter (fun j => (P0 j ∩ Ui).Nonempty)` and the same `hpull`, `hdel`, `hins`, group-size, and pulled-group hypotheses as the current theorem.

## 5. Why this is useful

Once the exact emptying identity telescopes through `LoopC`, the expensive insertion coefficient receives a credit for every group that permanently disappears. At a full parent call, the groups that remain at the end supply the missing `none` home, so the combination

```text
child meetings + final residual groups
```

can be bounded by the existing home-colour/PT-piece machinery. This is the route to removing the `+p` only from the expensive `O(t)` part while keeping the safe `O(k) * p` scan charge.


## 6. Correct potential orientation for the loop theorem

Inspecting the upstream proof shows that the refined insertion credit should
not reuse the current potential orientation.

The current theorem is:

```lean
c + g * nonemptyCount sigma'
  <=
1 + g * nonemptyCount sigma
  + childSum ...
  + (1 + I) * J.card
```

That orientation is appropriate for paying the pulled-group expansion term
with a `g * emptied` credit, but it does not expose the desired negative
once-per-group insertion term.

For the BM.23 insertion refinement, use the exact identity

```text
nonempty_now = nonempty_next + emptied
```

and

```text
marked + emptied <= meeting.
```

Then

```text
I * marked + I * nonempty_now
  <=
I * meeting + I * nonempty_next.
```

So the refined loop theorem should put the insertion potential in the
**opposite direction**:

```lean
/-- Candidate refined main-loop cost theorem.
    The expensive insertion potential flows from the initial nonempty groups
    to the final residual groups. -/
theorem loopC_cost_refined
    (hpre : CallPre B S d0)
    (hfp : FPContract B S d0 d1 p P0 Q W)
    {tau : Nat -> Nat} {Inv : Phi -> Prop}
    {sub : SubRelC G s Phi Omega} {l : Nat}
    (hsub : GoodSub G s tau Inv l sub)
    {taul : Nat} {ap bp ad bd I g : Nat}
    (hpull : forall x, DC.pull (l + 1) x <= ap * x + bp)
    (hdel : forall x, DC.del (l + 1) x <= ad * x + bd)
    (hins : DC.ins (l + 1) <= I)
    (hP0 : forall j, (P0 j).card <= g)
    (hMtau : DC.M (l + 1) <= tau l)
    (hgMtau : g * DC.M (l + 1) <= tau l) :
    forall i (sigma : LState G s p) phi sigma' phi' lg J cm c,
      LoopC G s DC sub (l + 1) B taul i sigma phi sigma' phi' lg J cm c ->
      LInv G s B S d0 d1 P0 B'0 sigma ->
      Inv phi ->
      c + I * nonemptyCount sigma
        <=
      1
        + childSum
            (childCharge P0
              (1 + bp + bd)
              (ap + ad + 4)
              (2 * g + 1 + I))
            lg
        + (1 + I) * J.card
        + I * nonemptyCount sigma'
```

The exact theorem may need an additional cheap `g`-potential term if the
existing pulled-group algebra is reused verbatim. The preferred route is to
absorb all `g(marked+emptied)` work directly into the same meeting count
using `marked_emptied_card_le_meeting`, which makes the pure `I` potential
above sufficient.

### One-step algebra

Let

```text
M = marked.card
E = emptied.card
R = meeting.card.
```

The group-dependent iteration work is bounded by

```text
g(M+E) + (g+1+I)M.
```

Adding the current potential gives

```text
g(M+E) + (g+1+I)M + I * nonempty_now
```

and substituting

```text
nonempty_now = nonempty_next + E
```

yields

```text
g(M+E)
+ (g+1+I)M
+ I E
+ I * nonempty_next.
```

The first three terms satisfy

```text
g(M+E) + (g+1+I)M + I E
<= (2g+1+I)(M+E)
<= (2g+1+I)R.
```

Therefore the iteration transitions exactly into the next state's
`I * nonemptyCount` potential.

### Why this creates the desired `-Ip`

At loop entry every original pivot group is nonempty, so the strengthened
entry fact should be

```text
nonemptyCount (initState ...) = p
```

rather than the current one-sided `<= p`.

The refined loop theorem then gives

```text
loop_cost + I p
<= cheap_meeting_charge + I * final_nonempty.
```

For a full call:

```text
final_nonempty <= ownGroupsOf.
```

The refined home-colour bound gives

```text
mkOf + ownGroupsOf <= p + |Cr| + |Be|.
```

Since the child charge contributes `I * mkOf`, the three inequalities combine
without natural-number subtraction:

```text
loop_cost + I p
<= cheap + I * mkOf + I * ownGroupsOf
<= cheap + I p + I(|Cr| + |Be|).
```

Cancel `I p` on both sides to obtain

```text
loop_cost <= cheap + I(|Cr| + |Be|).
```

This is the exact formal shape needed to remove the expensive once-per-group
term while leaving the safe `O(g p)=O(kp)` work untouched.

## 7. Immediate Lean implementation order

1. Compile `card_nonempty_next_eq`.
2. Compile `emptied_sub_meeting`.
3. Compile `marked_emptied_card_le_meeting`.
4. Add `iterCost_le_with_empty_credit`.
5. Prove the strengthened entry equality
   `nonemptyCount (initState ...) = p` from `FPContract.groups`.
6. Clone `loopC_cost` into `loopC_cost_refined` and change only the
   potential algebra.
7. Only after this compiles, introduce `ownGroupsOf` in `CrBe.lean`.

No shortest-path correctness lemma needs to change in steps 1--6.
