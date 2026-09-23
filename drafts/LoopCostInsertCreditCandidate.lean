/-!
# Candidate I-weighted loop-cost telescope for C-HD

Status: UNCOMPILED source-aligned draft.
This file is intended to be checked after:
  LoopCostFiniteCandidates.lean
  IterCostRefinedCandidate.lean

Upstream proof template:
  Frontier.CHD.LoopCost.loopC_cost
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}
variable {Φ Ω : Type} {DC : DCost}
variable {B : WLab G s} {S : Finset (Fin G.n)}
variable {d0 d1 : Labels G s} {p : ℕ}
variable {P0 : Fin p → Finset (Fin G.n)}
variable {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- The expensive insertion-cost telescope.

Unlike upstream `loopC_cost`, whose `g * nonemptyCount` potential pays
cheap group scanning, this theorem moves the generic insertion coefficient
`I` from the initial nonempty groups to the final nonempty groups.

The child-charge interface itself is unchanged.
-/
theorem loopC_cost_insert_credit_candidate
    (hpre : CallPre B S d0)
    (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Φ → Prop}
    {sub : SubRelC G s Φ Ω} {l : ℕ}
    (hsub : GoodSub G s τ Inv l sub)
    {τl : ℕ} {ap bp ad bd I g : ℕ}
    (hpull : ∀ x, DC.pull (l + 1) x ≤ ap * x + bp)
    (hdel : ∀ x, DC.del (l + 1) x ≤ ad * x + bd)
    (hins : DC.ins (l + 1) ≤ I)
    (hP0 : ∀ j, (P0 j).card ≤ g)
    (hMτ : DC.M (l + 1) ≤ τ l)
    (hgMτ : g * DC.M (l + 1) ≤ τ l) :
    ∀ i (σ : LState G s p) φ σ' φ' lg J cm c,
      LoopC G s DC sub (l + 1) B τl i σ φ σ' φ' lg J cm c →
      LInv G s B S d0 d1 P0 B'0 σ → Inv φ →
      c + I * nonemptyCount σ
        ≤
      1
        + childSum
            (childCharge P0
              (1 + bp + bd)
              (ap + ad + 4)
              (2 * g + 1 + I)) lg
        + (1 + I) * J.card
        + I * nonemptyCount σ' := by
  classical
  intro i σ φ σ' φ' lg J cm c hloop
  induction hloop with
  | stop i σ φ hstop =>
      intro _ _
      simp [childSum_nil]
  | step i σ σ' φ φ1 φ' S0 Bi D1 B'i Ui Di dsub L' piv'
      lg lg' J' cm c _ hne hpull' hSM _ hsubrel
      hnd hmem hres hrest ih =>
    intro h hI

    -- Same sub-call facts as upstream loopC_cost.
    have hsp : CallPre Bi (expand σ S0 Bi) σ.d :=
      step_pre hpre hfp h hpull'
    have hlowdis : ∀ x ∈ expand σ S0 Bi,
        σ.B' ≤ dis (s := s) x :=
      fun x hx => (Si_facts h hpull' hx).1.2.2
    have hSne : S0.Nonempty := by
      apply hpull'.nonempty
      simp only [DS.IsEmpty, not_forall] at hne
      exact hne
    obtain ⟨x0, hx0⟩ := hSne
    have hx0S : x0 ∈ expand σ S0 Bi :=
      mem_expand.mpr (Or.inl hx0)
    have hBlt : σ.B' < Bi := by
      obtain ⟨⟨-, -, hB⟩, hlt⟩ := Si_facts h hpull' hx0S
      exact lt_of_le_of_lt (hB.trans (h.walk.sound x0)) hlt
    obtain ⟨hpost, hI1, hlog⟩ :=
      hsub σ.B' Bi (expand σ S0 Bi) σ.d φ
        (B'i, Ui, Di, dsub) φ1 lg
        hsp hI hlowdis hBlt.le hsubrel

    have hmem' : ∀ e, e ∈ L' ↔
        G.src e ∈ Ui ∧
        Bi ≤ ext (dis (s := s) (G.src e)) e ∧
        ext (dis (s := s) (G.src e)) e < B := by
      intro e
      rw [hmem e]
      constructor
      · rintro ⟨hu, h1, h2⟩
        have hc : dsub (G.src e) = dis (s := s) (G.src e) :=
          hpost.U_complete _ hu
        rw [hc] at h1 h2
        exact ⟨hu, h1, h2⟩
      · rintro ⟨hu, h1, h2⟩
        have hc : dsub (G.src e) = dis (s := s) (G.src e) :=
          hpost.U_complete _ hu
        rw [← hc] at h1 h2
        exact ⟨hu, h1, h2⟩

    obtain ⟨L, hL, hfold⟩ :=
      window_scan_step hpull'.bound hpost
        ((D1.merge Di).deleteSet Ui) hnd hmem'
    have hres' : Reselect σ Ui
        (L.foldl (relaxIns G s B (some Bi))
          (dsub, (D1.merge Di).deleteSet Ui)).1 piv' := by
      rw [hfold]
      exact hres
    have hnext := step_post hpre hfp h hne hpull' hpost hL hres'
    rw [hfold] at hnext
    have ih' := ih hnext hI1

    -- Tail-log facts, copied from upstream.
    obtain ⟨-, -, -, hll⟩ :=
      loopC_log hpre hfp hsub _ _ _ _ _ _ _ _ _ hrest hnext hI1
    obtain ⟨ri, hri, -, -, -, -, hriB', hriU⟩ := hlog.root
    have hriU' : ri.U = Ui := hriU

    -- Current group facts.
    have hsubP : ∀ j, σ.P j ⊆ P0 j := h.Psub
    have hpivP : ∀ j, (σ.P j).Nonempty → σ.piv j ∈ σ.P j :=
      fun j hj => (h.pivots j hj).1
    have hdisjP : ∀ a b, a ≠ b → Disjoint (σ.P a) (σ.P b) :=
      fun a b hab =>
        Disjoint.mono (hsubP a) (hsubP b) (hfp.gdisj a b hab)
    have hgP : ∀ j, (σ.P j).card ≤ g :=
      fun j => (Finset.card_le_card (hsubP j)).trans (hP0 j)

    -- Same full/partial-child pulled-group estimate as upstream.
    have hS0U : S0.card ≤ Ui.card ∧
        ∑ j ∈ pulledGroups σ S0, (σ.P j).card
          ≤ Ui.card
            + g * ((markedGroups σ Ui).card
              + (emptiedGroups σ Ui).card) := by
      by_cases hfull : B'i = Bi
      · have hsubU : S0 ⊆ Ui := by
          intro x hx
          have hxS : x ∈ expand σ S0 Bi :=
            mem_expand.mpr (Or.inl hx)
          obtain ⟨-, hlt⟩ := Si_facts h hpull' hxS
          have hdis : dis (s := s) x < Bi :=
            lt_of_le_of_lt (h.walk.sound x) hlt
          have hreach : G.Reachable s x := by
            have hne' : σ.d x ≠ ⊤ := ne_top_of_lt hlt
            obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hne'
            exact ⟨q, h.walk x q hq.symm⟩
          have hU : x ∈ Utilde Bi
              (expand σ S0 Bi : Set (Fin G.n)) :=
            ⟨hdis, x, hxS, onPath_self hreach⟩
          have hxU := (hpost.U_eq x).mpr (by
            rw [show (B'i, Ui, Di, dsub).1 = B'i from rfl, hfull]
            exact hU)
          exact hxU
        refine ⟨Finset.card_le_card hsubU, ?_⟩
        have hp := pulled_sum_full hgP (Ui := Ui) hsubU
        omega
      · have hlt : B'i < Bi := lt_of_le_of_ne hpost.B'_le hfull
        have hcap := hpost.partial_card hlt
        have hc' : τ l ≤ Ui.card := hcap
        refine ⟨by omega, ?_⟩
        have h1 := pulled_sum_le hgP hdisjP S0
        have h2 : g * S0.card ≤ g * DC.M (l + 1) :=
          Nat.mul_le_mul_left _ hSM
        omega

    -- The new event inequality: actual markings PLUS emptyings fit inside
    -- the original groups meeting this child.
    have hmeet :
        (markedGroups σ Ui).card + (emptiedGroups σ Ui).card
          ≤
        (Finset.univ.filter
          (fun j => (P0 j ∩ Ui).Nonempty)).card :=
      marked_emptied_card_le_meeting_candidate
        σ P0 hsubP hpivP Ui

    have hit :=
      iterCost_le_with_empty_credit_candidate
        (σ := σ) (DC := DC) (lv := l + 1)
        (S0 := S0) (Ui := Ui) (nL := L'.length)
        (hpull S0.card) (hdel Ui.card) hins hgP
        hS0U.1 hS0U.2 hmeet

    -- Exact emptying identity.
    have hpot :=
      card_nonempty_next_eq_candidate σ P0 Ui
    have hne_next :
        nonemptyCount
          (nextState B σ Bi B'i Ui D1 Di dsub L' piv')
          =
        (Finset.univ.filter
          (fun j => (σ.P j \ Ui).Nonempty)).card := by
      rfl
    have hne_now :
        nonemptyCount σ =
        (Finset.univ.filter
          (fun j => (σ.P j).Nonempty)).card := rfl

    -- Window-edge disjointness, unchanged from upstream.
    have hJdisj : Disjoint L'.toFinset J' := by
      rw [Finset.disjoint_left]
      intro e he he'
      obtain ⟨j, r, hjr, hsrc, -, -⟩ := hll.Jwin e he'
      have hsrcU : G.src e ∈ Ui :=
        ((hmem' e).mp (List.mem_toFinset.mp he)).1
      obtain ⟨-, hdisj, -, -, -⟩ := hll.root j r hjr
      have hx :
          G.src e ∈
            (nextState B σ Bi B'i Ui D1 Di dsub L' piv').U := by
        simp [nextState, hsrcU]
      exact Finset.disjoint_left.mp hdisj hsrc hx
    have hJcard :
        (L'.toFinset ∪ J').card = L'.length + J'.card := by
      rw [Finset.card_union_of_disjoint hJdisj,
        List.toFinset_card_of_nodup hnd]

    -- Child charge, unchanged.
    have hch :
        childSum
          (childCharge P0
            (1 + bp + bd)
            (ap + ad + 4)
            (2 * g + 1 + I))
          (lg.shift i ++ lg')
        =
        childCharge P0
            (1 + bp + bd)
            (ap + ad + 4)
            (2 * g + 1 + I) ri
          +
        childSum
          (childCharge P0
            (1 + bp + bd)
            (ap + ad + 4)
            (2 * g + 1 + I)) lg' := by
      rw [childSum_append,
        childSum_shift _ _ hlog.inv.nodup hri]
    have hri_charge :
        childCharge P0
            (1 + bp + bd)
            (ap + ad + 4)
            (2 * g + 1 + I) ri
        =
        (1 + bp + bd)
          + (ap + ad + 4) * Ui.card
          + (2 * g + 1 + I) *
              (Finset.univ.filter
                (fun j => (P0 j ∩ Ui).Nonempty)).card := by
      simp [childCharge, hriU']

    rw [hch, hri_charge, hJcard]
    rw [hne_next] at ih'
    rw [hne_now]

    -- Expose the exact potential drop to Presburger arithmetic.
    have hpotI :
        I * (Finset.univ.filter
          (fun j => (σ.P j).Nonempty)).card
        =
        I * (Finset.univ.filter
          (fun j => (σ.P j \ Ui).Nonempty)).card
          + I * (emptiedGroups σ Ui).card := by
      rw [← Nat.mul_add, hpot]

    omega

end BM
end CHD
end Frontier
