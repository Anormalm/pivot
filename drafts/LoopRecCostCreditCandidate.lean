/-!
# Candidate credit-carrying loop-log transport

Status: UNCOMPILED candidate for Frontier/CHD/CostLog.lean.
Requires RecCostCreditCandidate.lean.

This is intended to be a structural copy of upstream loopC_reccost.
The record-local credit is never inspected; it is merely preserved when
child logs are shifted and appended.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n} {Ω : Type}

section LoopRecCredit

variable {Φ : Type} {DC : DCost}
variable {B : WLab G s} {S : Finset (Fin G.n)}
variable {d0 d1 : Labels G s} {p : ℕ}
variable {P0 : Fin p → Finset (Fin G.n)}
variable {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- Credit-carrying analogue of upstream loopC_reccost.

The proof is deliberately identical in shape to the upstream theorem.
-/
theorem loopC_reccost_credit_candidate
    (hpre : CallPre B S d0)
    (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Φ → Prop}
    {sub : SubRelC G s Φ Ω} {l : ℕ}
    (hsub : GoodSub G s τ Inv l sub)
    {credit : CallRec G s Ω → ℕ}
    {chg : CallRec G s Ω → CallRec G s Ω → ℕ}
    {bud : CallRec G s Ω → ℕ → ℕ}
    (hsubc : SubCostCredit credit chg bud sub Inv)
    {τl : ℕ} :
    ∀ i (σ : LState G s p) φ σ' φ' lg J cm c,
      LoopC G s DC sub (l + 1) B τl i σ φ σ' φ' lg J cm c →
      LInv G s B S d0 d1 P0 B'0 σ →
      Inv φ →
      RecCostCredit credit chg bud lg ∧
        ∀ q r, (q, r) ∈ lg →
          ∃ j q', q = j :: q' ∧ i ≤ j := by
  intro i σ φ σ' φ' lg J cm c hloop
  induction hloop with
  | stop i σ φ hstop =>
      intro _ _
      exact ⟨RecCostCredit.nil credit chg bud,
        fun q r h => absurd h List.not_mem_nil⟩

  | step i σ σ' φ φ1 φ' S0 Bi D1 B'i Ui Di dsub L' piv'
      lg lg' J' cm c _ hne hpull' _ _ hsubrel
      hnd hmem hres _ ih =>
      intro h hI

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
        exact lt_of_le_of_lt
          (hB.trans (h.walk.sound x0)) hlt

      obtain ⟨hpost, hI1, hlog⟩ :=
        hsub σ.B' Bi (expand σ S0 Bi) σ.d φ
          (B'i, Ui, Di, dsub) φ1 lg
          hsp hI hlowdis hBlt.le hsubrel

      have hrc :=
        hsubc σ.B' Bi (expand σ S0 Bi) σ.d φ
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
          have hc :
              dsub (G.src e) = dis (s := s) (G.src e) :=
            hpost.U_complete _ hu
          rw [hc] at h1 h2
          exact ⟨hu, h1, h2⟩
        · rintro ⟨hu, h1, h2⟩
          have hc :
              dsub (G.src e) = dis (s := s) (G.src e) :=
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

      have hnext :=
        step_post hpre hfp h hne hpull' hpost hL hres'
      rw [hfold] at hnext

      obtain ⟨hrc', hsh'⟩ := ih hnext hI1

      have hsh'' :
          ∀ q r, (q, r) ∈ lg' →
            ∃ j q', q = j :: q' ∧ j ≠ i := by
        intro q r hqr
        obtain ⟨j, q', hq, hj⟩ := hsh' q r hqr
        exact ⟨j, q', hq, by omega⟩

      refine ⟨fun q r hqr hb => ?_,
        fun q r hqr => ?_⟩

      · rcases List.mem_append.mp hqr with h1 | h2
        · exact
            RecCostCredit.shift hrc i lg' hsh''
              q r h1 hb
        · obtain ⟨j, q', hq, hj⟩ := hsh' q r h2
          subst hq
          have h0 :
              childSumAt (chg r) (j :: q') (lg.shift i) = 0 := by
            apply childSumAt_of_shape
            intro q'' r'' h''
            obtain ⟨q3, rfl, -⟩ := mem_shift.mp h''
            exact ⟨i, q3, rfl, by omega⟩
          rw [childSumAt_append, h0, Nat.zero_add]
          exact hrc' _ r h2 hb

      · rcases List.mem_append.mp hqr with h1 | h2
        · obtain ⟨q', rfl, -⟩ := mem_shift.mp h1
          exact ⟨i, q', rfl, le_rfl⟩
        · obtain ⟨j, q', hq, hj⟩ := hsh' q r h2
          exact ⟨j, q', hq, by omega⟩

end LoopRecCredit

end BM
end CHD
end Frontier
