/-!
# W' ownership provenance for traced BMSSP calls

Every vertex in a record's final W' set is returned by that record and by
no direct child record.  This is the vertex-level version of the ownership
argument upstream already uses for sources of W' relaxation edges.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- Path-level ownership of every W' vertex in a log. -/
def WPrimeOwnC (lg : Log G s (FPData G s)) : Prop :=
  ∀ q r, (q, r) ∈ lg →
    ∀ v ∈ r.W',
      v ∈ r.U ∧
      ∀ a r', (q ++ [a], r') ∈ lg → v ∉ r'.U

/-- Sub-call form of WPrimeOwnC. -/
def SubWPrimeOwnC
    (sub : SubRelC G s (Finset (Fin G.m)) (FPData G s)) : Prop :=
  ∀ Blow B S d φ res φ' lg,
    CallPre B S d →
    DelInv G s φ →
    (∀ x ∈ S, Blow ≤ dis (s := s) x) →
    Blow ≤ B →
    sub Blow B S d φ res φ' lg →
    WPrimeOwnC lg

section Loop

variable {DC : DCost}
variable {B : WLab G s} {S : Finset (Fin G.n)}
variable {d0 d1 : Labels G s} {p : ℕ}
variable {P0 : Fin p → Finset (Fin G.n)}
variable {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- The loop preserves W' ownership of all sub-call records. -/
theorem loopC_wprime_own_candidate
    (hpre : CallPre B S d0)
    (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ}
    {sub : SubRelC G s (Finset (Fin G.m)) (FPData G s)}
    {l : ℕ}
    (hsub : GoodSub G s τ (DelInv G s) l sub)
    (hsubW : SubWPrimeOwnC sub)
    {τl : ℕ} :
    ∀ i (σ : LState G s p) φ σ' φ' lg J cm c,
      LoopC G s DC sub (l + 1) B τl i σ φ σ' φ' lg J cm c →
      LInv G s B S d0 d1 P0 B'0 σ →
      DelInv G s φ →
      WPrimeOwnC lg := by
  classical
  intro i σ φ σ' φ' lg J cm c hloop
  induction hloop with
  | stop i σ φ hstop =>
      intro _ _ q r hqr
      exact absurd hqr List.not_mem_nil

  | step i σ σ' φ φ1 φ' S0 Bi D1 B'i Ui Di dsub L' piv'
      lg lg' J' cm c _ hne hpull' _ _ hsubrel
      hnd hmem hres hrest ih =>
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
        exact lt_of_le_of_lt (hB.trans (h.walk.sound x0)) hlt

      obtain ⟨hpost, hI1, hlog⟩ :=
        hsub σ.B' Bi (expand σ S0 Bi) σ.d φ
          (B'i, Ui, Di, dsub) φ1 lg
          hsp hI hlowdis hBlt.le hsubrel

      have hcurOwn :
          WPrimeOwnC lg :=
        hsubW σ.B' Bi (expand σ S0 Bi) σ.d φ
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

      have htailOwn := ih hnext hI1

      obtain ⟨-, -, -, hll⟩ :=
        loopC_log hpre hfp hsub
          _ _ _ _ _ _ _ _ _ hrest hnext hI1

      intro q r hqr v hv
      rcases List.mem_append.mp hqr with hcur | htail

      · obtain ⟨q0, hq, hqmem⟩ := mem_shift.mp hcur
        subst q
        have hc := hcurOwn q0 r hqmem v hv
        refine ⟨hc.1, ?_⟩
        intro a r' hchild
        rcases List.mem_append.mp hchild with hchildCur | hchildTail
        · obtain ⟨qc, hqc, hqcmem⟩ := mem_shift.mp hchildCur
          have heq : qc = q0 ++ [a] := by
            exact (List.cons.inj hqc).2.symm
          subst qc
          exact hc.2 a r' hqcmem
        · obtain ⟨j, qj, hqj, hj⟩ :=
            hll.shape _ _ hchildTail
          have hfirst : i = j := by
            exact (List.cons.inj hqj).1
          omega

      · have ht := htailOwn q r htail v hv
        refine ⟨ht.1, ?_⟩
        intro a r' hchild
        rcases List.mem_append.mp hchild with hchildCur | hchildTail
        · obtain ⟨j, q0, hq, hj⟩ := hll.shape q r htail
          obtain ⟨qc, hqc, hqcmem⟩ := mem_shift.mp hchildCur
          rw [hq] at hqc
          have hfirst : j = i := by
            exact (List.cons.inj hqc).1
          omega
        · exact ht.2 a r' hchildTail

end Loop

/-- Every BMSSPC log carries W' ownership at every level. -/
theorem bmsspC_wprime_own_candidate
    {DC : DCost} {out : Fin G.n → List (Fin G.m)}
    {k hins hext : ℕ}
    (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hsimp : ∀ u, ((out u).map G.dst).Nodup)
    (hk : 2 ≤ k)
    (τ : ℕ → ℕ) :
    ∀ l,
      SubWPrimeOwnC
        (BMSSPC G s (fpC G s out k hins hext) DC τ l) := by
  intro l
  induction l with
  | zero =>
      intro Blow B S d φ res φ' lg hpre hI hlow hBB hrel
      obtain ⟨st, c, hloop, h1, h2, h3, h4, h5, h6, rfl⟩ := hrel
      intro q r hqr v hv
      rcases List.mem_singleton.mp hqr with heq
      obtain ⟨-, rfl⟩ := Prod.mk.inj heq
      simp at hv

  | succ l ih =>
      intro Blow B S d φ res φ' lg hpre hI hlow hBB hrel

      have hsub :=
        bmsspC_log
          (DC := DC)
          (fpC_sound (hins := hins) (hext := hext) hout hsort hsimp hk) τ l

      obtain ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, σ, lgc, J, cm, cl,
        L, B'f, T6, W', hfprel, hpiv, hloop, hB'e, hB'n, hT6, hW',
        hL, hres, hlg⟩ := hrel

      have hlow' : ∀ x ∈ S, Blow ≤ d x :=
        fun x hx => (hlow x hx).trans (hpre.walk.sound x)
      obtain ⟨hfp, hI1⟩ :=
        fpC_sound (hins := hins) (hext := hext) hout hsort hsimp hk
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hI hlow' hfprel
      have h0 := linv_init hpre hfp hpiv

      have hloopOwn :=
        loopC_wprime_own_candidate
          (DC := DC) hpre hfp hsub ih
          0 (initState B d1 P piv) φ1 σ φ' lgc J cm cl
          hloop h0 hI1

      obtain ⟨-, -, -, hll⟩ :=
        loopC_log hpre hfp hsub
          0 (initState B d1 P piv) φ1 σ φ' lgc J cm cl
          hloop h0 hI1

      rw [hlg]
      intro q r hqr v hv
      rcases List.mem_cons.mp hqr with hroot | hdesc

      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hroot
        refine ⟨Finset.mem_union_right _ hv, ?_⟩
        intro a r' hchild hvChild
        have hchild' := mem_cons_nonempty hchild (by simp)
        obtain ⟨hU, -, -, -, -⟩ := hll.root a r' hchild'
        have hvNot : v ∉ σ.U := (hW' v).mp hv |>.1.2
        exact hvNot (hU hvChild)

      · have hd := hloopOwn q r hdesc v hv
        refine ⟨hd.1, ?_⟩
        intro a r' hchild
        rcases List.mem_cons.mp hchild with hrootChild | htailChild
        · have hqnil : q ++ [a] = [] :=
            (Prod.mk.inj hrootChild).1
          exact absurd hqnil (List.append_ne_nil_of_right_ne_nil _ (by simp))
        · exact hd.2 a r' htailChild

end BM
end CHD
end Frontier
