/-!
# Credit-aware recursive-call cost theorem

This is the record/log integration analogue of upstream CostLog.callC_reccost.
It uses:
- the compiled loop credit transport for descendants;
- the full/partial root budget bridges;
- a fresh BM.6 initialization bound only for the current full root.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}
variable {DC : DCost} {out : Fin G.n → List (Fin G.m)}
variable {k hins hext : ℕ}

theorem callC_reccost_credit_case_candidate
    (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hsimp : ∀ u, ((out u).map G.dst).Nodup)
    (hk : 2 ≤ k)
    {τ : ℕ → ℕ}
    {sub : SubRelC G s (Finset (Fin G.m)) (FPData G s)}
    {l : ℕ}
    (hsub : GoodSub G s τ (DelInv G s) l sub)
    {ap bp ad bd I nw initI : ℕ}
    (hsubc :
      SubCostCredit
        (fullPivotCredit I)
        (chgOf k (1 + bp + bd) (ap + ad + 4)
          (2 * (3 * k) + 1 + I))
        (budCreditCaseCandidate
          k hins hext ad bd I nw initI)
        sub (DelInv G s))
    {Blow B : WLab G s} {S : Finset (Fin G.n)}
    {d0 : Labels G s} {φ0 φ2 : Finset (Fin G.m)}
    {τl : ℕ} {res : Result G s}
    {lg : Log G s (FPData G s)}
    (hpre : CallPre B S d0)
    (hI : DelInv G s φ0)
    (hlow : ∀ x ∈ S, Blow ≤ dis (s := s) x)
    (hrel : CallC G s (fpC G s out k hins hext) DC sub
      (l + 1) Blow B S d0 φ0 τl res φ2 lg)
    (hpull : ∀ x, DC.pull (l + 1) x ≤ ap * x + bp)
    (hdel : ∀ x, DC.del (l + 1) x ≤ ad * x + bd)
    (hinsI : DC.ins (l + 1) ≤ I)
    (hnew : DC.new (l + 1) ≤ nw)
    (hMτ : DC.M (l + 1) ≤ τ l)
    (hgMτ : 3 * k * DC.M (l + 1) ≤ τ l)
    (hinit : ∀ (p : ℕ) (P : Fin p → Finset (Fin G.n)),
      initCost DC (l + 1) p P ≤
        nw + (∑ j, (P j).card) + p * (2 + initI)) :
    RecCostCredit
      (fullPivotCredit I)
      (chgOf k (1 + bp + bd) (ap + ad + 4)
        (2 * (3 * k) + 1 + I))
      (budCreditCaseCandidate
        k hins hext ad bd I nw initI)
      lg := by
  classical

  -- Keep the original derivation available for the root-budget theorem;
  -- destructuring a dependent CallC witness may clear the source hypothesis.
  have hrelRoot := hrel

  -- Expose the actual loop tail so its recursive records can be handled by
  -- the already-compiled structural credit transport.
  obtain ⟨d1, p0, P0, Q0, W0, φ1, ω0, cfp, piv, σ, lgc0, J,
    cm, cl, L, B'f, T6, W', hfprel, hpiv, hloop, hB'e, hB'n,
    hT6, hW', hL, hres, hlg0⟩ := hrel

  have hlow' : ∀ x ∈ S, Blow ≤ d0 x :=
    fun x hx => (hlow x hx).trans (hpre.walk.sound x)

  obtain ⟨hfp, hI1⟩ :=
    fpC_sound hout hsort hsimp hk
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hI hlow' hfprel

  have h0 := linv_init hpre hfp hpiv

  obtain ⟨hrcTail, -⟩ :=
    loopC_reccost_credit_candidate
      (DC := DC)
      hpre hfp hsub hsubc
      0 (initState B d1 P0 piv) φ1 σ φ2 lgc0 J cm cl
      hloop h0 hI1

  -- Root record: full calls use the refined credit budget; partial calls use
  -- the unchanged upstream budget with zero credit.
  by_cases hfull : res.1 = B

  · obtain ⟨r, lgc, hlg, hrfull, hroot⟩ :=
      callC_full_root_credit_budget_candidate
        hout hsort hsimp hk hsub hpre hI hlow hrelRoot hfull
        hpull hdel hinsI hMτ hgMτ hinit

    rw [hlg] at hlg0
    have htail : lgc = lgc0 := (List.cons.inj hlg0).2
    rw [← htail] at hrcTail

    have hhead :
        ∀ (f : CallRec G s (FPData G s) → ℕ) (q : List ℕ),
          childSumAt f q (([], r) :: lgc) =
            childSumAt f q lgc := by
      intro f q
      unfold childSumAt
      rw [List.filter_cons_of_neg (by simp)]

    rw [hlg]
    intro q r' hqr hb
    rcases List.mem_cons.mp hqr with heq | hmem
    · obtain ⟨hq, hr⟩ := Prod.mk.inj heq
      subst q
      subst r'
      rw [hhead, childSumAt_nil]
      exact hroot
    · rw [hhead]
      exact hrcTail q r' hmem hb

  · obtain ⟨r, lgc, hlg, hrpart, hroot⟩ :=
      callC_partial_root_credit_budget_candidate
        hout hsort hsimp hk hsub hpre hI hlow hrelRoot hfull
        hpull hdel hinsI hnew hMτ hgMτ

    rw [hlg] at hlg0
    have htail : lgc = lgc0 := (List.cons.inj hlg0).2
    rw [← htail] at hrcTail

    have hhead :
        ∀ (f : CallRec G s (FPData G s) → ℕ) (q : List ℕ),
          childSumAt f q (([], r) :: lgc) =
            childSumAt f q lgc := by
      intro f q
      unfold childSumAt
      rw [List.filter_cons_of_neg (by simp)]

    rw [hlg]
    intro q r' hqr hb
    rcases List.mem_cons.mp hqr with heq | hmem
    · obtain ⟨hq, hr⟩ := Prod.mk.inj heq
      subst q
      subst r'
      rw [hhead, childSumAt_nil]
      exact hroot
    · rw [hhead]
      exact hrcTail q r' hmem hb

end BM
end CHD
end Frontier
