/-!
# Root-record refined credit budgets

This file packages the already-compiled full-call credit theorem and the
upstream partial-call theorem into one record-level budget shape.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- Refined budget used only for FULL recursive records. -/
noncomputable def budFullCreditCandidate
    (k hins hext ad bd I nw initI : ℕ)
    (r : CallRec G s (FPData G s))
    (cs : ℕ) : ℕ :=
  scanC * delCard r
    + fpA k hins hext * (tvLen r + k * r.Q.card)
    + 3 * r.S.card
    + (nw + r.S.card + r.p * (2 + initI))
    + (1 + cs + (1 + I) * r.J.card
        + I * ownGroupsCredit k r)
    + r.cMerge
    + (1 + r.S.card + r.W.card + r.W'.card
        + r.Wr.card * (1 + I)
        + (ad * r.W'.card + bd)
        + r.S.card)

/-- Case-split record budget:
- full calls use the refined credit-aware budget;
- partial calls retain upstream budOf unchanged.
-/
noncomputable def budCreditCaseCandidate
    (k hins hext ad bd I nw initI : ℕ)
    (r : CallRec G s (FPData G s))
    (cs : ℕ) : ℕ :=
  if r.B' = r.B then
    budFullCreditCandidate k hins hext ad bd I nw initI r cs
  else
    budOf k hins hext ad bd I nw r cs

variable {DC : DCost} {out : Fin G.n → List (Fin G.m)}
variable {k hins hext : ℕ}

/-- FULL root record fits the refined case budget with I*p credit. -/
theorem callC_full_root_credit_budget_candidate
    (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hsimp : ∀ u, ((out u).map G.dst).Nodup)
    (hk : 2 ≤ k)
    {τ : ℕ → ℕ}
    {sub : SubRelC G s (Finset (Fin G.m)) (FPData G s)}
    {l : ℕ}
    (hsub : GoodSub G s τ (DelInv G s) l sub)
    {Blow B : WLab G s} {S : Finset (Fin G.n)}
    {d0 : Labels G s} {φ0 φ2 : Finset (Fin G.m)}
    {τl : ℕ} {res : Result G s}
    {lg : Log G s (FPData G s)}
    (hpre : CallPre B S d0)
    (hI : DelInv G s φ0)
    (hlow : ∀ x ∈ S, Blow ≤ dis (s := s) x)
    (hrel : CallC G s (fpC G s out k hins hext) DC sub
      (l + 1) Blow B S d0 φ0 τl res φ2 lg)
    (hfull : res.1 = B)
    {ap bp ad bd I nw initI : ℕ}
    (hpull : ∀ x, DC.pull (l + 1) x ≤ ap * x + bp)
    (hdel : ∀ x, DC.del (l + 1) x ≤ ad * x + bd)
    (hinsI : DC.ins (l + 1) ≤ I)
    (hMτ : DC.M (l + 1) ≤ τ l)
    (hgMτ : 3 * k * DC.M (l + 1) ≤ τ l)
    (hinit : ∀ (p : ℕ) (P : Fin p → Finset (Fin G.n)),
      initCost DC (l + 1) p P ≤
        nw + (∑ j, (P j).card) + p * (2 + initI)) :
    ∃ (r : CallRec G s (FPData G s))
      (lgc : Log G s (FPData G s)),
      lg = ([], r) :: lgc ∧
      r.B' = r.B ∧
      r.cost + fullPivotCredit I r ≤
        budCreditCaseCandidate
          k hins hext ad bd I nw initI r
          (childSum
            (chgOf k (1 + bp + bd) (ap + ad + 4)
              (2 * (3 * k) + 1 + I) r) lgc) := by
  classical
  obtain ⟨r, lgc, ω, p, P, W', hlg, hω, hp, hrfull, hW,
    hPsub, hpin, hcost⟩ :=
    callC_cost_full_credit_given_init_candidate
      hout hsort hsimp hk hsub hpre hI hlow hrel hfull
      hpull hdel hinsI hMτ hgMτ hinit

  have hchg :=
    childSum_pinned_eq_chgOf_candidate
      (k := k)
      (C0 := 1 + bp + bd)
      (C1 := ap + ad + 4)
      (C2 := 2 * (3 * k) + 1 + I)
      (r := r) (lgc := lgc) hω hpin

  have hown :=
    terminalOwnGroups_eq_ownGroupsCredit_candidate
      (k := k) (r := r) hω hW hpin

  have htv :
      tvLen r = (ω.trees.flatMap (fun T => T.ord)).length := by
    unfold tvLen
    rw [hω]

  have hdl :
      delCard r = (ω.Dout \ ω.Din).card := by
    unfold delCard
    rw [hω]

  refine ⟨r, lgc, hlg, hrfull, ?_⟩
  simp only [fullPivotCredit, budCreditCaseCandidate, hrfull,
    if_pos]
  unfold budFullCreditCandidate
  rw [hp, htv, hdl, ← hchg, ← hown]
  exact hcost

/-- PARTIAL root record fits the old upstream budget and receives no credit. -/
theorem callC_partial_root_credit_budget_candidate
    (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hsimp : ∀ u, ((out u).map G.dst).Nodup)
    (hk : 2 ≤ k)
    {τ : ℕ → ℕ}
    {sub : SubRelC G s (Finset (Fin G.m)) (FPData G s)}
    {l : ℕ}
    (hsub : GoodSub G s τ (DelInv G s) l sub)
    {Blow B : WLab G s} {S : Finset (Fin G.n)}
    {d0 : Labels G s} {φ0 φ2 : Finset (Fin G.m)}
    {τl : ℕ} {res : Result G s}
    {lg : Log G s (FPData G s)}
    (hpre : CallPre B S d0)
    (hI : DelInv G s φ0)
    (hlow : ∀ x ∈ S, Blow ≤ dis (s := s) x)
    (hrel : CallC G s (fpC G s out k hins hext) DC sub
      (l + 1) Blow B S d0 φ0 τl res φ2 lg)
    (hpartial : res.1 ≠ B)
    {ap bp ad bd I nw initI : ℕ}
    (hpull : ∀ x, DC.pull (l + 1) x ≤ ap * x + bp)
    (hdel : ∀ x, DC.del (l + 1) x ≤ ad * x + bd)
    (hinsI : DC.ins (l + 1) ≤ I)
    (hnew : DC.new (l + 1) ≤ nw)
    (hMτ : DC.M (l + 1) ≤ τ l)
    (hgMτ : 3 * k * DC.M (l + 1) ≤ τ l) :
    ∃ (r : CallRec G s (FPData G s))
      (lgc : Log G s (FPData G s)),
      lg = ([], r) :: lgc ∧
      r.B' ≠ r.B ∧
      r.cost + fullPivotCredit I r ≤
        budCreditCaseCandidate
          k hins hext ad bd I nw initI r
          (childSum
            (chgOf k (1 + bp + bd) (ap + ad + 4)
              (2 * (3 * k) + 1 + I) r) lgc) := by
  classical

  obtain ⟨r, lgc, ω, p, P, T6, hlg, hω, hp, hPsub, hpin,
    hPdisj, hT6S, hT6e, hcost⟩ :=
    callC_cost hout hsort hsimp hk hsub hpre hI hlow hrel
      hpull hdel hinsI hnew hMτ hgMτ

  obtain ⟨d1, p2, P2, Q2, W2, φ1, ω2, cfp, piv, σ, lgc2, J,
    cm, cl, L, B'f, T62, W', hfprel, hpiv, hloop, hB'e, hB'n,
    hT62, hW', hL, hres, hlg2⟩ := hrel

  rw [hlg] at hlg2
  have hrEq :
      r =
        { lvl := l + 1, Blow := Blow, B := B, S := S, B' := B'f,
          U := σ.U ∪ W', base := false, p := p2, Q := Q2, W := W2,
          W' := W', J := J, Wr := L.toFinset,
          fp := some ω2, cFP := cfp, cMerge := cm,
          cost := cfp + initCost DC (l + 1) p2 P2 + cl + cm
            + finCost DC (l + 1) p2 P2 S W2 T62 W' L.length } := by
    exact (Prod.mk.inj (List.cons.inj hlg2).1).2

  have hBfpart : B'f ≠ B := by
    intro hB
    apply hpartial
    rw [hres]
    exact hB

  have hrpart : r.B' ≠ r.B := by
    rw [hrEq]
    exact hBfpart

  have hchg :=
    childSum_pinned_eq_chgOf_candidate
      (k := k)
      (C0 := 1 + bp + bd)
      (C1 := ap + ad + 4)
      (C2 := 2 * (3 * k) + 1 + I)
      (r := r) (lgc := lgc) hω hpin

  have htv :
      tvLen r = (ω.trees.flatMap (fun T => T.ord)).length := by
    unfold tvLen
    rw [hω]

  have hdl :
      delCard r = (ω.Dout \ ω.Din).card := by
    unfold delCard
    rw [hω]

  have hT6 :
      T6.card * I ≤
        (if r.B' = r.B then 0 else r.S.card) * I := by
    rw [if_neg hrpart]
    exact Nat.mul_le_mul_right I (Finset.card_le_card hT6S)

  refine ⟨r, lgc, hlg, hrpart, ?_⟩
  unfold fullPivotCredit budCreditCaseCandidate
  rw [if_neg hrpart, if_neg hrpart]
  simp only [Nat.zero_add]
  unfold budOf
  rw [htv, hdl, hp, ← hchg]
  exact le_trans hcost (by
    omega)

end BM
end CHD
end Frontier
