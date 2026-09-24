/-!
# All-level credit-aware BMSSP cost facts

This is the refined analogue of upstream CostLog.bmsspC_reccost.
It is parameterized by a fresh BM.6 initialization bound; once the DCost
interface exposes that bound, it can be instantiated directly.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}
variable {DC : DCost} {out : Fin G.n → List (Fin G.m)}
variable {k hins hext : ℕ}

theorem bmsspC_reccost_credit_case_candidate
    (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hsimp : ∀ u, ((out u).map G.dst).Nodup)
    (hk : 2 ≤ k)
    (τ : ℕ → ℕ)
    {ap bp ad bd I nw initI : ℕ}
    (hpull : ∀ l x, DC.pull (l + 1) x ≤ ap * x + bp)
    (hdel : ∀ l x, DC.del (l + 1) x ≤ ad * x + bd)
    (hinsI : ∀ l, DC.ins (l + 1) ≤ I)
    (hnew : ∀ l, DC.new (l + 1) ≤ nw)
    (hMτ : ∀ l, DC.M (l + 1) ≤ τ l)
    (hgMτ : ∀ l, 3 * k * DC.M (l + 1) ≤ τ l)
    (hinit : ∀ l (p : ℕ) (P : Fin p → Finset (Fin G.n)),
      initCost DC (l + 1) p P ≤
        nw + (∑ j, (P j).card) + p * (2 + initI)) :
    ∀ l,
      SubCostCredit
        (fullPivotCredit I)
        (chgOf k (1 + bp + bd) (ap + ad + 4)
          (2 * (3 * k) + 1 + I))
        (budCreditCaseCandidate
          k hins hext ad bd I nw initI)
        (BMSSPC G s (fpC G s out k hins hext) DC τ l)
        (DelInv G s) := by
  intro l
  induction l with
  | zero =>
      intro Blow B S d φ res φ' lg hpre hInv hlow hBB hrel
      obtain ⟨st, c, hloop, hU, hD, hd, hemp, hne, hphi, rfl⟩ := hrel
      intro q r hqr hb
      rcases List.mem_singleton.mp hqr with heq
      obtain ⟨-, rfl⟩ := Prod.mk.inj heq
      simp at hb

  | succ l ih =>
      intro Blow B S d φ res φ' lg hpre hInv hlow hBB hrel
      exact
        callC_reccost_credit_case_candidate
          hout hsort hsimp hk
          (bmsspC_log
            (fpC_sound hout hsort hsimp hk) τ l)
          ih
          hpre hInv hlow hrel
          (hpull l) (hdel l) (hinsI l) (hnew l)
          (hMτ l) (hgMτ l) (hinit l)

end BM
end CHD
end Frontier
