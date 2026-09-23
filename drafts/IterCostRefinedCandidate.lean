/-!
# Candidate refined iteration cost lemma for C-HD

Status: UNCOMPILED source-aligned draft.
Upstream target:
  formal/lean/Frontier/CHD/LoopCost.lean
Snapshot:
  98c53accb47a505482a1781597ae14bf67e81cec

This draft assumes the finite-set candidate lemmas from
`LoopCostFiniteCandidates.lean`.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

section CandidateIter

variable {p : ℕ} {σ : LState G s p}

/-- Refined one-iteration cost bound.

Compared with upstream `iterCost_le`, the expensive insertion coefficient
receives a credit `I * |emptiedGroups|` on the left.  Marked and emptied
groups are charged together to the original child/group meeting count.
-/
theorem iterCost_le_with_empty_credit_candidate
    {DC : DCost} {lv : ℕ} {S0 Ui : Finset (Fin G.n)} {nL : ℕ}
    {ap bp ad bd I g R : ℕ}
    (hpull : DC.pull lv S0.card ≤ ap * S0.card + bp)
    (hdel : DC.del lv Ui.card ≤ ad * Ui.card + bd)
    (hins : DC.ins lv ≤ I)
    (hg : ∀ j, (σ.P j).card ≤ g)
    (hS0 : S0.card ≤ Ui.card)
    (hpulled :
      ∑ j ∈ pulledGroups σ S0, (σ.P j).card
        ≤ Ui.card
          + g * ((markedGroups σ Ui).card
            + (emptiedGroups σ Ui).card))
    (hmeet :
      (markedGroups σ Ui).card + (emptiedGroups σ Ui).card ≤ R) :
    iterCost DC lv σ S0 Ui nL
        + I * (emptiedGroups σ Ui).card
      ≤
    (1 + bp + bd)
      + (ap + ad + 4) * Ui.card
      + (1 + I) * nL
      + (2 * g + 1 + I) * R := by
  classical
  unfold iterCost

  have hmarked :
      ∑ j ∈ markedGroups σ Ui,
          ((σ.P j \ Ui).card + 1 + DC.ins lv)
        ≤
      (markedGroups σ Ui).card * (g + 1 + I) := by
    calc
      ∑ j ∈ markedGroups σ Ui,
          ((σ.P j \ Ui).card + 1 + DC.ins lv)
          ≤
        ∑ j ∈ markedGroups σ Ui, (g + 1 + I) :=
          Finset.sum_le_sum (fun j _ => by
            have hsd :
                (σ.P j \ Ui).card ≤ (σ.P j).card :=
              Finset.card_le_card Finset.sdiff_subset
            have hgj := hg j
            omega)
      _ = (markedGroups σ Ui).card * (g + 1 + I) := by
          rw [Finset.sum_const, smul_eq_mul]

  have hpullS : ap * S0.card ≤ ap * Ui.card :=
    Nat.mul_le_mul_left _ hS0

  have hnL :
      nL * (1 + DC.ins lv) ≤ (1 + I) * nL := by
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_right _ (by omega)

  have hgroup :
      g * ((markedGroups σ Ui).card + (emptiedGroups σ Ui).card)
        + (g + 1 + I) * (markedGroups σ Ui).card
        + I * (emptiedGroups σ Ui).card
      ≤
      (2 * g + 1 + I) * R := by
    have hcoeff :
        g * ((markedGroups σ Ui).card + (emptiedGroups σ Ui).card)
          + (g + 1 + I) * (markedGroups σ Ui).card
          + I * (emptiedGroups σ Ui).card
        ≤
        (2 * g + 1 + I) *
          ((markedGroups σ Ui).card + (emptiedGroups σ Ui).card) := by
      omega
    exact hcoeff.trans
      (Nat.mul_le_mul_left (2 * g + 1 + I) hmeet)

  have hU :
      (ap + ad + 4) * Ui.card
        = ap * Ui.card + ad * Ui.card + 4 * Ui.card := by
    ring

  omega

end CandidateIter

section CandidateEntry

variable {B : WLab G s} {d1 : Labels G s}
variable {p : ℕ} {P : Fin p → Finset (Fin G.n)}
variable {piv : Fin p → Fin G.n}

/-- Exact loop-entry potential: every FindPivots group is nonempty, so
`nonemptyCount(initState) = p`.

This replaces the one-sided `hne0 : ... ≤ p` currently used by
`callC_cost`.
-/
theorem nonemptyCount_initState_eq_candidate
    (hne : ∀ j, (P j).Nonempty) :
    nonemptyCount (initState B d1 P piv) = p := by
  classical
  unfold nonemptyCount initState
  have hf :
      Finset.univ.filter (fun j => (P j).Nonempty)
        = (Finset.univ : Finset (Fin p)) := by
    ext j
    simp [hne j]
  rw [hf]
  simp

end CandidateEntry

end BM
end CHD
end Frontier
