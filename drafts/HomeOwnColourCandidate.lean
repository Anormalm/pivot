/-!
# Candidate generic own-home colour lemma

Status: source-aligned candidate under CI.
Natural upstream target:
  formal/lean/Frontier/Homes.lean

This lemma strengthens `card_children_meeting_le` by one when the set P
contains a vertex whose home is `none`.
-/

namespace Frontier.Density.Ranges

open Frontier.CostCharging

variable {ι V α : Type*}
variable [LinearOrder α]
variable {F : CallForest ι V α}
variable (R : Ranges F) (val : V → α)

/-- If P contains a vertex with home `none`, then the direct children
meeting P plus that extra own-home colour fit inside the distinct home
colours represented by P.

This is the per-group inequality needed for the refined C-HD
`mkOf + ownGroupsOf` charge.
-/
theorem card_children_meeting_add_one_le_of_none_candidate
    [Fintype ι] [DecidableEq ι] [DecidableEq V]
    (X : ι) (P : Finset V)
    (hnone : ∃ v ∈ P, R.home val X v = none) :
    (Finset.univ.filter
        (fun Y => F.parent Y = some X ∧ (P ∩ F.U Y).Nonempty)).card + 1
      ≤
    (P.image (R.home val X)).card := by
  classical
  let C : Finset ι :=
    Finset.univ.filter
      (fun Y => F.parent Y = some X ∧ (P ∩ F.U Y).Nonempty)
  let H : Finset (Option ι) := P.image (R.home val X)

  obtain ⟨v0, hv0P, hv0none⟩ := hnone
  have hnoneMem : (none : Option ι) ∈ H := by
    exact Finset.mem_image.mpr ⟨v0, hv0P, hv0none⟩

  have hchildren :
      C.card ≤ (H.erase (none : Option ι)).card := by
    refine Finset.card_le_card_of_injOn
      (fun Y : ι => (some Y : Option ι)) ?_ ?_
    · intro Y hY
      have hYC : Y ∈ C := hY
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hYC
      obtain ⟨hpar, v, hv⟩ := hYC
      obtain ⟨hvP, hvU⟩ := Finset.mem_inter.mp hv
      change (some Y : Option ι) ∈ H.erase none
      rw [Finset.mem_erase]
      refine ⟨by simp, ?_⟩
      exact Finset.mem_image.mpr
        ⟨v, hvP, home_of_mem hpar hvU⟩
    · intro Y1 _ Y2 _ heq
      exact Option.some.inj heq

  have hcard :
      (H.erase (none : Option ι)).card + 1 = H.card :=
    Finset.card_erase_add_one hnoneMem

  change C.card + 1 ≤ H.card
  rw [← hcard]
  exact Nat.add_le_add_right hchildren 1

end Frontier.Density.Ranges
