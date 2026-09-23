/-!
# Candidate generic own-home colour lemma

Status: UNCOMPILED source-aligned draft.
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
meeting P plus that extra own-home colour fit injectively inside the distinct
home colours represented by P.

This is the exact per-group inequality needed for the refined C-HD
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

  have hsomeSub :
      C.image (fun Y => (some Y : Option ι))
        ⊆ P.image (R.home val X) := by
    intro oy hoy
    obtain ⟨Y, hYC, rfl⟩ := Finset.mem_image.mp hoy
    obtain ⟨hpar, v, hv⟩ := (Finset.mem_filter.mp hYC).2
    obtain ⟨hvP, hvU⟩ := Finset.mem_inter.mp hv
    exact Finset.mem_image.mpr
      ⟨v, hvP, home_of_mem hpar hvU⟩

  obtain ⟨v0, hv0P, hv0none⟩ := hnone
  have hnoneMem :
      (none : Option ι) ∈ P.image (R.home val X) :=
    Finset.mem_image.mpr ⟨v0, hv0P, hv0none⟩

  have hnoneNot :
      (none : Option ι) ∉ C.image (fun Y => (some Y : Option ι)) := by
    simp

  have hinjSome :
      Set.InjOn (fun Y : ι => (some Y : Option ι)) (C : Set ι) := by
    intro a _ b _ hab
    exact Option.some.inj hab

  have hcardSome :
      (C.image (fun Y => (some Y : Option ι))).card = C.card :=
    Finset.card_image_iff.mpr
      (fun a ha b hb hab => Option.some.inj hab)

  have hunionSub :
      insert (none : Option ι)
          (C.image (fun Y => (some Y : Option ι)))
        ⊆ P.image (R.home val X) := by
    intro z hz
    simp only [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact hnoneMem
    · exact hsomeSub hz

  have hcardInsert :
      (insert (none : Option ι)
          (C.image (fun Y => (some Y : Option ι)))).card
        =
      C.card + 1 := by
    rw [Finset.card_insert_of_notMem hnoneNot, hcardSome]
    omega

  have hle :=
    Finset.card_le_card hunionSub

  change C.card + 1 ≤ (P.image (R.home val X)).card
  rw [← hcardInsert]
  exact hle

end Frontier.Density.Ranges
