/-!
# Candidate LoopCost finite-set lemmas for C-HD re-selection refinement

Status: UNCOMPILED source-aligned draft.
Upstream target:
  formal/lean/Frontier/CHD/LoopCost.lean
Snapshot audited:
  98c53accb47a505482a1781597ae14bf67e81cec

These lemmas isolate the purely finite-set part of the proposed
full-call BM.23 accounting refinement. They are intentionally kept
separate from the upstream tree/range machinery.

The target is to replace the one-sided emptying potential with an exact
identity and then charge actual marked groups plus emptied groups to
original groups meeting the child return set.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

section CandidateGroups

variable {p : ℕ} (σ : LState G s p) (P0 : Fin p → Finset (Fin G.n))

/-- Exact form of upstream `card_nonempty_next`.

The two sets
  {j | (P_j \ U_i).Nonempty}
and
  emptiedGroups σ U_i
partition the currently nonempty groups.
-/
theorem card_nonempty_next_eq_candidate (Ui : Finset (Fin G.n)) :
    (Finset.univ.filter (fun j => (σ.P j \ Ui).Nonempty)).card
      + (emptiedGroups σ Ui).card
    =
    (Finset.univ.filter (fun j => (σ.P j).Nonempty)).card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_congr
    refine ⟨fun j hj => j, ?_, ?_, ?_⟩
    · intro j hj
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and, emptiedGroups] at hj ⊢
      rcases hj with hres | hemp
      · obtain ⟨x, hx⟩ := hres
        exact ⟨x, (Finset.mem_sdiff.mp hx).1⟩
      · exact hemp.1
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union, emptiedGroups] at hj ⊢
      by_cases hres : (σ.P j \ Ui).Nonempty
      · exact Or.inl hres
      · right
        refine ⟨hj, fun x hx => ?_⟩
        by_contra hxU
        exact hres ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxU⟩⟩
    · intro a _ b _ h
      exact h
  · rw [Finset.disjoint_left]
    intro j hres hemp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      emptiedGroups] at hres hemp
    obtain ⟨x, hx⟩ := hres
    exact (Finset.mem_sdiff.mp hx).2 (hemp.2 (Finset.mem_sdiff.mp hx).1)

/-- Every group emptied by child U_i also meets U_i through the
original group P0_j. -/
theorem emptied_sub_meeting_candidate
    (hsub : ∀ j, σ.P j ⊆ P0 j) (Ui : Finset (Fin G.n)) :
    emptiedGroups σ Ui
      ⊆ Finset.univ.filter (fun j => (P0 j ∩ Ui).Nonempty) := by
  classical
  intro j hj
  simp only [emptiedGroups, Finset.mem_filter, Finset.mem_univ,
    true_and] at hj ⊢
  obtain ⟨hne, hUi⟩ := hj
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, Finset.mem_inter.mpr ⟨hsub j hx, hUi hx⟩⟩

/-- Actual BM.23-marked groups and groups emptied by the child are
pairwise disjoint. -/
theorem marked_disjoint_emptied_candidate (Ui : Finset (Fin G.n)) :
    Disjoint (markedGroups σ Ui) (emptiedGroups σ Ui) := by
  classical
  rw [Finset.disjoint_left]
  intro j hmk hemp
  simp only [markedGroups, emptiedGroups, Finset.mem_filter,
    Finset.mem_univ, true_and] at hmk hemp
  obtain ⟨_, hres⟩ := hmk
  obtain ⟨_, hsubUi⟩ := hemp
  obtain ⟨x, hx⟩ := hres
  exact (Finset.mem_sdiff.mp hx).2 (hsubUi (Finset.mem_sdiff.mp hx).1)

/-- The one-step event bound needed for the loop telescope:
marked + emptied is bounded by the number of original groups meeting
the child return set. -/
theorem marked_emptied_card_le_meeting_candidate
    (hsub : ∀ j, σ.P j ⊆ P0 j)
    (hpiv : ∀ j, (σ.P j).Nonempty → σ.piv j ∈ σ.P j)
    (Ui : Finset (Fin G.n)) :
    (markedGroups σ Ui).card + (emptiedGroups σ Ui).card
      ≤
    (Finset.univ.filter (fun j => (P0 j ∩ Ui).Nonempty)).card := by
  classical
  rw [← Finset.card_union_of_disjoint
    (marked_disjoint_emptied_candidate (σ := σ) Ui)]
  refine Finset.card_le_card ?_
  intro j hj
  rw [Finset.mem_union] at hj
  rcases hj with hmk | hemp
  · exact marked_sub_meeting σ P0 hsub hpiv Ui hmk
  · exact emptied_sub_meeting_candidate σ P0 hsub Ui hemp

end CandidateGroups

end BM
end CHD
end Frontier
