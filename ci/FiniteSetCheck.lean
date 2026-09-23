import Frontier.CHD.LoopCost

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

section CandidateGroups

variable {p : ℕ} (σ : LState G s p) (P0 : Fin p → Finset (Fin G.n))

theorem card_nonempty_next_eq_candidate (Ui : Finset (Fin G.n)) :
    (Finset.univ.filter (fun j => (σ.P j \ Ui).Nonempty)).card
      + (emptiedGroups σ Ui).card
    = (Finset.univ.filter (fun j => (σ.P j).Nonempty)).card := by
  classical
  have hdisj : Disjoint
      (Finset.univ.filter (fun j => (σ.P j \ Ui).Nonempty))
      (emptiedGroups σ Ui) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, emptiedGroups] at h1 h2
    obtain ⟨x, hx⟩ := h1
    exact (Finset.mem_sdiff.mp hx).2 (h2.2 (Finset.mem_sdiff.mp hx).1)
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext j
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, emptiedGroups]
  constructor
  · rintro (hres | hemp)
    · obtain ⟨x, hx⟩ := hres
      exact ⟨x, (Finset.mem_sdiff.mp hx).1⟩
    · exact hemp.1
  · intro hne
    by_cases hres : (σ.P j \ Ui).Nonempty
    · exact Or.inl hres
    · right
      refine ⟨hne, fun x hx => ?_⟩
      by_contra hxU
      exact hres ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxU⟩⟩

theorem emptied_sub_meeting_candidate
    (hsub : ∀ j, σ.P j ⊆ P0 j) (Ui : Finset (Fin G.n)) :
    emptiedGroups σ Ui
      ⊆ Finset.univ.filter (fun j => (P0 j ∩ Ui).Nonempty) := by
  classical
  intro j hj
  simp only [emptiedGroups, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  obtain ⟨hne, hUi⟩ := hj
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, Finset.mem_inter.mpr ⟨hsub j hx, hUi hx⟩⟩

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

theorem marked_emptied_card_le_meeting_candidate
    (hsub : ∀ j, σ.P j ⊆ P0 j)
    (hpiv : ∀ j, (σ.P j).Nonempty → σ.piv j ∈ σ.P j)
    (Ui : Finset (Fin G.n)) :
    (markedGroups σ Ui).card + (emptiedGroups σ Ui).card
      ≤ (Finset.univ.filter (fun j => (P0 j ∩ Ui).Nonempty)).card := by
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
