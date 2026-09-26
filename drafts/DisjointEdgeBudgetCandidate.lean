/-!
# Disjoint component edge budget

If final dormant/successful components own pairwise-disjoint vertex sets, then
their outgoing edge sets are pairwise disjoint by tail.  Consequently the sum
of their outgoing-edge counts is at most the graph edge count m.

This is the global combinatorial bridge needed by geometric component repair:
an O(log k) rescan factor per final component becomes O(m log k) globally.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- Pairwise-disjoint vertex components have pairwise-disjoint outgoing edge
sets. -/
theorem eout_pairwise_of_vertex_pairwise_candidate
    {Cs : List (Finset (Fin G.n))}
    (hdisj : Cs.Pairwise (fun A B => Disjoint A B)) :
    Cs.Pairwise
      (fun A B => Disjoint (BM.Eout G A) (BM.Eout G B)) := by
  refine hdisj.imp_of_mem ?_
  intro A B hA hB hAB
  rw [Finset.disjoint_left]
  intro e heA heB
  have hsA : G.src e ∈ A := by
    simpa [BM.Eout] using heA
  have hsB : G.src e ∈ B := by
    simpa [BM.Eout] using heB
  exact Finset.disjoint_left.mp hAB hsA hsB

/-- The total number of outgoing edges owned by pairwise-disjoint components
is at most the total number m of graph edges. -/
theorem sum_eout_disjoint_le_m_candidate
    (Cs : List (Finset (Fin G.n)))
    (hdisj : Cs.Pairwise (fun A B => Disjoint A B)) :
    (Cs.map (fun U => (BM.Eout G U).card)).sum ≤ G.m := by
  classical
  have hedisj :=
    eout_pairwise_of_vertex_pairwise_candidate
      (G := G) (s := s) hdisj
  rw [← card_foldr_union Cs (BM.Eout G) hedisj]
  calc
    (Cs.foldr (fun U acc => BM.Eout G U ∪ acc) ∅).card
        ≤ (Finset.univ : Finset (Fin G.m)).card :=
      Finset.card_le_card (by
        intro e he
        exact Finset.mem_univ e)
    _ = G.m := by simp

end CHD
end Frontier
