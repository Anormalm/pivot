/-!
# Global-min frontier step for batched FindPivots

The existing C-HD framework already contains the two facts needed by a
global multi-source FindPivots queue:

1. the minimum-label member of the current frontier is complete;
2. after relaxing all below-B outgoing edges of a complete settled set, the
   frontier is preserved.

This file packages the singleton step directly.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- One global-min extraction can be settled exactly as in Dijkstra while
preserving the frontier representation. -/
theorem global_min_frontier_step_candidate
    {d d' : Labels G s}
    {B : WLab G s}
    {S X Y : Set (Fin G.n)}
    {y : Fin G.n}
    (hF :
      IsFrontier d (Utilde B S) X Y)
    (hY : Y ⊆ Utilde B S)
    (hsound : Sound d)
    (hy : y ∈ Y)
    (hmin : ∀ y' ∈ Y, d y ≤ d y')
    (hle : ∀ v, d' v ≤ d v)
    (hsound' : Sound d')
    (hrelax :
      ∀ e : Fin G.m,
        G.src e = y →
        ext (d' y) e < B →
        d' (G.dst e) ≤ ext (d' y) e) :
    IsFrontier d' (Utilde B S)
      (X ∪ ({y} : Set (Fin G.n)))
      ((Y \ ({y} : Set (Fin G.n))) ∪
        Relaxed d' B ({y} : Set (Fin G.n))) := by
  have hyc : Complete d y :=
    IsFrontier.complete_of_min hF hY hsound hy hmin
  have hyc' : Complete d' y :=
    complete_of_le hyc (hle y) hsound'
  have hU :
      ∀ v ∈ Utilde B S, dis (s := s) v < B := by
    intro v hv
    exact hv.1
  have hZ :
      ∀ z ∈ ({y} : Set (Fin G.n)), Complete d' z := by
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact hyc'
  have hrelax' :
      ∀ e : Fin G.m,
        G.src e ∈ ({y} : Set (Fin G.n)) →
        ext (d' (G.src e)) e < B →
        d' (G.dst e) ≤ ext (d' (G.src e)) e := by
    intro e he hbelow
    simp only [Set.mem_singleton_iff] at he
    subst he
    exact hrelax e rfl hbelow
  exact IsFrontier.step hF hU hsound' hle hZ hrelax'

/-- The extracted global minimum is complete before and after the monotone
relaxation step, hence its label is stable. -/
theorem global_min_stable_candidate
    {d d' : Labels G s}
    {B : WLab G s}
    {S X Y : Set (Fin G.n)}
    {y : Fin G.n}
    (hF : IsFrontier d (Utilde B S) X Y)
    (hY : Y ⊆ Utilde B S)
    (hsound : Sound d)
    (hy : y ∈ Y)
    (hmin : ∀ y' ∈ Y, d y ≤ d y')
    (hle : d' y ≤ d y)
    (hsound' : Sound d') :
    Complete d' y ∧ d' y = d y := by
  have hyc : Complete d y :=
    IsFrontier.complete_of_min hF hY hsound hy hmin
  exact complete_stable_candidate hyc hle hsound'

end CHD
end Frontier
