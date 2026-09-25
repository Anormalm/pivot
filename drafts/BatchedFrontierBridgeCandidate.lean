/-!
# Batched FindPivots frontier bridge

The BMSSP correctness proof does not require an independent failed search for
each q in Q.  It only needs a root-closure property for those Q vertices that
serve as complete witnesses of the incoming frontier.

This lemma factors that argument out of FindPivots.lean so a batched/dormant
component implementation can target the same FPContract frontier field.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- An incoming frontier can be converted to a FindPivots output frontier
from only:
  * monotone sound labels,
  * a partition/cover of S into Q or pivot groups,
  * Q-root canonical closure into W.

No one-search-per-Q hypothesis appears. -/
theorem frontier_of_qroot_closure_candidate
    {B : WLab G s}
    {S Q W : Finset (Fin G.n)}
    {d d' : Labels G s}
    {p : ℕ} {P : Fin p → Finset (Fin G.n)}
    (hfront :
      IsFrontier d (Utilde B (S : Set (Fin G.n)))
        ∅ (S : Set (Fin G.n)))
    (hsound : Sound d')
    (hle : ∀ v, d' v ≤ d v)
    (hcover : ∀ y ∈ S, y ∈ Q ∨ ∃ j, y ∈ P j)
    (hqdone :
      ∀ y ∈ Q, ∀ v ∈ Utilde B (S : Set (Fin G.n)),
        Complete d y →
        OnPath (s := s) y v →
        v ∈ W ∧ Complete d' v) :
    IsFrontier d' (Utilde B (S : Set (Fin G.n)))
      (W : Set (Fin G.n))
      {x | ∃ j, x ∈ P j} := by
  intro v hv
  rcases hfront v hv with ⟨hX, -⟩ | ⟨y, hy, hyc, hyv⟩
  · exact absurd hX (Set.notMem_empty v)
  · rcases hcover y hy with hyQ | ⟨j, hj⟩
    · exact Or.inl (hqdone y hyQ v hv hyc hyv)
    · exact Or.inr
        ⟨y, ⟨j, hj⟩, hyc.of_le hsound (hle y), hyv⟩

end CHD
end Frontier
