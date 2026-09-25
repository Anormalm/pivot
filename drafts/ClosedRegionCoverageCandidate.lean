/-!
# Closed-region coverage for batched / dormant FindPivots

A generic multi-root replacement for the *shape* of failed-search completeness.

If W consists of complete vertices and is closed under every outgoing
relaxation whose candidate is below B, then W contains every canonical
descendant below B of any root already in W.

This does not construct such a W efficiently; it isolates the correctness
obligation for a batched component implementation.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- Complete edge-closed regions contain their below-B canonical descendants. -/
theorem closed_complete_region_covers_candidate
    {d : Labels G s} {B : WLab G s}
    {W : Set (Fin G.n)} {q v : Fin G.n}
    (hcomplete : ∀ u ∈ W, Complete d u)
    (hclosed :
      ∀ e : Fin G.m,
        G.src e ∈ W →
        ext (d (G.src e)) e < B →
        G.dst e ∈ W)
    (hq : q ∈ W)
    (hqv : OnPath (s := s) q v)
    (hvB : dis (s := s) v < B) :
    v ∈ W ∧ Complete d v := by
  by_cases hvW : v ∈ W
  · exact ⟨hvW, hcomplete v hvW⟩
  · obtain ⟨e, hsrcW, hdstW, -, hdstPath, hcanon⟩ :=
      hqv.exists_exit W hq hvW
    have hsrcC := hcomplete (G.src e) hsrcW
    have hcand :
        ext (d (G.src e)) e = dis (s := s) (G.dst e) := by
      rw [hsrcC]
      exact hcanon.symm
    have hdstB :
        dis (s := s) (G.dst e) < B :=
      lt_of_le_of_lt hdstPath.dis_le hvB
    have hbelow :
        ext (d (G.src e)) e < B := by
      rw [hcand]
      exact hdstB
    exact absurd (hclosed e hsrcW hbelow) hdstW

/-- Set-of-roots form used by a final dormant component. -/
theorem closed_complete_region_covers_roots_candidate
    {d : Labels G s} {B : WLab G s}
    {W R : Set (Fin G.n)}
    (hcomplete : ∀ u ∈ W, Complete d u)
    (hclosed :
      ∀ e : Fin G.m,
        G.src e ∈ W →
        ext (d (G.src e)) e < B →
        G.dst e ∈ W)
    (hRW : R ⊆ W) :
    ∀ q ∈ R, ∀ v,
      OnPath (s := s) q v →
      dis (s := s) v < B →
      v ∈ W ∧ Complete d v := by
  intro q hq v hqv hvB
  exact closed_complete_region_covers_candidate
    hcomplete hclosed (hRW hq) hqv hvB

end CHD
end Frontier
