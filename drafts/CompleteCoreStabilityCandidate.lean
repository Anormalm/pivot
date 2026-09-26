/-!
# Stable complete cores for batched FindPivots

A complete edge-closed region is permanent under later sound monotone
label updates.  This isolates the part of a dormant component that can be
reused with zero version invalidation.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- Once a vertex is complete, any later sound pointwise-smaller label is
definitionally the same canonical label. -/
theorem complete_stable_candidate
    {d d' : Labels G s} {u : Fin G.n}
    (hc : Complete d u)
    (hle : d' u ≤ d u)
    (hsound : Sound d') :
    Complete d' u ∧ d' u = d u := by
  have hc' : Complete d' u :=
    le_antisymm (hle.trans hc.le) (hsound u)
  exact ⟨hc', hc'.trans hc.symm⟩

/-- A complete below-B closed region remains complete and closed after any
sound monotone label improvement.  In particular, no outgoing edge of the
core needs to be rescanned merely because labels elsewhere changed. -/
theorem complete_closed_region_stable_candidate
    {d d' : Labels G s} {B : WLab G s}
    {W : Set (Fin G.n)}
    (hcomplete : ∀ u ∈ W, Complete d u)
    (hclosed :
      ∀ e : Fin G.m,
        G.src e ∈ W →
        ext (d (G.src e)) e < B →
        G.dst e ∈ W)
    (hle : ∀ v, d' v ≤ d v)
    (hsound : Sound d') :
    (∀ u ∈ W, Complete d' u) ∧
    (∀ e : Fin G.m,
      G.src e ∈ W →
      ext (d' (G.src e)) e < B →
      G.dst e ∈ W) := by
  constructor
  · intro u hu
    exact (complete_stable_candidate
      (hcomplete u hu) (hle u) hsound).1
  · intro e hsrc hbelow
    have hstable :
        d' (G.src e) = d (G.src e) :=
      (complete_stable_candidate
        (hcomplete (G.src e) hsrc) (hle (G.src e)) hsound).2
    apply hclosed e hsrc
    simpa [hstable] using hbelow

/-- Unions of complete closed regions are again complete and closed.  This is
the algebraic operation needed when two already-certified dormant cores are
merged without changing labels on either core. -/
theorem complete_closed_union_candidate
    {d : Labels G s} {B : WLab G s}
    {W1 W2 : Set (Fin G.n)}
    (hc1 : ∀ u ∈ W1, Complete d u)
    (hc2 : ∀ u ∈ W2, Complete d u)
    (hcl1 :
      ∀ e : Fin G.m,
        G.src e ∈ W1 →
        ext (d (G.src e)) e < B →
        G.dst e ∈ W1)
    (hcl2 :
      ∀ e : Fin G.m,
        G.src e ∈ W2 →
        ext (d (G.src e)) e < B →
        G.dst e ∈ W2) :
    (∀ u ∈ W1 ∪ W2, Complete d u) ∧
    (∀ e : Fin G.m,
      G.src e ∈ W1 ∪ W2 →
      ext (d (G.src e)) e < B →
      G.dst e ∈ W1 ∪ W2) := by
  constructor
  · intro u hu
    rcases hu with hu | hu
    · exact hc1 u hu
    · exact hc2 u hu
  · intro e hsrc hbelow
    rcases hsrc with h1 | h2
    · exact Or.inl (hcl1 e h1 hbelow)
    · exact Or.inr (hcl2 e h2 hbelow)

end CHD
end Frontier
