/-!
# Complete-core stability under batched pending contacts

Composes the pending-map label safety facts with the complete-core stability
lemmas.  Sound pending candidates cannot perturb an already-complete dormant
core, so only the incomplete fringe needs propagation after a batch.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

theorem applyPendingMap_complete_stable_candidate
    {d : Labels G s} {P : DS G s} {u : Fin G.n}
    (hsound : Sound d)
    (hpending :
      ∀ v c, P v = some c →
        dis (s := s) v ≤ c)
    (hc : Complete d u) :
    Complete (applyPendingMap d P) u ∧
      applyPendingMap d P u = d u := by
  have hsound' :=
    applyPendingMap_sound_candidate
      (d := d) (P := P) hsound hpending
  have hle :=
    applyPendingMap_le_candidate d P u
  exact complete_stable_candidate hc hle hsound'

theorem applyPendingMap_complete_core_closed_candidate
    {d : Labels G s} {P : DS G s}
    {B : WLab G s} {W : Set (Fin G.n)}
    (hsound : Sound d)
    (hpending :
      ∀ v c, P v = some c →
        dis (s := s) v ≤ c)
    (hcomplete : ∀ u ∈ W, Complete d u)
    (hclosed :
      ∀ e : Fin G.m,
        G.src e ∈ W →
        ext (d (G.src e)) e < B →
        G.dst e ∈ W) :
    (∀ u ∈ W, Complete (applyPendingMap d P) u) ∧
    (∀ e : Fin G.m,
      G.src e ∈ W →
      ext (applyPendingMap d P (G.src e)) e < B →
      G.dst e ∈ W) := by
  apply complete_closed_region_stable_candidate
    hcomplete hclosed
  · exact applyPendingMap_le_candidate d P
  · exact applyPendingMap_sound_candidate
      (d := d) (P := P) hsound hpending

end CHD
end Frontier
