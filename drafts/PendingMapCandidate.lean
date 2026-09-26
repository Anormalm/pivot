/-!
# Component-level pending candidate map

A dormant component may accumulate many incoming relaxation candidates before
reactivating propagation.  Store those candidates in the existing abstract DS
shape (one optional minimum label per vertex), and apply them simultaneously at
a repair point.

This file proves only the label-level safety facts:
- applying pending candidates is pointwise monotone;
- sound candidate labels preserve Soundness.

Propagation/closure after the batch remains a separate obligation.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- Apply one optional pending minimum to every vertex. -/
noncomputable def applyPendingMap
    (d : Labels G s) (P : DS G s) : Labels G s :=
  fun v =>
    match P v with
    | none => d v
    | some c => min (d v) c

/-- A pending-map batch only decreases labels. -/
theorem applyPendingMap_le_candidate
    (d : Labels G s) (P : DS G s) :
    ∀ v, applyPendingMap d P v ≤ d v := by
  intro v
  unfold applyPendingMap
  cases h : P v with
  | none =>
      simp
  | some c =>
      exact min_le_left _ _

/-- If every stored pending candidate is a sound upper bound for its target's
canonical distance, applying the whole batch preserves Soundness. -/
theorem applyPendingMap_sound_candidate
    {d : Labels G s} {P : DS G s}
    (hsound : Sound d)
    (hpending :
      ∀ v c, P v = some c →
        dis (s := s) v ≤ c) :
    Sound (applyPendingMap d P) := by
  intro v
  unfold applyPendingMap
  cases h : P v with
  | none =>
      simpa [h] using hsound v
  | some c =>
      simp only [h]
      exact le_min (hsound v) (hpending v c h)

/-- Inserting one additional sound candidate into a pending map preserves the
pending-candidate soundness invariant. -/
theorem pending_insert_sound_candidate
    {P : DS G s} {v : Fin G.n} {c : WLab G s}
    (hP :
      ∀ x k, P x = some k →
        dis (s := s) x ≤ k)
    (hc : dis (s := s) v ≤ c) :
    ∀ x k, P.insert v c x = some k →
      dis (s := s) x ≤ k := by
  intro x k hk
  by_cases hx : x = v
  · subst x
    unfold DS.insert at hk
    simp only [Function.update_self] at hk
    cases hPv : P v with
    | none =>
        simp [DS.mergeVal, hPv] at hk
        subst k
        exact hc
    | some old =>
        simp [DS.mergeVal, hPv] at hk
        subst k
        exact le_min (hP v old hPv) hc
  · unfold DS.insert at hk
    rw [Function.update_noteq hx] at hk
    exact hP x k hk

end CHD
end Frontier
