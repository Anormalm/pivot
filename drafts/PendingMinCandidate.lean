/-!
# Pending-min batching for dormant contacts

Multiple incoming contact candidates to one dormant vertex can be accumulated
without immediately propagating through the component: keep only the minimum
candidate for that head.

This file isolates the label-level fact.  It does not claim that arbitrary
component propagation may be delayed forever; it only proves that coalescing
pending candidates at one head loses no best-label information.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- Minimum of the current head label and a list of pending candidate labels. -/
def pendingMin (base : WLab G s) : List (WLab G s) → WLab G s
  | [] => base
  | c :: cs => pendingMin (min base c) cs

/-- Apply all pending candidates to one head in one batched update. -/
noncomputable def applyPending
    (d : Labels G s) (v : Fin G.n)
    (cs : List (WLab G s)) : Labels G s :=
  Function.update d v (pendingMin (d v) cs)

theorem pendingMin_le_base_candidate
    (base : WLab G s) (cs : List (WLab G s)) :
    pendingMin base cs ≤ base := by
  induction cs generalizing base with
  | nil =>
      simp [pendingMin]
  | cons c cs ih =>
      exact (ih (min base c)).trans min_le_left

theorem pendingMin_le_mem_candidate
    {base : WLab G s} {cs : List (WLab G s)}
    {c : WLab G s} (hc : c ∈ cs) :
    pendingMin base cs ≤ c := by
  induction cs generalizing base with
  | nil =>
      simp at hc
  | cons a cs ih =>
      rcases List.mem_cons.mp hc with rfl | hc
      · exact (pendingMin_le_base_candidate
          (G := G) (s := s) (min base a) cs).trans min_le_right
      · exact ih (base := min base a) hc

/-- Batched pending candidates only decrease the chosen head. -/
theorem applyPending_le_candidate
    (d : Labels G s) (v : Fin G.n)
    (cs : List (WLab G s)) :
    ∀ x, applyPending d v cs x ≤ d x := by
  intro x
  by_cases hx : x = v
  · subst x
    simp [applyPending, pendingMin_le_base_candidate]
  · simp [applyPending, Function.update_noteq hx]

/-- If every pending candidate is itself a sound upper bound for the head's
canonical distance, batching by minimum preserves global Soundness. -/
theorem applyPending_sound_candidate
    {d : Labels G s} {v : Fin G.n}
    {cs : List (WLab G s)}
    (hsound : Sound d)
    (hcand : ∀ c ∈ cs, dis (s := s) v ≤ c) :
    Sound (applyPending d v cs) := by
  intro x
  by_cases hx : x = v
  · subst x
    simp only [applyPending, Function.update_self]
    induction cs generalizing d with
    | nil =>
        simp [pendingMin]
        exact hsound v
    | cons c cs ih =>
        simp only [pendingMin]
        have hbase : dis (s := s) v ≤ min (d v) c :=
          le_min (hsound v) (hcand c (by simp))
        have htail :
            ∀ z ∈ cs, dis (s := s) v ≤ z := by
          intro z hz
          exact hcand z (by simp [hz])
        clear ih
        induction cs generalizing d with
        | nil =>
            simpa [pendingMin] using hbase
        | cons a as ih2 =>
            simp only [pendingMin]
            have ha : dis (s := s) v ≤ a :=
              htail a (by simp)
            have hnext :
                dis (s := s) v ≤ min (min (d v) c) a :=
              le_min hbase ha
            -- continue through the remaining pending values
            have hrest :
                ∀ z ∈ as, dis (s := s) v ≤ z := by
              intro z hz
              exact htail z (by simp [hz])
            exact
              (by
                induction as generalizing d with
                | nil =>
                    simpa [pendingMin] using hnext
                | cons b bs ih3 =>
                    simp only [pendingMin]
                    have hb : dis (s := s) v ≤ b :=
                      hrest b (by simp)
                    exact ih3
                      (d := Function.update d v
                        (min (min (d v) c) a))
                      (by
                        intro z hz
                        exact hrest z (by simp [hz])))
  · simp [applyPending, Function.update_noteq hx]
    exact hsound x

/-- A singleton pending batch is just a min-update at the head. -/
theorem applyPending_singleton_candidate
    (d : Labels G s) (v : Fin G.n) (c : WLab G s) :
    applyPending d v [c]
      = Function.update d v (min (d v) c) := by
  funext x
  by_cases hx : x = v
  · subst x
    simp [applyPending, pendingMin]
  · simp [applyPending, pendingMin, Function.update_noteq hx]

end CHD
end Frontier
