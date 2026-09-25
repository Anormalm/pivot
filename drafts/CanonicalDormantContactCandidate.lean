/-!
# Canonical contacts into dormant regions

If an edge out of a complete tail is the canonical successor edge, then the
FindPivots Relax operation makes its head complete immediately.

This gives a useful operational split for dormant-region contacts:
- unchanged label: the target was already complete and its cached closure is stable;
- strict change: the new target version is complete, so its outgoing work can
  be scanned once from an exact tail and then retired.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- Relaxing a canonical successor edge from a complete tail writes the
canonical label of the head. -/
theorem canonical_relax_complete_candidate
    {d : Labels G s} {e : Fin G.m}
    (hsound : Sound d)
    (htail : Complete d (G.src e))
    (hcanon :
      dis (s := s) (G.dst e) =
        ext (dis (s := s) (G.src e)) e) :
    Complete
      (relaxL d (G.src e) e)
      (G.dst e) := by
  have hok : Ok d (G.src e) e := by
    unfold Ok
    rw [htail, ← hcanon]
    exact hsound (G.dst e)
  show
    relaxL d (G.src e) e (G.dst e) =
      dis (s := s) (G.dst e)
  rw [relaxL_apply_self hok, htail, ← hcanon]

/-- If the canonical contact did not change the head label, then the head was
already complete before the contact. -/
theorem canonical_contact_unchanged_was_complete_candidate
    {d : Labels G s} {e : Fin G.m}
    (hsound : Sound d)
    (htail : Complete d (G.src e))
    (hcanon :
      dis (s := s) (G.dst e) =
        ext (dis (s := s) (G.src e)) e)
    (hsame :
      relaxL d (G.src e) e (G.dst e) =
        d (G.dst e)) :
    Complete d (G.dst e) := by
  have hc :=
    canonical_relax_complete_candidate
      hsound htail hcanon
  show d (G.dst e) = dis (s := s) (G.dst e)
  rw [← hsame]
  exact hc

/-- A strict canonical contact creates a new exact version of the target.
This statement deliberately records only completeness; strictness is useful
for the cost layer as the observable cache invalidation event. -/
theorem canonical_contact_changed_now_complete_candidate
    {d : Labels G s} {e : Fin G.m}
    (hsound : Sound d)
    (htail : Complete d (G.src e))
    (hcanon :
      dis (s := s) (G.dst e) =
        ext (dis (s := s) (G.src e)) e)
    (_hchanged :
      relaxL d (G.src e) e (G.dst e) ≠
        d (G.dst e)) :
    Complete
      (relaxL d (G.src e) e)
      (G.dst e) :=
  canonical_relax_complete_candidate
    hsound htail hcanon

end CHD
end Frontier
