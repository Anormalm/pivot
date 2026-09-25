/-!
# Retiring scanned edges from complete tails

If an edge is processed while its tail is complete, then after the head has
been lowered to at most that edge candidate, the edge can never improve the
head in any later sound monotone label state.

This is the key safety lemma for a batched/global-min FindPivots design that
would scan outgoing edges only from complete vertices and retire them
globally.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- Generic retirement lemma. -/
theorem complete_tail_edge_retired_candidate
    {d d1 d2 : Labels G s} {e : Fin G.m}
    (hc : Complete d (G.src e))
    (hprocessed :
      d1 (G.dst e) ≤ ext (d (G.src e)) e)
    (hle21 : ∀ v, d2 v ≤ d1 v)
    (hle10 : ∀ v, d1 v ≤ d v)
    (hsound : Sound d2) :
    ¬ ext (d2 (G.src e)) e < d2 (G.dst e) := by
  have hsrcle : d2 (G.src e) ≤ d (G.src e) :=
    (hle21 (G.src e)).trans (hle10 (G.src e))
  have hstable :
      d2 (G.src e) = d (G.src e) :=
    (complete_stable_candidate hc hsrcle hsound).2
  have hhead :
      d2 (G.dst e) ≤ ext (d (G.src e)) e :=
    (hle21 (G.dst e)).trans hprocessed
  rw [hstable]
  exact not_lt_of_ge hhead

/-- A FindPivots Relax call processes an edge strongly enough for the generic
retirement lemma: afterwards the head label is at most the candidate computed
from the pre-relaxation tail label. -/
theorem relaxL_head_le_candidate_candidate
    {d : Labels G s} {e : Fin G.m} :
    relaxL d (G.src e) e (G.dst e) ≤
      ext (d (G.src e)) e := by
  by_cases hok : Ok d (G.src e) e
  · rw [relaxL_apply_self hok]
  · rw [relaxL_of_not_ok hok]
    exact le_of_not_ge hok

/-- Direct corollary for a processed FindPivots edge.  If later labels are
sound and pointwise no larger than the post-Relax labels, the same edge can
never become improving again. -/
theorem relax_from_complete_tail_retired_candidate
    {d d2 : Labels G s} {e : Fin G.m}
    (hc : Complete d (G.src e))
    (hle :
      ∀ v, d2 v ≤ relaxL d (G.src e) e v)
    (hsound : Sound d2) :
    ¬ ext (d2 (G.src e)) e < d2 (G.dst e) := by
  apply complete_tail_edge_retired_candidate
    (d1 := relaxL d (G.src e) e)
    hc
    relaxL_head_le_candidate_candidate
    hle
    (fun v => relaxL_le d (G.src e) e v)
    hsound

end CHD
end Frontier
