/-!
# Stable closure inside actual FindPivots search states

Bridges the abstract complete-core idea back to upstream Search/Grows.

Upstream Closed.grows preserves an edge certificate when its tail label is
unchanged.  A complete tail is automatically unchanged under any later
sound monotone search state, so its cached outgoing closure is permanent.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- Closed certificates of a complete tail survive arbitrary later Grows
states with a sound search invariant. -/
theorem Closed.grows_of_complete_candidate
    {c : FPCtx G s}
    {σ σ' : SSt G s}
    {u : Fin G.n} {e : Fin G.m}
    (hclosed : Closed c σ u e)
    (hc : Complete σ.d u)
    (hg : Grows σ σ')
    (hI' : SInv c σ') :
    Closed c σ' u e := by
  have hc' : Complete σ'.d u :=
    le_antisymm ((hg.dle u).trans hc.le) (hI'.walk.sound u)
  have hsame : σ'.d u = σ.d u := by
    rw [hc', hc]
  exact hclosed.grows hg hsame

/-- The semantic complete core of a failed final val-region is closed under
below-B canonical descendants. -/
theorem failed_val_complete_core_canonical_closed_candidate
    {c : FPCtx G s} (hout : OutOK c)
    {σ : SSt G s}
    (hI : SInv c σ)
    (hH : σ.H = ∅)
    (hcl :
      ∀ w ∈ σ.done, ∀ e ∈ c.out w, Closed c σ w e)
    (hD :
      ∀ e ∈ σ.D,
        dis (s := s) (G.dst e) < dis (s := s) (G.src e)) :
    ∀ q,
      q ∈ σ.val →
      Complete σ.d q →
      ∀ v,
        OnPath (s := s) q v →
        dis (s := s) v < c.B →
        v ∈ σ.val ∧ Complete σ.d v := by
  intro q hq hqc v hqv hvB
  exact failed_state_complete_from_val_candidate
    hout hI hH hcl hD hq hqc hqv hvB

end CHD
end Frontier
