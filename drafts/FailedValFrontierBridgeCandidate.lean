/-!
# One failed val-region serving multiple Q roots

Combines:
  * the generalized final-val failed-search closure; and
  * the batched frontier bridge.

This is the direct BMSSP-facing correctness statement needed to skip later
S-roots that already lie in a dormant failed region's final val set.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- A single failed-state val region may discharge the frontier obligation
for every Q root recorded inside it.

Crucially, Q roots need not be known complete by the implementation.  The
frontier proof only asks for closure when the incoming witness is complete. -/
theorem frontier_from_failed_val_qroots_candidate
    {c : FPCtx G s} (hout : OutOK c)
    {S Q : Finset (Fin G.n)}
    {d0 : Labels G s}
    {σ : SSt G s}
    {p : ℕ} {P : Fin p → Finset (Fin G.n)}
    (hfront :
      IsFrontier d0
        (Utilde c.B (S : Set (Fin G.n)))
        ∅ (S : Set (Fin G.n)))
    (hle : ∀ v, σ.d v ≤ d0 v)
    (hI : SInv c σ)
    (hH : σ.H = ∅)
    (hcl :
      ∀ w ∈ σ.done, ∀ e ∈ c.out w, Closed c σ w e)
    (hD :
      ∀ e ∈ σ.D,
        dis (s := s) (G.dst e) < dis (s := s) (G.src e))
    (hQval : Q ⊆ σ.val)
    (hcover : ∀ y ∈ S, y ∈ Q ∨ ∃ j, y ∈ P j) :
    IsFrontier σ.d
      (Utilde c.B (S : Set (Fin G.n)))
      (σ.val : Set (Fin G.n))
      {x | ∃ j, x ∈ P j} := by
  apply frontier_of_qroot_closure_candidate
    hfront hI.walk.sound hle hcover
  intro y hy v hvU hyc hyv
  have hyc' : Complete σ.d y :=
    le_antisymm ((hle y).trans hyc.le) (hI.walk.sound y)
  exact failed_state_complete_from_val_candidate
    hout hI hH hcl hD (hQval hy) hyc' hyv hvU.1

end CHD
end Frontier
