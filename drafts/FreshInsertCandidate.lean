/-!
# Candidate fresh BM.6 insertion-cost corollary

Status: source-aligned candidate under CI.
Upstream target:
  formal/lean/Frontier/CHD/DLazyFacts.lean

The point is purely accounting: BM.6 inserts the initial pivot list into
`newC`, which has exactly one block, while DLazy insertion never splits.
The generic evolved-structure insertion cost is therefore unnecessary here.
-/

namespace Frontier.CHD.BM

variable {G : Graph} {s : Fin G.n}

/-- Inserting any list into a freshly-created DLazy level structure costs
at most four abstract insertion steps per key.

This is the BM.6 specialization of upstream `insManyC_cost_le` at
`NB = 1`.
-/
theorem fresh_insManyC_cost_le_candidate
    (T0 : ℕ) (f : Fin G.n → WLab G s)
    (l : List (Fin G.n)) (g : DGl G s)
    (M : ℕ) (B : WLab G s) :
    (insManyC (dlOps G s) T0 f l g (newC M B)).2.2
      ≤ 4 * l.length := by
  have h :=
    insManyC_cost_le T0 f 1 l g (newC M B) (by
      simp [newC])
  simpa [Nat.mul_comm] using h

end Frontier.CHD.BM
