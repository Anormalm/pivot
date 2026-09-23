/-!
# Candidate credit-carrying CostLog interface

Status: UNCOMPILED source-aligned design draft.

This is intentionally parallel to existing RecCost/SubCost instead of
changing CallRec or LogInv.
-/

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n} {Ω : Type}

/-- Full-call credit carried on the left side. -/
def fullCredit (I : ℕ) (r : CallRec G s Ω) : ℕ :=
  if r.B' = r.B then I * r.p else 0

/-- Generic credit-aware per-record cost predicate. -/
def RecCostCredit
    (chg : CallRec G s Ω → CallRec G s Ω → ℕ)
    (bud extra : CallRec G s Ω → ℕ → ℕ)
    (credit : CallRec G s Ω → ℕ)
    (lg : Log G s Ω) : Prop :=
  ∀ q r, (q, r) ∈ lg → r.base = false →
    r.cost + credit r
      ≤ bud r (childSumAt (chg r) q lg)
        + extra r (childSumAt (chg r) q lg)

/-- Shift transport: verbatim shape of RecCost.shift. -/
theorem RecCostCredit.shift_candidate
    {chg : CallRec G s Ω → CallRec G s Ω → ℕ}
    {bud extra : CallRec G s Ω → ℕ → ℕ}
    {credit : CallRec G s Ω → ℕ}
    {lg : Log G s Ω}
    (h : RecCostCredit chg bud extra credit lg)
    (i : ℕ) (lg' : Log G s Ω)
    (hsh : ∀ q r, (q, r) ∈ lg' → ∃ j q', q = j :: q' ∧ j ≠ i) :
    ∀ q r, (q, r) ∈ lg.shift i → r.base = false →
      r.cost + credit r
        ≤ bud r (childSumAt (chg r) q (lg.shift i ++ lg'))
          + extra r (childSumAt (chg r) q (lg.shift i ++ lg')) := by
  intro q r hqr hb
  obtain ⟨q', rfl, hq'⟩ := mem_shift.mp hqr
  rw [childSumAt_append, childSumAt_shift,
    childSumAt_of_shape _ i q' lg' hsh, Nat.add_zero]
  exact h q' r hq' hb

end BM
end CHD
end Frontier