/-!
# Full-call credit cancellation arithmetic

Pure natural-number lemma used by the refined CostLe full-call branch.
-/

namespace Frontier
namespace CHD
namespace BM

/-- If the expensive insertion coefficient is carried with +I*p on the
left, the refined `mk + own <= p + Cr + Be` inequality cancels the p term.
The cheap coefficient C may still use the old `mk <= p + Cr + Be` bound. -/
theorem full_credit_cancel_candidate
    {cost base C I p mk own Cr Be : ℕ}
    (hcost : cost + I * p ≤ base + C * mk + I * mk + I * own)
    (hmk : mk ≤ p + Cr + Be)
    (hmkOwn : mk + own ≤ p + Cr + Be) :
    cost ≤ base + C * (p + Cr + Be) + I * (Cr + Be) := by
  have hcheap : C * mk ≤ C * (p + Cr + Be) :=
    Nat.mul_le_mul_left C hmk
  have hexp : I * mk + I * own ≤ I * (p + Cr + Be) := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left I hmkOwn
  have hsplit : I * (p + Cr + Be) = I * p + I * (Cr + Be) := by
    ring
  rw [hsplit] at hexp
  omega

end BM
end CHD
end Frontier