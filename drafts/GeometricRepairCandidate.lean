/-!
# Geometric repair amortization

Pure arithmetic skeleton for dormant-component repair epochs.

A RepairChain b r f means that starting from base size b, after r full
repair epochs, each triggered only after at least a doubling, the final base
is f.

The central theorem avoids any dependence on Nat.log APIs:
  2^r * b <= f.

Hence, while f < k and b >= 1:
  2^r < k.

This is the exact finite statement behind the O(log k) number of full repair
epochs.
-/

namespace Frontier
namespace CHD

/-- Doubling-triggered repair epochs. -/
inductive RepairChain : ℕ → ℕ → ℕ → Prop
  | zero (b : ℕ) : RepairChain b 0 b
  | step {b b' r f : ℕ} :
      2 * b ≤ b' →
      RepairChain b' r f →
      RepairChain b (r + 1) f

/-- After r doubling epochs, the final base is at least 2^r times the
initial base. -/
theorem RepairChain.pow_mul_le_candidate
    {b r f : ℕ}
    (h : RepairChain b r f) :
    2 ^ r * b ≤ f := by
  induction h with
  | zero b =>
      simp
  | @step b b' r f hdouble hrest ih =>
      calc
        2 ^ (r + 1) * b
            = 2 ^ r * (2 * b) := by ring
        _ ≤ 2 ^ r * b' :=
          Nat.mul_le_mul_left _ hdouble
        _ ≤ f := ih

/-- A sub-k component can undergo only as many doubling epochs as fit powers
of two below k. -/
theorem RepairChain.pow_lt_cap_candidate
    {b r f k : ℕ}
    (h : RepairChain b r f)
    (hb : 1 ≤ b)
    (hfk : f < k) :
    2 ^ r < k := by
  have hpow : 2 ^ r ≤ 2 ^ r * b := by
    simpa using
      (Nat.mul_le_mul_left (2 ^ r) hb)
  exact lt_of_le_of_lt
    (hpow.trans h.pow_mul_le_candidate)
    hfk

/-- In particular, no component of cap k can realize a chain whose power-of-2
lower bound already reaches k. -/
theorem RepairChain.not_of_cap_le_pow_candidate
    {b r f k : ℕ}
    (hb : 1 ≤ b)
    (hfk : f < k)
    (hpow : k ≤ 2 ^ r) :
    ¬ RepairChain b r f := by
  intro h
  have := h.pow_lt_cap_candidate hb hfk
  omega

end CHD
end Frontier


/-- If every full repair scans at most E edges and there are at most r+1
repairs (r doubling-triggered epochs plus one final closure), total full-repair
scan work is at most (r+1)E. -/
theorem repair_scan_sum_le_candidate
    {cs : List ℕ} {r E : ℕ}
    (hlen : cs.length ≤ r + 1)
    (hcost : ∀ c ∈ cs, c ≤ E) :
    cs.sum ≤ (r + 1) * E := by
  have hsum : cs.sum ≤ cs.length * E := by
    induction cs with
    | nil =>
        simp
    | cons c cs ih =>
        have hc : c ≤ E := hcost c (by simp)
        have htail : ∀ x ∈ cs, x ≤ E := by
          intro x hx
          exact hcost x (by simp [hx])
        have hih := ih htail
        simp only [List.sum_cons, List.length_cons]
        omega
  exact hsum.trans (Nat.mul_le_mul_right E hlen)

/-- Combined arithmetic envelope: a doubling-bounded component with r growth
epochs and at most one final closure pays at most (r+1)E full-repair scans,
while 2^r remains below the component cap k. -/
theorem RepairChain.scan_budget_candidate
    {b r f k E : ℕ}
    {cs : List ℕ}
    (h : RepairChain b r f)
    (hb : 1 ≤ b)
    (hfk : f < k)
    (hlen : cs.length ≤ r + 1)
    (hcost : ∀ c ∈ cs, c ≤ E) :
    cs.sum ≤ (r + 1) * E ∧ 2 ^ r < k := by
  exact ⟨repair_scan_sum_le_candidate hlen hcost,
    h.pow_lt_cap_candidate hb hfk⟩
