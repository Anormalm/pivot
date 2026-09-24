/-!
# Candidate square-root parameter arithmetic

These are generic arithmetic lemmas for the proposed retuning:
  k = 4,
  t >= 16,
  lgN <= t^2 * dd,
  L = lgN / t + 1.

No algorithmic semantics are changed here.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph Frontier.CostSkeleton

/-- Constant k=4 satisfies the current elementary k/t side conditions once
t >= 16. -/
theorem k4_side_conditions_candidate {t : ℕ} (ht : 16 ≤ t) :
    2 ≤ 4 ∧ 4 ≤ t ∧ 3 * 4 ≤ t ∧ 4 * (4 + 1) ≤ 2 * t := by
  omega

/-- Candidate recursion depth. -/
def LsqrtCandidate (n t : ℕ) : ℕ := lgN n / t + 1

theorem LsqrtCandidate_pos (n t : ℕ) :
    1 ≤ LsqrtCandidate n t := by
  unfold LsqrtCandidate
  omega

/-- The standard depth coverage lemma uses only t>0, not the old cube-root
parameter specification. -/
theorem lgN_succ_le_Lsqrt_mul_candidate
    (n t : ℕ) (ht : 1 ≤ t) :
    lgN n + 1 ≤ LsqrtCandidate n t * t := by
  unfold LsqrtCandidate
  have e1 := Nat.div_add_mod (lgN n) t
  have e2 := Nat.mod_lt (lgN n) t (by omega)
  rw [Nat.add_mul, one_mul]
  nlinarith

/-- The top workload cap remains above 2n with the candidate depth for any
t >= 16. -/
theorem tau_top_sqrt_candidate
    (n t : ℕ) (ht : 16 ≤ t) :
    2 * n < chdTau t (LsqrtCandidate n t) := by
  have hLt :=
    lgN_succ_le_Lsqrt_mul_candidate n t (by omega)
  have hn2 : n < 2 ^ (lgN n + 1) := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    have hle : Nat.log 2 n ≤ lgN n := le_max_right _ _
    exact lt_of_lt_of_le h
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 :
      2 ^ (lgN n + 1) ≤
        2 ^ (LsqrtCandidate n t * t) :=
    Nat.pow_le_pow_right (by norm_num) hLt
  have ht3 : 2 ≤ t ^ 3 := by
    have h16 : 16 ^ 3 ≤ t ^ 3 :=
      Nat.pow_le_pow_left ht 3
    omega
  unfold chdTau
  calc
    2 * n < 2 * 2 ^ (LsqrtCandidate n t * t) := by omega
    _ ≤ t ^ 3 * 2 ^ (LsqrtCandidate n t * t) :=
      Nat.mul_le_mul_right _ ht3

/-- Under the C-HD Gate-C density branch, the new square-root specification
still makes lgN polynomially bounded in t.  A loose exponent 8 is enough for
the logarithmic block-search proof. -/
theorem lgN_le_t8_candidate
    (n m t : ℕ)
    (ht : 1 ≤ t)
    (hspec : lgN n ≤ t ^ 2 * dd n m)
    (hdd : dd n m ≤ Frontier.GateCCalc.F n + 1) :
    lgN n ≤ 16 * t ^ 8 := by
  set f := Frontier.GateCCalc.F n with hf
  set A := lgN n with hA
  set d := dd n m with hd

  have hlog : Nat.log 2 n ≤ A := by
    rw [hA]
    exact le_max_right _ _

  have hf4 : f ^ 4 ≤ A ^ 3 := by
    rw [hf]
    exact le_trans (Frontier.GateCCalc.F_pow_four_le n)
      (Nat.pow_le_pow_left hlog 3)

  have hAd : A ≤ t ^ 2 * (f + 1) := by
    rw [hA, ← hd, ← hf]
    exact hspec.trans (Nat.mul_le_mul_left _ hdd)

  by_cases hf0 : f = 0
  · subst f
    have hA_le : A ≤ t ^ 2 := by
      simpa using hAd
    have ht2_le : t ^ 2 ≤ 16 * t ^ 8 := by
      have ht6 : 1 ≤ t ^ 6 := Nat.one_le_pow _ _ ht
      calc
        t ^ 2 = 1 * t ^ 2 := by ring
        _ ≤ (16 * t ^ 6) * t ^ 2 := by
          exact Nat.mul_le_mul_right _ (by omega)
        _ = 16 * t ^ 8 := by ring
    exact hA_le.trans ht2_le
  · have hfpos : 1 ≤ f := by omega
    have hf1 : f + 1 ≤ 2 * f := by omega
    have hA2 : A ≤ 2 * t ^ 2 * f := by
      calc
        A ≤ t ^ 2 * (f + 1) := hAd
        _ ≤ t ^ 2 * (2 * f) :=
          Nat.mul_le_mul_left _ hf1
        _ = 2 * t ^ 2 * f := by ring

    have hA3 : A ^ 3 ≤ (2 * t ^ 2 * f) ^ 3 :=
      Nat.pow_le_pow_left hA2 3

    have hfbound :
        f ^ 4 ≤ 8 * t ^ 6 * f ^ 3 := by
      calc
        f ^ 4 ≤ A ^ 3 := hf4
        _ ≤ (2 * t ^ 2 * f) ^ 3 := hA3
        _ = 8 * t ^ 6 * f ^ 3 := by ring

    have hf3pos : 0 < f ^ 3 := by positivity
    have hfactor :
        f * f ^ 3 ≤ (8 * t ^ 6) * f ^ 3 := by
      simpa [pow_succ] using hfbound
    have hf_le : f ≤ 8 * t ^ 6 := by
      exact Nat.le_of_mul_le_mul_right hfactor hf3pos

    have hfp1 : f + 1 ≤ 9 * t ^ 6 := by
      have ht6 : 1 ≤ t ^ 6 := Nat.one_le_pow _ _ ht
      omega

    calc
      A ≤ t ^ 2 * (f + 1) := hAd
      _ ≤ t ^ 2 * (9 * t ^ 6) :=
        Nat.mul_le_mul_left _ hfp1
      _ = 9 * t ^ 8 := by ring
      _ ≤ 16 * t ^ 8 := by omega

end BM
end CHD
end Frontier
