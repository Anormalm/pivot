/-!
# Refined global aggregation with cheap full-call pivot work

This leaves CostAggregate.Valid unchanged and reuses all of its structural
fields.  The theorem takes a separate refined per-call cost premise whose
pivot term is k*p rather than t*p.

The old Valid.cost_le field can remain as a redundant coarse bound.
-/

namespace Frontier.CostAggregate.CallCounters

open Finset Frontier.CostCharging

set_option linter.unusedSectionVars false

variable {ι V E α : Type*}
  [Fintype ι] [Fintype V] [Fintype E]
  [DecidableEq ι] [DecidableEq V] [DecidableEq E]
  [LinearOrder α]

variable {C : CallCounters ι V E α}

/-- With the refined local accounting, pivot work is only O(k) per group.
After multiplying by k-1, full calls charge to U+Fo, while partial calls
are absorbed by t*S and hence U. -/
theorem sum_kp_refined_candidate
    {t k c Lmax M0 : ℕ}
    {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (h : C.Valid t k c Lmax M0 inE wit src) :
    (k - 1) * ∑ X, k * C.p X
      ≤
    3 * k * ((Lmax + 1) * Fintype.card V)
      + (k - 1) * ((Lmax + 1) * Fintype.card V) := by
  classical
  rw [sum_split (C := C), Nat.mul_add]
  have hU := sum_U_le h
  have hFo := sum_Fo_le h

  have hfull :
      (k - 1) *
          ∑ X ∈ univ.filter (fun X => C.full X = true), k * C.p X
        ≤
      3 * k * ((Lmax + 1) * Fintype.card V) := by
    rw [Finset.mul_sum]
    calc
      ∑ X ∈ univ.filter (fun X => C.full X = true),
          (k - 1) * (k * C.p X)
        ≤
      ∑ X ∈ univ.filter (fun X => C.full X = true),
          k * ((C.F.U X).card + (C.Fo X).card) := by
        refine Finset.sum_le_sum fun X hX => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
        have hp := h.full_p X hX
        calc
          (k - 1) * (k * C.p X)
              = k * (C.p X * (k - 1)) := by ring
          _ ≤ k * ((C.F.U X).card + (C.Fo X).card) :=
            Nat.mul_le_mul_left _ hp
      _ ≤
      ∑ X, k * ((C.F.U X).card + (C.Fo X).card) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ =
      k * (∑ X, (C.F.U X).card + ∑ X, (C.Fo X).card) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤
      k * (((Lmax + 1) * Fintype.card V)
        + 2 * ((Lmax + 1) * Fintype.card V)) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add hU hFo)
      _ = 3 * k * ((Lmax + 1) * Fintype.card V) := by ring

  have hpart :
      (k - 1) *
          ∑ X ∈ univ.filter (fun X => ¬ C.full X = true), k * C.p X
        ≤
      (k - 1) * ((Lmax + 1) * Fintype.card V) := by
    apply Nat.mul_le_mul_left
    calc
      ∑ X ∈ univ.filter (fun X => ¬ C.full X = true), k * C.p X
        ≤
      ∑ X ∈ univ.filter (fun X => ¬ C.full X = true),
          (C.F.U X).card := by
        refine Finset.sum_le_sum fun X hX => ?_
        simp only [Finset.mem_filter, Finset.mem_univ,
          true_and, Bool.not_eq_true] at hX
        calc
          k * C.p X
            ≤ k * (C.S X).card :=
              Nat.mul_le_mul_left _ (h.partial_p X hX)
          _ ≤ t * (C.S X).card :=
              Nat.mul_le_mul_right _ h.k_le_t
          _ ≤ (C.F.U X).card := h.partial_S X hX
      _ ≤ ∑ X, (C.F.U X).card :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ (Lmax + 1) * Fintype.card V := hU

  exact Nat.add_le_add hfull hpart

/-- Refined aggregation theorem.

The per-call premise differs from Valid.cost_le only in the pivot term:
  old: t * p
  new: k * p
while the partial-call t*S term is retained.
-/
theorem total_cost_refined_candidate
    {t k c Lmax M0 : ℕ}
    {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (h : C.Valid t k c Lmax M0 inE wit src)
    (hcost : ∀ X, C.base X = false →
      C.cost X ≤ c *
        ((k + 1) * ((C.F.U X).card + (C.Fo X).card)
          + (C.S X).card
          + t * (C.Q X).card
          + t * ((C.J X).card + (C.Wr X).card
            + (C.Cr X).card + (C.Be X).card)
          + k * C.p X
          + (if C.full X then 0 else t * (C.S X).card)
          + C.mergeCost X + (C.Del X).card)) :
    (k - 1) *
        ∑ X ∈ univ.filter (fun X => C.base X = false), C.cost X
      ≤
    c * (
      (k - 1) *
        ((3 * k + 8) * ((Lmax + 1) * Fintype.card V)
          + 6 * t * (Fintype.card E + 1)
          + M0)
      + 3 * k * ((Lmax + 1) * Fintype.card V)) := by
  classical
  set N := (Lmax + 1) * Fintype.card V with hN

  have hU := sum_U_le h
  have hFo := sum_Fo_le h
  have hS : ∑ X, (C.S X).card ≤ N :=
    le_trans (Finset.sum_le_sum fun X _ => S_le_U h X) hU
  have hQ := sum_tQ_le h
  have hJ := sum_J_le h
  have hW := sum_Wr_le h
  have hCr := sum_Cr_le h
  have hp := sum_kp_refined_candidate h
  have hpS := sum_partial_tS_le h
  have hM := h.merge_total
  have hBe := h.be_total
  have hDel := sum_Del_le h

  set R : ι → ℕ := fun X =>
      (k + 1) * ((C.F.U X).card + (C.Fo X).card)
        + (C.S X).card
        + t * (C.Q X).card
        + t * ((C.J X).card + (C.Wr X).card
          + (C.Cr X).card + (C.Be X).card)
        + (if C.full X then 0 else t * (C.S X).card)
        + C.mergeCost X + (C.Del X).card with hR

  have hRsum :
      ∑ X, R X
        ≤
      (3 * k + 7) * N
        + 5 * t * (Fintype.card E + 1)
        + M0 + Fintype.card E := by
    have e : ∑ X, R X =
        (k + 1) *
            (∑ X, (C.F.U X).card + ∑ X, (C.Fo X).card)
          + ∑ X, (C.S X).card
          + ∑ X, t * (C.Q X).card
          + t * (∑ X, (C.J X).card
            + ∑ X, (C.Wr X).card
            + ∑ X, (C.Cr X).card
            + ∑ X, (C.Be X).card)
          + ∑ X, (if C.full X then 0 else t * (C.S X).card)
          + ∑ X, C.mergeCost X
          + ∑ X, (C.Del X).card := by
      simp only [hR, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [e]
    have h1 :
        (k + 1) *
            (∑ X, (C.F.U X).card + ∑ X, (C.Fo X).card)
          ≤
        (k + 1) * (3 * N) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 :
        t * (∑ X, (C.J X).card
          + ∑ X, (C.Wr X).card
          + ∑ X, (C.Cr X).card
          + ∑ X, (C.Be X).card)
          ≤
        t * (4 * Fintype.card E) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith

  have hsum :
      ∑ X ∈ univ.filter (fun X => C.base X = false), C.cost X
        ≤
      c * (∑ X, R X + ∑ X, k * C.p X) := by
    calc
      ∑ X ∈ univ.filter (fun X => C.base X = false), C.cost X
        ≤
      ∑ X ∈ univ.filter (fun X => C.base X = false),
          c * (R X + k * C.p X) := by
        refine Finset.sum_le_sum fun X hX => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
        have hc := hcost X hX
        simp only [hR]
        calc
          C.cost X ≤ c *
            ((k + 1) * ((C.F.U X).card + (C.Fo X).card)
              + (C.S X).card
              + t * (C.Q X).card
              + t * ((C.J X).card + (C.Wr X).card
                + (C.Cr X).card + (C.Be X).card)
              + k * C.p X
              + (if C.full X then 0 else t * (C.S X).card)
              + C.mergeCost X + (C.Del X).card) := hc
          _ = c * (R X + k * C.p X) := by ring
      _ ≤ ∑ X, c * (R X + k * C.p X) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = c * (∑ X, R X + ∑ X, k * C.p X) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]

  calc
    (k - 1) *
        ∑ X ∈ univ.filter (fun X => C.base X = false), C.cost X
      ≤
    (k - 1) * (c * (∑ X, R X + ∑ X, k * C.p X)) :=
      Nat.mul_le_mul_left _ hsum
    _ =
    c * ((k - 1) * ∑ X, R X
      + (k - 1) * ∑ X, k * C.p X) := by ring
    _ ≤
    c * (
      (k - 1) *
        ((3 * k + 7) * N
          + 5 * t * (Fintype.card E + 1)
          + M0 + Fintype.card E)
      + (3 * k * N + (k - 1) * N)) := by
      apply Nat.mul_le_mul_left
      exact Nat.add_le_add
        (Nat.mul_le_mul_left _ hRsum) hp
    _ ≤
    c * (
      (k - 1) *
        ((3 * k + 8) * N
          + 6 * t * (Fintype.card E + 1)
          + M0)
      + 3 * k * N) := by
      have ht1 : 1 ≤ t :=
        le_trans (by norm_num) (le_trans h.two_le_k h.k_le_t)
      have hE1 :
          Fintype.card E + 1 ≤
            t * (Fintype.card E + 1) :=
        Nat.le_mul_of_pos_left _ ht1
      apply Nat.mul_le_mul_left
      have h1 :
          (3 * k + 7) * N
              + 5 * t * (Fintype.card E + 1)
              + M0 + Fintype.card E + N
            ≤
          (3 * k + 8) * N
              + 6 * t * (Fintype.card E + 1)
              + M0 := by
        nlinarith
      have h2 := Nat.mul_le_mul_left (k - 1) h1
      nlinarith

end Frontier.CostAggregate.CallCounters
