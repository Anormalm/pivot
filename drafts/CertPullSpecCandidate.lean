/-!
# Candidate weaker pull contract for BMSSP correctness

Research draft: isolate the exact PullSpec properties used by BM.lean's
correctness proof.

The existing PullSpec requires:
  y in S0 <-> D[y]=some k and k < Bi.

The proofs of Si_facts / certified_mem_expand use less:
- soundness of selected keys;
- coverage of exact/certifying keys;
- ordinary rest/bound/nonempty facts.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- Pull contract tailored to the BMSSP correctness proof.

selected: every returned key is genuinely stored below Bi.
coverExact: enough for Certified's direct-key case.
coverPivot: enough for Certified's group-certificate case.

Unlike PullSpec, arbitrary non-certifying D entries below Bi need not be returned. -/
structure CertPullSpec
    {p : ℕ} (σ : LState G s p) (Bd : WLab G s)
    (S0 : Finset (Fin G.n)) (Bi : WLab G s) (D1 : DS G s) : Prop where
  selected :
    ∀ y, y ∈ S0 → ∃ k, σ.D y = some k ∧ k < Bi
  coverExact :
    ∀ y, Complete σ.d y →
      σ.D y = some (dis (s := s) y) →
      dis (s := s) y < Bi →
      y ∈ S0
  coverPivot :
    ∀ j y k,
      y ∈ σ.P j →
      Complete σ.d y →
      σ.D (σ.piv j) = some k →
      k ≤ dis (s := s) y →
      dis (s := s) y < Bi →
      σ.piv j ∈ S0
  rest :
    ∀ y, D1 y = if y ∈ S0 then none else σ.D y
  bound : Bi ≤ Bd
  nonempty : (∃ y, σ.D y ≠ none) → S0.Nonempty

/-- The old exact PullSpec implies the weaker certificate-oriented contract. -/
theorem PullSpec.toCertPullSpec
    {p : ℕ} {σ : LState G s p}
    {Bd : WLab G s} {S0 : Finset (Fin G.n)}
    {Bi : WLab G s} {D1 : DS G s}
    (h : PullSpec σ.D Bd S0 Bi D1) :
    CertPullSpec (G := G) (s := s) σ Bd S0 Bi D1 where
  selected := by
    intro y hy
    exact (h.pulled y).mp hy
  coverExact := by
    intro y _ hkey hlt
    exact (h.pulled y).mpr ⟨_, hkey, hlt⟩
  coverPivot := by
    intro j y k _ _ hk _ hlt
    exact (h.pulled _).mpr ⟨k, hk, hlt⟩
  rest := h.rest
  bound := h.bound
  nonempty := h.nonempty

end BM
end CHD
end Frontier
