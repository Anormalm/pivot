open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

section CertPullCorrectness

variable {B : WLab G s} {S : Finset (Fin G.n)}
  {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)}
  {B'0 : WLab G s}
  {σ : LState G s p} {S0 : Finset (Fin G.n)}
  {Bi : WLab G s} {D1 : DS G s}

theorem Si_facts_cert_candidate
    (h : LInv G s B S d0 d1 P0 B'0 σ)
    (hpull : CertPullSpec G s σ B S0 Bi D1)
    {x : Fin G.n} (hx : x ∈ expand σ S0 Bi) :
    (x ∈ Aset G s B S d1 P0 ∧ x ∉ σ.U ∧
      σ.B' ≤ dis (s := s) x) ∧ σ.d x < Bi := by
  rcases mem_expand.mp hx with hx0 | ⟨j, -, -, hxP, hxlt⟩
  · obtain ⟨k, hk, hklt⟩ := hpull.selected x hx0
    obtain ⟨hA, hU, hB, -⟩ := h.keys x k hk
    exact ⟨⟨hA, hU, hB⟩,
      lt_of_le_of_lt (h.storedGe x k hk) hklt⟩
  · exact ⟨h.Pmem j x hxP, hxlt⟩

theorem certified_mem_expand_cert_candidate
    (h : LInv G s B S d0 d1 P0 B'0 σ)
    (hpull : CertPullSpec G s σ B S0 Bi D1)
    {y : Fin G.n} (hc : Certified G s σ y)
    (hlt : dis (s := s) y < Bi) :
    y ∈ expand σ S0 Bi := by
  obtain ⟨hyc, hc⟩ := hc
  rcases hc with hkey | ⟨j, hyP, k, hk, hkle⟩
  · exact mem_expand.mpr
      (Or.inl (hpull.coverExact y hyc hkey hlt))
  · have hpj : σ.piv j ∈ S0 :=
      hpull.coverPivot j y k hyP hyc hk hkle hlt
    have hpP := (h.pivots j ⟨y, hyP⟩).1
    exact mem_expand.mpr
      (Or.inr ⟨j, hpj, hpP, hyP, by rw [hyc]; exact hlt⟩)

theorem UKi_sub_cert_candidate
    (h : LInv G s B S d0 d1 P0 B'0 σ)
    (hpull : CertPullSpec G s σ B S0 Bi D1)
    {v : Fin G.n}
    (hv : v ∈ Utilde Bi (expand σ S0 Bi : Set (Fin G.n))) :
    v ∈ Aset G s B S d1 P0 ∧ v ∉ σ.U ∧
      σ.B' ≤ dis (s := s) v := by
  obtain ⟨hvlt, z, hz, hzv⟩ := hv
  obtain ⟨⟨hzA, -, hzB⟩, -⟩ :=
    Si_facts_cert_candidate h hpull hz
  have hvB : dis (s := s) v < B :=
    lt_of_lt_of_le hvlt hpull.bound
  have hvA : v ∈ Aset G s B S d1 P0 :=
    Aset_closure hzA (UK_closure hzA.1 hzv hvB) hzv
  have hge : σ.B' ≤ dis (s := s) v := hzB.trans hzv.dis_le
  exact ⟨hvA,
    fun hvU => absurd (h.U_below v hvU) (not_lt.mpr hge), hge⟩

theorem step_pre_cert_candidate
    (hpre : CallPre B S d0)
    (hfp : FPContract B S d0 d1 p P0 Q W)
    (h : LInv G s B S d0 d1 P0 B'0 σ)
    (hpull : CertPullSpec G s σ B S0 Bi D1) :
    CallPre Bi (expand σ S0 Bi) σ.d where
  walk := h.walk
  claimC := by
    intro v hvlt hvnot
    have hvB : dis (s := s) v < B :=
      lt_of_lt_of_le hvlt hpull.bound
    by_cases hvUK : v ∈ Utilde B (S : Set (Fin G.n))
    · by_cases hvA : v ∈ Aset G s B S d1 P0
      · by_cases hvU : v ∈ σ.U
        · exact h.U_complete v hvU
        · obtain ⟨y, hyc, hyv⟩ := h.certified v hvA hvU
          have hyS := certified_mem_expand_cert_candidate
            h hpull hyc (lt_of_le_of_lt hyv.dis_le hvlt)
          exact absurd ⟨hvlt, y, hyS, hyv⟩ hvnot
      · have hc := (Wc_complete hfp hvUK hvA).2
        exact complete_of_le hc (h.mono v) h.walk.sound
    · have hc := hpre.claimC v hvB hvUK
      exact complete_of_le hc
        ((h.mono v).trans (hfp.le v)) h.walk.sound
  frontier := by
    intro v hv
    obtain ⟨hvA, hvU, -⟩ :=
      UKi_sub_cert_candidate h hpull hv
    obtain ⟨y, hyc, hyv⟩ := h.certified v hvA hvU
    exact Or.inr ⟨y,
      certified_mem_expand_cert_candidate h hpull hyc
        (lt_of_le_of_lt hyv.dis_le hv.1),
      hyc.1, hyv⟩
  inRange := fun x hx =>
    (Si_facts_cert_candidate h hpull hx).2

theorem pull_rest_some_cert_candidate
    (hpull : CertPullSpec G s σ B S0 Bi D1)
    {y : Fin G.n} {k : WLab G s}
    (hk : D1 y = some k) :
    σ.D y = some k ∧ y ∉ S0 := by
  rw [hpull.rest y] at hk
  split_ifs at hk with hy
  exact ⟨hk, hy⟩

theorem pull_rest_keep_cert_candidate
    (hpull : CertPullSpec G s σ B S0 Bi D1)
    {y : Fin G.n} (hy : y ∉ S0) :
    D1 y = σ.D y := by
  rw [hpull.rest y, if_neg hy]

end CertPullCorrectness

end BM
end CHD
end Frontier
