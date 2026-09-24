open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

theorem step_post_cert_candidate (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    (h : LInv G s B S d0 d1 P0 B'0 σ) (hne : ¬ σ.D.IsEmpty) (hpull : CertPullSpec (G := G) (s := s) σ B S0 Bi D1)
    {cap : ℕ} {B'i : WLab G s} {Ui : Finset (Fin G.n)} {Di : DS G s} {d1' : Labels G s}
    (hpost : CallPost G s Bi (expand σ S0 Bi) σ.d cap (B'i, Ui, Di, d1'))
    {L : List (Fin G.m)} (hL : Enumerates G L Ui) {piv' : Fin p → Fin G.n}
    (hres : Reselect σ Ui
      (L.foldl (relaxIns G s B (some Bi)) (d1', (D1.merge Di).deleteSet Ui)).1 piv') :
    LInv G s B S d0 d1 P0 B'0
      { d := (L.foldl (relaxIns G s B (some Bi)) (d1', (D1.merge Di).deleteSet Ui)).1
        D := insertMany G s
              (L.foldl (relaxIns G s B (some Bi)) (d1', (D1.merge Di).deleteSet Ui)).2
              (reselected σ Ui piv')
              (L.foldl (relaxIns G s B (some Bi)) (d1', (D1.merge Di).deleteSet Ui)).1
        P := fun j => σ.P j \ Ui
        piv := piv'
        U := σ.U ∪ Ui
        B' := B'i } := by
  set Si := expand σ S0 Bi with hSi
  set st0 : Labels G s × DS G s := (d1', (D1.merge Di).deleteSet Ui) with hst0
  set st2 := L.foldl (relaxIns G s B (some Bi)) st0 with hst2
  set d2 := st2.1 with hd2
  set Dn := insertMany G s st2.2 (reselected σ Ui piv') d2 with hDn
  have hsubpre : CallPre Bi Si σ.d := step_pre_cert_candidate hpre hfp h hpull
  have hBiB : Bi ≤ B := hpull.bound
  -- Step 3
  have hB'Bi : σ.B' ≤ Bi := by
    obtain ⟨y, hy⟩ := hpull.nonempty (by
      by_contra hc; push_neg at hc; exact hne hc)
    obtain ⟨k, hk, hklt⟩ := hpull.selected y hy
    obtain ⟨-, -, hB, -⟩ := h.keys y k hk
    exact (hB.trans ((h.walk.sound y).trans (h.storedGe y k hk))).trans hklt.le
  have hB'ge : σ.B' ≤ B'i :=
    hpost.B'_ge σ.B' hB'Bi (fun x hx => (Si_facts_cert_candidate h hpull hx).1.2.2)
  have hB'iBi : B'i ≤ Bi := hpost.B'_le
  have hUi : ∀ u ∈ Ui, u ∈ Aset G s B S d1 P0 ∧ u ∉ σ.U ∧ dis (s := s) u < B'i ∧
      Complete d1' u := by
    intro u hu
    have hu' := (hpost.U_eq u).mp hu
    have huBi : u ∈ Utilde Bi (Si : Set (Fin G.n)) := ⟨lt_of_lt_of_le hu'.1 hB'iBi, hu'.2⟩
    obtain ⟨hA, hU, -⟩ := UKi_sub_cert_candidate h hpull huBi
    exact ⟨hA, hU, hu'.1, hpost.U_complete u hu⟩
  have hAbelow : ∀ v ∈ Aset G s B S d1 P0, dis (s := s) v < B'i → v ∈ σ.U ∨ v ∈ Ui := by
    intro v hvA hvlt
    by_cases hvU : v ∈ σ.U
    · exact Or.inl hvU
    · obtain ⟨y, hyc, hyv⟩ := h.certified v hvA hvU
      have hyS : y ∈ Si := certified_mem_expand_cert_candidate h hpull hyc
        (lt_of_le_of_lt hyv.dis_le (lt_of_lt_of_le hvlt hB'iBi))
      exact Or.inr ((hpost.U_eq v).mpr ⟨hvlt, y, hyS, hyv⟩)
  have hAge : ∀ v ∈ Aset G s B S d1 P0, v ∉ σ.U → v ∉ Ui → B'i ≤ dis (s := s) v := by
    intro v hvA hvU hvUi
    by_contra hc
    rcases hAbelow v hvA (not_le.mp hc) with h1 | h1
    · exact hvU h1
    · exact hvUi h1
  -- labels
  have hw1 : WalkInv d1' := hpost.walk
  have hle1 : ∀ v, d1' v ≤ σ.d v := hpost.mono
  have hle2 : ∀ v, d2 v ≤ d1' v := fun v => foldl_relaxIns_fst_le B (some Bi) L st0 v
  have hw2 : WalkInv d2 := foldl_relaxIns_walk B (some Bi) L st0 hw1
  have hle2d1 : ∀ v, d2 v ≤ d1 v := fun v => (hle2 v).trans ((hle1 v).trans (h.mono v))
  have hcomp2 : ∀ v, Complete σ.d v → Complete d2 v :=
    fun v hv => complete_of_le hv ((hle2 v).trans (hle1 v)) hw2.sound
  have hcomp2' : ∀ v, Complete d1' v → Complete d2 v :=
    fun v hv => complete_of_le hv (hle2 v) hw2.sound
  have hLsrc : ∀ e ∈ L, Complete st0.1 (G.src e) := by
    intro e he
    have hsrc : G.src e ∈ Ui := by simpa using (hL.2 e).mp he
    exact (hUi _ hsrc).2.2.2
  -- stored values dominate labels
  have hsg0 : StoredGe G s st0.1 st0.2 := by
    have hD1 : StoredGe G s d1' D1 := by
      intro y k hk
      obtain ⟨hk', -⟩ := pull_rest_some_cert_candidate hpull hk
      exact (hle1 y).trans (h.storedGe y k hk')
    have hDi : StoredGe G s d1' Di := fun y k hk => (hpost.keys y k hk).2.2.2.1
    exact storedGe_deleteSet Ui (storedGe_merge hD1 hDi)
  have hsg2 : StoredGe G s d2 st2.2 := foldl_relaxIns_storedGe B (some Bi) L st0 hsg0
  have hsgn : StoredGe G s d2 Dn := storedGe_insertMany _ hsg2
  -- exact keys persist
  have hexact : ∀ y k, st0.2 y = some k → k ≤ dis (s := s) y → Dn y = some (dis (s := s) y) := by
    intro y k hk hkle
    obtain ⟨k2, hk2, hk2le⟩ : ∃ k', st2.2 y = some k' ∧ k' ≤ k :=
      foldl_relaxIns_snd_le B (some Bi) L st0 y k hk
    obtain ⟨k3, hk3, hk3le⟩ : ∃ k', Dn y = some k' ∧ k' ≤ k2 :=
      insertMany_le (reselected σ Ui piv') d2 hk2
    have hge : dis (s := s) y ≤ k3 := (hw2.sound y).trans (hsgn y k3 hk3)
    rw [hk3, le_antisymm (hk3le.trans (hk2le.trans hkle)) hge]
  have hst0_apply : ∀ y, st0.2 y = if y ∈ Ui then none else DS.mergeVal (D1 y) (Di y) :=
    fun y => rfl
  have hDi_exact : ∀ y, Di y = some (dis (s := s) y) → Dn y = some (dis (s := s) y) := by
    intro y hy
    have hyUi : y ∉ Ui := (hpost.keys y _ hy).2.1
    obtain ⟨k, hk, hkle⟩ := DSx.mergeVal_le_right (a := D1 y) hy
    have hst : st0.2 y = some k := by rw [hst0_apply, if_neg hyUi]; exact hk
    exact hexact y k hst hkle
  have hkeep : ∀ y k, st0.2 y = some k → ∃ k', Dn y = some k' ∧ k' ≤ k := by
    intro y k hk
    obtain ⟨k2, hk2, hk2le⟩ : ∃ k', st2.2 y = some k' ∧ k' ≤ k :=
      foldl_relaxIns_snd_le B (some Bi) L st0 y k hk
    obtain ⟨k3, hk3, hk3le⟩ : ∃ k', Dn y = some k' ∧ k' ≤ k2 :=
      insertMany_le (reselected σ Ui piv') d2 hk2
    exact ⟨k3, hk3, hk3le.trans hk2le⟩
  -- the key property of the new structure
  let Pk : Fin G.n → WLab G s → Prop := fun y k =>
    y ∈ Aset G s B S d1 P0 ∧ y ∉ σ.U ∧ y ∉ Ui ∧ B'i ≤ dis (s := s) y ∧ k < B
  have hPk0 : ∀ y k, st0.2 y = some k → Pk y k := by
    intro y k hk
    rw [hst0_apply] at hk
    split_ifs at hk with hyUi
    rcases DSx.mergeVal_cases _ _ _ hk with h1 | h1
    · obtain ⟨hk', -⟩ := pull_rest_some_cert_candidate hpull h1
      obtain ⟨hA, hU, -, hkB⟩ := h.keys y k hk'
      exact ⟨hA, hU, hyUi, hAge y hA hU hyUi, hkB⟩
    · obtain ⟨hyUK, -, hB', -, hkBi⟩ := hpost.keys y k h1
      obtain ⟨hA, hU, -⟩ := UKi_sub_cert_candidate h hpull hyUK
      exact ⟨hA, hU, hyUi, hB', lt_of_lt_of_le hkBi hBiB⟩
  have hPkL : ∀ e ∈ L, ∀ d' : Labels G s, Sound d' → (∀ v, d' v ≤ st0.1 v) →
      Complete d' (G.src e) → ValidRelax G s d' B e →
      (∀ b, some Bi = some b → b ≤ ext (dis (s := s) (G.src e)) e) →
      Pk (G.dst e) (ext (dis (s := s) (G.src e)) e) := by
    intro e he d' hs' hd' hsrc' hv hlo
    have hsrc : G.src e ∈ Ui := by simpa using (hL.2 e).mp he
    obtain ⟨hsA, -, hslt, -⟩ := hUi _ hsrc
    have hd'0 : ∀ v, d' v ≤ d0 v := fun v =>
      (hd' v).trans ((hle1 v).trans ((h.mono v).trans (hfp.le v)))
    have hvUK : G.dst e ∈ Utilde B (S : Set (Fin G.n)) :=
      mem_UK_of_valid hpre hs' hd'0 hsA.1 hsrc' hv
    have hcandB : ext (dis (s := s) (G.src e)) e < B := by
      rw [← hsrc']; exact hv.2
    have hloBi : Bi ≤ ext (dis (s := s) (G.src e)) e := hlo Bi rfl
    have hsfin : dis (s := s) (G.src e) ≠ ⊤ := ne_top_of_lt hsA.1.1
    have htight : Complete d' (G.dst e) → OnPath (s := s) (G.src e) (G.dst e) := by
      intro hc
      have hle := hv.1
      rw [hsrc', hc] at hle
      exact onPath_of_tight (le_antisymm hle (dis_le_ext_dis hsfin)) hsfin
    have hvA : G.dst e ∈ Aset G s B S d1 P0 := by
      by_contra hvA
      have hc1 := (Wc_complete hfp hvUK hvA).2
      have hc' : Complete d' (G.dst e) :=
        complete_of_le hc1 ((hd' _).trans ((hle1 _).trans (h.mono _))) hs'
      exact hvA (Aset_closure hsA hvUK (htight hc'))
    have hnotin : ∀ w, Complete d' w → dis (s := s) w < B'i → G.dst e ≠ w := by
      intro w hwc hwlt hw
      subst hw
      have hle := hv.1
      rw [hwc, hsrc'] at hle
      have : ext (dis (s := s) (G.src e)) e < Bi := lt_of_le_of_lt hle (lt_of_lt_of_le hwlt hB'iBi)
      exact absurd hloBi (not_le.mpr this)
    have hvU : G.dst e ∉ σ.U := by
      intro hvU
      exact hnotin _ (complete_of_le (h.U_complete _ hvU) ((hd' _).trans (hle1 _)) hs')
        (lt_of_lt_of_le (h.U_below _ hvU) hB'ge) rfl
    have hvUi : G.dst e ∉ Ui := by
      intro hvUi
      obtain ⟨-, -, hlt', hc'⟩ := hUi _ hvUi
      exact hnotin _ (complete_of_le hc' (hd' _) hs') hlt' rfl
    exact ⟨hvA, hvU, hvUi, hAge _ hvA hvU hvUi, hcandB⟩
  have hPk2 : ∀ y k, st2.2 y = some k → Pk y k :=
    foldl_relaxIns_keys B (some Bi) Pk L st0 hw1.sound hLsrc hPk0 hPkL
  have hPkn : ∀ y k, Dn y = some k → Pk y k := by
    intro y k hk
    rcases insertMany_key_cases hk with h1 | ⟨hy, rfl⟩
    · exact hPk2 y k h1
    · obtain ⟨j, rfl, hpUi, hne'⟩ := mem_reselected.mp hy
      obtain ⟨hmem, -⟩ := hres.resel j hpUi hne'
      obtain ⟨hPj, hnotUi⟩ := Finset.mem_sdiff.mp hmem
      obtain ⟨hA, hU, -⟩ := h.Pmem j _ hPj
      refine ⟨hA, hU, hnotUi, hAge _ hA hU hnotUi, ?_⟩
      have hS : piv' j ∈ S := (hfp.groups j).2 (h.Psub j hPj)
      exact lt_of_le_of_lt ((hle2d1 _).trans (hfp.le _)) (hpre.inRange _ hS)
  refine
    { walk := hw2
      mono := hle2d1
      confined := ?_
      storedGe := hsgn
      keys := ?_
      Pmem := ?_
      Psub := fun j => (Finset.sdiff_subset).trans (h.Psub j)
      U_A := ?_
      U_complete := ?_
      U_below := ?_
      A_below := ?_
      certified := ?_
      pivots := ?_
      B'_le := hB'iBi.trans hBiB
      B'_ge := h.B'_ge.trans hB'ge
      scanned := ?_ }
  · -- confined
    intro v hv
    change d2 v ≠ d0 v at hv
    by_cases h2 : d2 v = d1' v
    · rw [h2] at hv
      by_cases h1 : d1' v = σ.d v
      · rw [h1] at hv; exact h.confined v hv
      · exact (UKi_sub_cert_candidate h hpull (hpost.confined v h1)).1.1
    · obtain ⟨hlt, hkey⟩ := foldl_relaxIns_changed B (some Bi) L st0 v h2
      by_contra hvUK
      have hc := hpre.claimC v (lt_of_le_of_lt (hw2.sound v) hkey) hvUK
      have : d2 v < dis (s := s) v := by
        calc d2 v < d1' v := hlt
          _ ≤ d0 v := (hle1 v).trans ((h.mono v).trans (hfp.le v))
          _ = dis (s := s) v := hc
      exact absurd (hw2.sound v) (not_le.mpr this)
  · -- keys
    intro y k hk
    obtain ⟨hA, hU, hUi', hB', hkB⟩ := hPkn y k hk
    exact ⟨hA, fun hm => (Finset.mem_union.mp hm).elim hU hUi', hB', hkB⟩
  · -- Pmem
    intro j y hy
    obtain ⟨hyP, hyUi⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨hA, hU, -⟩ := h.Pmem j y hyP
    exact ⟨hA, fun hm => (Finset.mem_union.mp hm).elim hU hyUi, hAge y hA hU hyUi⟩
  · -- U_A
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact h.U_A u hu
    · exact (hUi u hu).1
  · -- U_complete
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact hcomp2 u (h.U_complete u hu)
    · exact hcomp2' u (hUi u hu).2.2.2
  · -- U_below
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact lt_of_lt_of_le (h.U_below u hu) hB'ge
    · exact (hUi u hu).2.2.1
  · -- A_below
    intro v hvA hvlt
    rcases hAbelow v hvA hvlt with h1 | h1
    · exact Finset.mem_union_left _ h1
    · exact Finset.mem_union_right _ h1
  · -- certified (S2 Step 4, J3)
    intro v hvA hvnot
    have hvU : v ∉ σ.U := fun hm => hvnot (Finset.mem_union_left _ hm)
    have hvUi : v ∉ Ui := fun hm => hvnot (Finset.mem_union_right _ hm)
    have hvB : dis (s := s) v < B := hvA.1.1
    by_cases hcase : ∃ x ∈ Ui, OnPath (s := s) x v
    · -- Case 1: the canonical path leaves U_i through an exit edge
      obtain ⟨x, hxUi, hxv⟩ := hcase
      obtain ⟨e, hsUi, hdUi, -, hbv, htight⟩ := hxv.exists_exit (Ui : Set (Fin G.n)) hxUi hvUi
      obtain ⟨-, -, hslt, hsc⟩ := hUi _ hsUi
      have hbB : dis (s := s) (G.dst e) < B := lt_of_le_of_lt hbv.dis_le hvB
      by_cases hbBi : dis (s := s) (G.dst e) < Bi
      · have hsUK : G.src e ∈ Utilde Bi (Si : Set (Fin G.n)) := by
          have := (hpost.U_eq _).mp hsUi
          exact ⟨lt_of_lt_of_le this.1 hB'iBi, this.2⟩
        have hab : OnPath (s := s) (G.src e) (G.dst e) :=
          onPath_of_tight htight.symm (ne_top_of_lt hslt)
        have hbUK : G.dst e ∈ Utilde Bi (Si : Set (Fin G.n)) := UK_closure hsUK hab hbBi
        obtain ⟨y', hy'D, hy'c, hy'v⟩ := hpost.certified _ hbUK hdUi
        exact ⟨y', ⟨hcomp2' y' hy'c, Or.inl (hDi_exact y' hy'D)⟩, hy'v.trans hbv⟩
      · have he : e ∈ L := (hL.2 e).mpr (by simpa using hsUi)
        obtain ⟨hbc, hbk⟩ := foldl_relaxIns_canonical (s := s) B (some Bi) L st0 e he hw1
          hsc htight hbB
        obtain ⟨k, hk, hkle⟩ := hbk (fun b hb => by
          simp only [Option.some.injEq] at hb; subst hb; exact not_lt.mp hbBi)
        obtain ⟨k3, hk3, hk3le⟩ : ∃ k', Dn (G.dst e) = some k' ∧ k' ≤ k :=
          insertMany_le (reselected σ Ui piv') d2 hk
        have hge : dis (s := s) (G.dst e) ≤ k3 := (hw2.sound _).trans (hsgn _ k3 hk3)
        refine ⟨G.dst e, ⟨hbc, Or.inl ?_⟩, hbv⟩
        show Dn (G.dst e) = _
        rw [hk3, le_antisymm (hk3le.trans hkle) hge]
    · -- Case 2: the canonical path avoids U_i
      push_neg at hcase
      obtain ⟨y, ⟨hyc, hyc'⟩, hyv⟩ := h.certified v hvA hvU
      have hyUi : y ∉ Ui := fun hm => hcase y hm hyv
      by_cases hyS : y ∈ Si
      · have hyUK : y ∈ Utilde Bi (Si : Set (Fin G.n)) := S_sub_of_pre hsubpre y hyS
        obtain ⟨y', hy'D, hy'c, hy'v⟩ := hpost.certified y hyUK hyUi
        exact ⟨y', ⟨hcomp2' y' hy'c, Or.inl (hDi_exact y' hy'D)⟩, hy'v.trans hyv⟩
      · have hyS0 : y ∉ S0 := fun hm => hyS (mem_expand.mpr (Or.inl hm))
        rcases hyc' with hkey | ⟨j, hyP, k, hk, hkle⟩
        · obtain ⟨k0, hk0, hk0le⟩ := DSx.mergeVal_le_left (b := Di y) hkey
          have : st0.2 y = some k0 := by
            rw [hst0_apply, if_neg hyUi, pull_rest_keep_cert_candidate hpull hyS0]
            exact hk0
          exact ⟨y, ⟨hcomp2 y hyc, Or.inl (hexact y k0 this hk0le)⟩, hyv⟩
        · have hyP' : y ∈ σ.P j \ Ui := Finset.mem_sdiff.mpr ⟨hyP, hyUi⟩
          refine ⟨y, ⟨hcomp2 y hyc, Or.inr ⟨j, hyP', ?_⟩⟩, hyv⟩
          by_cases hpUi : σ.piv j ∈ Ui
          · obtain ⟨hmem, hmin⟩ := hres.resel j hpUi ⟨y, hyP'⟩
            have hrs : piv' j ∈ reselected σ Ui piv' :=
              mem_reselected.mpr ⟨j, rfl, hpUi, ⟨y, hyP'⟩⟩
            obtain ⟨k', hk', hk'le⟩ : ∃ k', Dn (piv' j) = some k' ∧ k' ≤ d2 (piv' j) :=
              insertMany_mem (D := st2.2) d2 hrs
            refine ⟨k', hk', hk'le.trans ?_⟩
            have := hmin y hyP'
            rw [hcomp2 y hyc] at this
            exact this
          · have hkeepj : piv' j = σ.piv j := hres.keep j (fun hc => hpUi hc.1)
            show ∃ k, Dn (piv' j) = some k ∧ k ≤ dis (s := s) y
            rw [hkeepj]
            by_cases hpS0 : σ.piv j ∈ S0
            · have hpSi : σ.piv j ∈ Si := mem_expand.mpr (Or.inl hpS0)
              obtain ⟨k'', hk'', hk''le⟩ := hpost.S_keys _ hpSi hpUi
              obtain ⟨k0, hk0, hk0le⟩ := DSx.mergeVal_le_right (a := D1 (σ.piv j)) hk''
              have hst : st0.2 (σ.piv j) = some k0 := by
                rw [hst0_apply, if_neg hpUi]
                exact hk0
              obtain ⟨k', hk', hk'le⟩ := hkeep _ _ hst
              refine ⟨k', hk', hk'le.trans (hk0le.trans (hk''le.trans ?_))⟩
              exact (h.storedGe _ k hk).trans hkle
            · obtain ⟨k0, hk0, hk0le⟩ := DSx.mergeVal_le_left (b := Di (σ.piv j)) hk
              have hst : st0.2 (σ.piv j) = some k0 := by
                rw [hst0_apply, if_neg hpUi, pull_rest_keep_cert_candidate hpull hpS0]
                exact hk0
              obtain ⟨k', hk', hk'le⟩ := hkeep _ _ hst
              exact ⟨k', hk', hk'le.trans (hk0le.trans hkle)⟩
  · -- pivots (J4)
    intro j hj
    by_cases hpUi : σ.piv j ∈ Ui
    · obtain ⟨hmem, -⟩ := hres.resel j hpUi hj
      have hrs : piv' j ∈ reselected σ Ui piv' := mem_reselected.mpr ⟨j, rfl, hpUi, hj⟩
      obtain ⟨k', hk', -⟩ : ∃ k', Dn (piv' j) = some k' ∧ k' ≤ d2 (piv' j) :=
        insertMany_mem (D := st2.2) d2 hrs
      refine ⟨hmem, ?_⟩
      show Dn (piv' j) ≠ none
      rw [hk']; simp
    · have hkeepj : piv' j = σ.piv j := hres.keep j (fun hc => hpUi hc.1)
      have hPj : (σ.P j).Nonempty := hj.mono Finset.sdiff_subset
      obtain ⟨hpP, hpD⟩ := h.pivots j hPj
      refine ⟨?_, ?_⟩
      · show piv' j ∈ σ.P j \ Ui
        rw [hkeepj]; exact Finset.mem_sdiff.mpr ⟨hpP, hpUi⟩
      show Dn (piv' j) ≠ none
      rw [hkeepj]
      obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hpD
      by_cases hpS0 : σ.piv j ∈ S0
      · have hpSi : σ.piv j ∈ Si := mem_expand.mpr (Or.inl hpS0)
        obtain ⟨k'', hk'', -⟩ := hpost.S_keys _ hpSi hpUi
        obtain ⟨k0, hk0, -⟩ := DSx.mergeVal_le_right (a := D1 (σ.piv j)) hk''
        have hst : st0.2 (σ.piv j) = some k0 := by
          rw [hst0_apply, if_neg hpUi]
          exact hk0
        obtain ⟨k', hk', -⟩ := hkeep _ _ hst
        rw [hk']; simp
      · obtain ⟨k0, hk0, -⟩ := DSx.mergeVal_le_left (b := Di (σ.piv j)) hk
        have hst : st0.2 (σ.piv j) = some k0 := by
          rw [hst0_apply, if_neg hpUi, pull_rest_keep_cert_candidate hpull hpS0]
          exact hk0
        obtain ⟨k', hk', -⟩ := hkeep _ _ hst
        rw [hk']; simp
  · -- scanned (S2 Lemma S2.4)
    intro u hu e he hB
    rcases Finset.mem_union.mp hu with hu | hu
    · exact ((hle2 _).trans (hle1 _)).trans (h.scanned u hu e he hB)
    · have heL : e ∈ L := (hL.2 e).mpr (by rw [he]; exact hu)
      have := foldl_relaxIns_scan (s := s) B (some Bi) L st0 e heL hw1
        (by rw [he]; exact (hUi u hu).2.2.2) (by rw [he]; exact hB)
      rw [he] at this
      exact this


end BM
end CHD
end Frontier
