/-!
# Candidate own-home / final-residual lemmas for C-HD

Status: UNCOMPILED source-aligned draft.
Targets:
  formal/lean/Frontier/CHD/CrBe.lean
  formal/lean/Frontier/CHD/CostLe.lean
  possibly BMTrace/CostLog for one child-subset transport lemma.

Upstream snapshot:
  98c53accb47a505482a1781597ae14bf67e81cec
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph Frontier.CHD.Partition

variable {G : Graph} {s : Fin G.n}

namespace BM

/-- Original pivot groups that contain at least one vertex returned by the
parent's final W' region.  This is the record-level proxy for the extra
`none` home colour. -/
noncomputable def ownGroupsOf
    (k : ℕ) (r : CallRec G s (FPData G s)) : ℕ := by
  classical
  exact (groupsOf k r).countP
    (fun g => decide (g.toFinset ∩ r.W').Nonempty)

end BM

variable {τ : ℕ → ℕ} {L0 : ℕ}
variable {lg : BM.Log G s (FPData G s)}
variable (hL : BM.LogInv τ L0 lg)

/-- Desired transport fact.

If `Y` is a direct child of `X), then every vertex returned by `Y`
was accumulated into the loop-returned part of `X`, before the final W'
extension.  Equivalently, parent W' is disjoint from every direct child U.

This is not currently a field of `LogInv`; it should follow from the traced
`LoopLog.root` fact together with the finalization definition of W'.
A proof may be easier at `CallC` derivation level and then transported into
the record log, analogously to `RecFPLog`.
-/
theorem child_U_disjoint_parent_W'_candidate
    {X Y : lg.Call}
    (hpar : (BM.Log.forest hL).parent Y = some X) :
    Disjoint (BM.Log.forest hL).U Y (lg.recOf X).W' := by
  -- TODO: transport from the concrete loop/finalization derivation.
  sorry

/-- A parent-W' vertex has home `none` at a full call.

Reason:
1. W' is part of the parent's returned U, so the foreign-range branch of
   `Ranges.home` is disabled.
2. W' is disjoint from every child returned U, so the direct-child branch is
   disabled.
-/
theorem home_eq_none_of_mem_W'_candidate
    {X : lg.Call} {v : Fin G.n}
    (hvW : v ∈ (lg.recOf X).W')
    (hvU : v ∈ (lg.recOf X).U) :
    homeX hL X v = none := by
  classical
  unfold homeX Density.Ranges.home
  have hnoChild :
      ¬ ∃ Y,
        (BM.Log.forest hL).parent Y = some X ∧
        v ∈ (BM.Log.forest hL).U Y := by
    rintro ⟨Y, hpar, hvY⟩
    exact Finset.disjoint_left.mp
      (child_U_disjoint_parent_W'_candidate hL hpar) hvY hvW
  rw [dif_neg hnoChild]
  -- The second branch requires v ∉ U_X, contradicting hvU.
  rw [dif_neg]
  intro h
  exact h.1 hvU

/-- Candidate full-call residual-group lemma.

Every nonempty group still present after the child loop meets parent W'.

This statement is most naturally first proved inside `callC_cost`, where
the final loop state sigma and the finalization W' are both available:
- `LInv.Pmem`: y in sigma.P j -> y notin sigma.U;
- `Psub` + FP groups: y belongs to original S;
- full call: S subset returned parent U;
- call result: returned parent U = sigma.U union W'.

Hence y must belong to W'.
-/
theorem final_residual_meets_W'_candidate
    {p : ℕ} {P0 : Fin p → Finset (Fin G.n)}
    {σ : BM.LState G s p}
    {W' S Uret : Finset (Fin G.n)}
    (hPsub : ∀ j, σ.P j ⊆ P0 j)
    (hP0S : ∀ j, P0 j ⊆ S)
    (hNotU : ∀ j, ∀ y ∈ σ.P j, y ∉ σ.U)
    (hFullS : S ⊆ Uret)
    (hUret : Uret = σ.U ∪ W') :
    ∀ j, (σ.P j).Nonempty →
      (P0 j ∩ W').Nonempty := by
  classical
  intro j hne
  obtain ⟨y, hy⟩ := hne
  have hyP0 : y ∈ P0 j := hPsub j hy
  have hyS : y ∈ S := hP0S j hyP0
  have hyRet : y ∈ Uret := hFullS hyS
  rw [hUret, Finset.mem_union] at hyRet
  have hyW : y ∈ W' := hyRet.resolve_left (hNotU j y hy)
  exact ⟨y, Finset.mem_inter.mpr ⟨hyP0, hyW⟩⟩

/-- Refined home-colour target for full calls.

Current upstream:
  mkOf <= p + Cr + Be.

Desired strengthening:
  mkOf + ownGroupsOf <= p + Cr + Be.

Per group:
- every child meeting contributes a distinct `some Y` home;
- if the group meets parent W', that contributes the distinct `none` home;
- therefore childMeetCount + ownIndicator <= number of home colours.

Then reuse unchanged:
  Reselect.groups_colors_le
  bich_le_crbe.
-/
theorem mk_own_full_le_candidate
    (k : ℕ) (hk : 2 ≤ k)
    (hF : ∀ q r, (q, r) ∈ lg → RecForest r)
    {X : lg.Call}
    (hfull : (lg.recOf X).B' = (lg.recOf X).B)
    (hUt : ∀ v ∈ Utilde (lg.recOf X).B
        ((lg.recOf X).S : Set (Fin G.n)),
      v ∈ (lg.recOf X).U) :
    BM.mkOf hL k X + BM.ownGroupsOf k (lg.recOf X)
      ≤
    (BM.groupsOf k (lg.recOf X)).length
      + (crOf hL X).card
      + (beOf hL X).card := by
  classical
  -- TODO:
  -- 1. cases hω : (lg.recOf X).fp;
  -- 2. per group inject direct children meeting g as `some Y`;
  -- 3. if g meets W', inject an additional `none` using
  --    home_eq_none_of_mem_W'_candidate;
  -- 4. conclude
  --      meetings(g) + ownIndicator(g)
  --        <= #(g.map (homeX hL X)).toFinset;
  -- 5. sum over groups;
  -- 6. reuse groups_colors_le and bich_le_crbe verbatim.
  sorry

end CHD
end Frontier
