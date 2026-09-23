/-!
# Candidate refined full-call home-colour / Cr-Be bound

Status: source-aligned candidate.
Intended to be checked after HomeOwnColourCandidate.lean.

This isolates the remaining semantic bridge as one explicit hypothesis:
  every parent W' vertex has home = none.

Under that hypothesis, the existing PT-piece colour machinery already
removes the once-per-group term from the EXPENSIVE re-selection charge.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph Frontier.CHD.Partition

variable {G : Graph} {s : Fin G.n}
variable {τ : ℕ → ℕ} {L0 : ℕ}
variable {lg : BM.Log G s (FPData G s)}
variable (hL : BM.LogInv τ L0 lg)

/-- Per-record count of original pivot groups containing at least one
parent-final W' vertex. -/
noncomputable def ownGroupsOfCandidate
    (k : ℕ) (r : BM.CallRec G s (FPData G s)) : ℕ :=
  ((groupsOf k r).map (fun g =>
    if (g.toFinset ∩ r.W').Nonempty then 1 else 0)).sum

/-- Combined meeting + own-home count, written directly as a group sum. -/
noncomputable def mkOwnOfCandidate
    (k : ℕ) (X : lg.Call) : ℕ :=
  ((groupsOf k (lg.recOf X)).map (fun g =>
    (Finset.univ.filter (fun Y =>
      (BM.Log.forest hL).parent Y = some X ∧
      (g.toFinset ∩ (BM.Log.forest hL).U Y).Nonempty)).card
      +
      if (g.toFinset ∩ (lg.recOf X).W').Nonempty then 1 else 0)).sum

/-- The direct definition is exactly mkOf plus the number of groups
meeting parent W'. -/
theorem mkOwn_eq_candidate (k : ℕ) (X : lg.Call) :
    mkOwnOfCandidate hL k X
      =
    mkOf hL k X + ownGroupsOfCandidate k (lg.recOf X) := by
  classical
  unfold mkOwnOfCandidate mkOf ownGroupsOfCandidate
  generalize groupsOf k (lg.recOf X) = gs
  induction gs with
  | nil => simp
  | cons g gs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      omega

/-- Refined full-call colour bound, conditional only on the semantic
fact that parent W' vertices receive the extra none home.

This theorem reuses upstream:
- Ranges.card_children_meeting_le (when no own home is present);
- candidate card_children_meeting_add_one_le_of_none (when it is);
- Reselect.groups_colors_le;
- bich_le_crbe.
-/
theorem mkOwn_full_le_of_W'_none_candidate
    (k : ℕ) (hk : 2 ≤ k)
    (hF : ∀ q r, (q, r) ∈ lg → RecForest r)
    {X : lg.Call}
    (hfull : (lg.recOf X).B' = (lg.recOf X).B)
    (hUt : ∀ v ∈ Utilde (lg.recOf X).B
        ((lg.recOf X).S : Set (Fin G.n)),
      v ∈ (lg.recOf X).U)
    (hWnone : ∀ v ∈ (lg.recOf X).W',
      homeX hL X v = none) :
    mkOwnOfCandidate hL k X
      ≤
    (groupsOf k (lg.recOf X)).length
      + (crOf hL X).card
      + (beOf hL X).card := by
  classical
  unfold mkOwnOfCandidate groupsOf
  cases hω : (lg.recOf X).fp with
  | none =>
      simp
  | some ω =>
      simp only
      have hFX := hF _ _ (BM.recOf_mem X)

      have h1 :
          ((forestGroups (lg.recOf X).S (lg.recOf X).Q k ω.trees).map
            (fun g =>
              (Finset.univ.filter (fun Y =>
                (BM.Log.forest hL).parent Y = some X ∧
                (g.toFinset ∩ (BM.Log.forest hL).U Y).Nonempty)).card
              +
              if (g.toFinset ∩ (lg.recOf X).W').Nonempty
                then 1 else 0)).sum
          ≤
          ((forestGroups (lg.recOf X).S (lg.recOf X).Q k ω.trees).map
            (fun g => (g.map (homeX hL X)).toFinset.card)).sum := by
        refine Reselect.map_sum_le _ _ _ (fun g _ => ?_)
        have heq :
            g.toFinset.image
                ((BM.Log.ranges hL).home
                  (fun v => dis (s := s) v) X)
              =
            (g.map (homeX hL X)).toFinset := by
          ext z
          simp [homeX]
        by_cases hown :
            (g.toFinset ∩ (lg.recOf X).W').Nonempty
        · simp only [if_pos hown]
          obtain ⟨v, hv⟩ := hown
          obtain ⟨hvG, hvW⟩ := Finset.mem_inter.mp hv
          have hnone :
              ∃ z ∈ g.toFinset,
                (BM.Log.ranges hL).home
                  (fun v => dis (s := s) v) X z = none := by
            refine ⟨v, hvG, ?_⟩
            simpa [homeX] using hWnone v hvW
          have htmp :=
            (BM.Log.ranges hL).
              card_children_meeting_add_one_le_of_none_candidate
                (val := fun v => dis (s := s) v)
                X g.toFinset hnone
          rw [heq] at htmp
          exact htmp
        · simp only [if_neg hown, Nat.add_zero]
          have htmp :=
            (BM.Log.ranges hL).card_children_meeting_le
              (val := fun v => dis (s := s) v)
              X g.toFinset
          rw [heq] at htmp
          exact htmp

      have h2 :=
        Reselect.groups_colors_le
          (lg.recOf X).S (lg.recOf X).Q hk
          (homeX hL X) ω.trees
          (hFX.pf ω hω)

      have h3 :=
        bich_le_crbe hL hF hfull hUt hω

      unfold forestGroups at h1 ⊢
      omega

/-- The form consumed by the call-cost algebra. -/
theorem mk_add_own_full_le_of_W'_none_candidate
    (k : ℕ) (hk : 2 ≤ k)
    (hF : ∀ q r, (q, r) ∈ lg → RecForest r)
    {X : lg.Call}
    (hfull : (lg.recOf X).B' = (lg.recOf X).B)
    (hUt : ∀ v ∈ Utilde (lg.recOf X).B
        ((lg.recOf X).S : Set (Fin G.n)),
      v ∈ (lg.recOf X).U)
    (hWnone : ∀ v ∈ (lg.recOf X).W',
      homeX hL X v = none) :
    mkOf hL k X + ownGroupsOfCandidate k (lg.recOf X)
      ≤
    (groupsOf k (lg.recOf X)).length
      + (crOf hL X).card
      + (beOf hL X).card := by
  rw [← mkOwn_eq_candidate hL k X]
  exact mkOwn_full_le_of_W'_none_candidate
    hL k hk hF hfull hUt hWnone

end CHD
end Frontier
