/-!
# Record-level bridges for the refined credit budget

These lemmas connect the existential P/W' objects exposed by the call-cost
proof to the record-level groupsOf/ownGroupsCredit functions used by CostLog.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- Child charges computed from a pinned group family agree with the
record-level `chgOf` function. -/
theorem childSum_pinned_eq_chgOf_candidate
    {k C0 C1 C2 : ℕ}
    {r : CallRec G s (FPData G s)}
    {lgc : Log G s (FPData G s)}
    {ω : FPData G s} {p : ℕ}
    {P : Fin p → Finset (Fin G.n)}
    (hω : r.fp = some ω)
    (hpin : ∃ hp : p = (forestGroups r.S r.Q k ω.trees).length,
      ∀ j, P j =
        ((forestGroups r.S r.Q k ω.trees).get (Fin.cast hp j)).toFinset) :
    childSum (childCharge P C0 C1 C2) lgc =
      childSum (chgOf k C0 C1 C2 r) lgc := by
  classical
  unfold childSum
  congr 2
  funext x
  unfold childCharge chgOf groupsOf
  rw [hω]
  congr 2
  obtain ⟨rfl, hP⟩ := hpin
  have hPj : ∀ j, (P j ∩ x.2.U).Nonempty ↔
      ((((forestGroups r.S r.Q k ω.trees).get j).toFinset ∩ x.2.U).Nonempty) := by
    intro j
    rw [hP j]
  rw [← card_filter_get
    (forestGroups r.S r.Q k ω.trees)
    (fun g => (g.toFinset ∩ x.2.U).Nonempty)]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hPj j

/-- The terminal W' group counter of the call proof agrees with the
record-level ownGroupsCredit counter once P and W' are exposed by the record. -/
theorem terminalOwnGroups_eq_ownGroupsCredit_candidate
    {k : ℕ}
    {r : CallRec G s (FPData G s)}
    {ω : FPData G s} {p : ℕ}
    {P : Fin p → Finset (Fin G.n)}
    {W' : Finset (Fin G.n)}
    (hω : r.fp = some ω)
    (hW : r.W' = W')
    (hpin : ∃ hp : p = (forestGroups r.S r.Q k ω.trees).length,
      ∀ j, P j =
        ((forestGroups r.S r.Q k ω.trees).get (Fin.cast hp j)).toFinset) :
    terminalOwnGroups P W' = ownGroupsCredit k r := by
  classical
  unfold terminalOwnGroups ownGroupsCredit groupsOf
  rw [hω]
  obtain ⟨rfl, hP⟩ := hpin
  rw [← card_filter_get
    (forestGroups r.S r.Q k ω.trees)
    (fun g => (g.toFinset ∩ r.W').Nonempty)]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hP j, hW]

end BM
end CHD
end Frontier
