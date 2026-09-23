/-!
# Final residual groups meet W' in a full call

Source-aligned candidate for the root-call credit proof.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

section FinalResidual

variable {B : WLab G s} {S : Finset (Fin G.n)}
variable {d0 d1 : Labels G s} {p : ℕ}
variable {P0 : Fin p → Finset (Fin G.n)}
variable {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- In a full call, every group still nonempty after the child loop
contains an original-group vertex in the final W' region. -/
theorem final_nonempty_le_groups_meeting_W'_candidate
    {σ : LState G s p}
    {W' : Finset (Fin G.n)}
    (hfp : FPContract B S d0 d1 p P0 Q W)
    (h : LInv G s B S d0 d1 P0 B'0 σ)
    (hfullS : S ⊆ σ.U ∪ W') :
    nonemptyCount σ ≤
      (Finset.univ.filter
        (fun j => (P0 j ∩ W').Nonempty)).card := by
  classical
  unfold nonemptyCount
  refine Finset.card_le_card ?_
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  obtain ⟨y, hyP⟩ := hj
  have hyP0 : y ∈ P0 j := h.Psub j hyP
  have hyS : y ∈ S := (hfp.groups j).2 hyP0
  have hyRet : y ∈ σ.U ∪ W' := hfullS hyS
  have hyNotU : y ∉ σ.U := (h.Pmem j y hyP).2.1
  have hyW : y ∈ W' := by
    rw [Finset.mem_union] at hyRet
    exact hyRet.resolve_left hyNotU
  exact ⟨y, Finset.mem_inter.mpr ⟨hyP0, hyW⟩⟩

end FinalResidual

end BM
end CHD
end Frontier