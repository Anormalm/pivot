/-!
# Abstract dormant-component state

This is the first state-machine layer for a batched FindPivots replacement.
It deliberately excludes the eventual RAM representation and detailed repair
search.  The goal is to pin the persistent semantic state that contacts and
root absorption must preserve.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

structure DormantComp (G : Graph) (s : Fin G.n) where
  /-- Permanently owned discovered vertices of this invocation. -/
  owned : Finset (Fin G.n)
  /-- Frontier roots assigned to this component. -/
  roots : Finset (Fin G.n)
  /-- Reusable failed-search/repair val region. -/
  val : Finset (Fin G.n)
  /-- Semantically complete, permanently stable subregion. -/
  core : Finset (Fin G.n)
  /-- Deferred incoming candidate minima. -/
  pending : DS G s

namespace DormantComp

/-- Add a later S-root that is already owned by this component. -/
def addRoot (C : DormantComp G s) (x : Fin G.n) :
    DormantComp G s :=
  { C with roots := insert x C.roots }

/-- Structural union of two dormant components.  Pending candidates combine by
pointwise minimum through the existing DS merge operation. -/
noncomputable def merge
    (A B : DormantComp G s) : DormantComp G s :=
  { owned := A.owned ∪ B.owned
    roots := A.roots ∪ B.roots
    val := A.val ∪ B.val
    core := A.core ∪ B.core
    pending := DS.merge A.pending B.pending }

end DormantComp

/-- Persistent semantic invariant of a dormant component at labels d/bound B.

The full val-region need not be complete.  Only core is required to be
complete/closed and therefore permanently reusable. -/
structure DormantInv
    (d : Labels G s) (B : WLab G s)
    (C : DormantComp G s) : Prop where
  roots_owned : C.roots ⊆ C.owned
  val_owned : C.val ⊆ C.owned
  core_val : C.core ⊆ C.val
  pending_sound :
    ∀ v c, C.pending v = some c →
      dis (s := s) v ≤ c
  core_complete :
    ∀ v ∈ C.core, Complete d v
  core_closed :
    ∀ e : Fin G.m,
      G.src e ∈ C.core →
      ext (d (G.src e)) e < B →
      G.dst e ∈ C.core

/-- Absorbing an already-owned root requires no label/search work and
preserves the dormant invariant. -/
theorem DormantInv.addRoot_candidate
    {d : Labels G s} {B : WLab G s}
    {C : DormantComp G s} {x : Fin G.n}
    (h : DormantInv d B C)
    (hx : x ∈ C.owned) :
    DormantInv d B (C.addRoot x) := by
  refine
    { roots_owned := ?_
      val_owned := h.val_owned
      core_val := h.core_val
      pending_sound := h.pending_sound
      core_complete := h.core_complete
      core_closed := h.core_closed }
  intro y hy
  simp only [DormantComp.addRoot, Finset.mem_insert] at hy
  rcases hy with rfl | hy
  · exact hx
  · exact h.roots_owned hy

/-- Merging two dormant components preserves all persistent semantic fields.
No closure claim is made for the full val union; only the complete cores are
combined. -/
theorem DormantInv.merge_candidate
    {d : Labels G s} {B : WLab G s}
    {A C : DormantComp G s}
    (hA : DormantInv d B A)
    (hC : DormantInv d B C) :
    DormantInv d B (A.merge C) := by
  classical
  refine
    { roots_owned := ?_
      val_owned := ?_
      core_val := ?_
      pending_sound := ?_
      core_complete := ?_
      core_closed := ?_ }
  · intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact Finset.mem_union_left _ (hA.roots_owned h)
    · exact Finset.mem_union_right _ (hC.roots_owned h)
  · intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact Finset.mem_union_left _ (hA.val_owned h)
    · exact Finset.mem_union_right _ (hC.val_owned h)
  · intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact Finset.mem_union_left _ (hA.core_val h)
    · exact Finset.mem_union_right _ (hC.core_val h)
  · exact pending_merge_sound_candidate
      hA.pending_sound hC.pending_sound
  · intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact hA.core_complete v h
    · exact hC.core_complete v h
  · intro e he hbelow
    rcases Finset.mem_union.mp he with h | h
    · exact Finset.mem_union_left _
        (hA.core_closed e h hbelow)
    · exact Finset.mem_union_right _
        (hC.core_closed e h hbelow)

end CHD
end Frontier
