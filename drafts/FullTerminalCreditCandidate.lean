/-!
# Candidate full-call loop cost with terminal W' credit

Requires the finite-set, refined iteration, loop insertion-credit, and
final-residual candidate lemmas.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}
variable {Φ Ω : Type} {DC : DCost}
variable {B : WLab G s} {S : Finset (Fin G.n)}
variable {d0 d1 : Labels G s} {p : ℕ}
variable {P0 : Fin p → Finset (Fin G.n)}
variable {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- Number of original pivot groups meeting the final W' region. -/
noncomputable def terminalOwnGroups
    (P0 : Fin p → Finset (Fin G.n))
    (W' : Finset (Fin G.n)) : ℕ :=
  (Finset.univ.filter
    (fun j => (P0 j ∩ W').Nonempty)).card

/-- Full-call loop credit after replacing the final nonempty-group
potential by groups meeting W'. -/
theorem loopC_cost_full_terminal_credit_candidate
    (hpre : CallPre B S d0)
    (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Φ → Prop}
    {sub : SubRelC G s Φ Ω} {l : ℕ}
    (hsub : GoodSub G s τ Inv l sub)
    {τl : ℕ} {ap bp ad bd I g : ℕ}
    (hpull : ∀ x, DC.pull (l + 1) x ≤ ap * x + bp)
    (hdel : ∀ x, DC.del (l + 1) x ≤ ad * x + bd)
    (hins : DC.ins (l + 1) ≤ I)
    (hP0 : ∀ j, (P0 j).card ≤ g)
    (hMτ : DC.M (l + 1) ≤ τ l)
    (hgMτ : g * DC.M (l + 1) ≤ τ l)
    {piv : Fin p → Fin G.n}
    (hpiv : ∀ j, piv j ∈ P0 j ∧
      ∀ x ∈ P0 j, d1 (piv j) ≤ d1 x)
    {φ φ' : Φ} {σ : LState G s p}
    {lg : Log G s Ω} {J : Finset (Fin G.m)} {cm cl : ℕ}
    (hloop : LoopC G s DC sub (l + 1) B τl 0
      (initState B d1 P0 piv) φ σ φ' lg J cm cl)
    (hI : Inv φ)
    {W' : Finset (Fin G.n)}
    (hfullS : S ⊆ σ.U ∪ W') :
    cl + I * p ≤
      1 + childSum
        (childCharge P0 (1 + bp + bd) (ap + ad + 4)
          (2 * g + 1 + I)) lg
        + (1 + I) * J.card
        + I * terminalOwnGroups P0 W' := by
  classical
  have h0 := linv_init hpre hfp hpiv
  have hlc :=
    loopC_cost_insert_credit_candidate
      (DC := DC) hpre hfp hsub hpull hdel hins hP0 hMτ hgMτ
      0 (initState B d1 P0 piv) φ σ φ' lg J cm cl
      hloop h0 hI
  have hentry : nonemptyCount (initState B d1 P0 piv) = p :=
    nonemptyCount_initState_eq_candidate
      (B := B) (d1 := d1) (P := P0) (piv := piv)
      (fun j => (hfp.groups j).1)
  obtain ⟨hfinal, -, -, -⟩ :=
    loopC_log hpre hfp hsub
      0 (initState B d1 P0 piv) φ σ φ' lg J cm cl
      hloop h0 hI
  have hres : nonemptyCount σ ≤ terminalOwnGroups P0 W' := by
    exact final_nonempty_le_groups_meeting_W'_candidate
      hfp hfinal hfullS
  have hresI : I * nonemptyCount σ ≤ I * terminalOwnGroups P0 W' :=
    Nat.mul_le_mul_left I hres
  rw [hentry] at hlc
  omega

end BM
end CHD
end Frontier