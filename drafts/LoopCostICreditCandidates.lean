/-!
# Candidate strengthened iterCost / loop telescope for C-HD

Status: UNCOMPILED source-aligned draft.
Upstream target:
  formal/lean/Frontier/CHD/LoopCost.lean

This file assumes the candidate finite-set lemmas in
`drafts/LoopCostFiniteCandidates.lean`.

Key algebraic refinement:

  group work
    <= (2g+1) * meetings + I * marked

and because marked/emptied are disjoint and both meet the child,

  I * marked + I * emptied <= I * meetings.

Therefore

  iterCost + I * emptied
    <= ordinary terms + (2g+1+I) * meetings.

The exact emptying identity then telescopes the I-weighted potential.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

section IterCandidate

variable {p : ℕ} {σ : LState G s p}

/-- Candidate replacement/refinement of `iterCost_le`.

Unlike the current theorem, the expensive insertion factor `I` is attached
to actual BM.23 markings, while the cheap group scan/expansion work is charged
to all original groups meeting the child.

Adding `I * |emptiedGroups|` to the left lets marked+emptied be charged
together to the meeting count.
-/
theorem iterCost_le_with_empty_credit_candidate
    {DC : DCost} {lv : ℕ} {S0 Ui : Finset (Fin G.n)} {nL : ℕ}
    {ap bp ad bd I g : ℕ} {P0 : Fin p → Finset (Fin G.n)}
    (hpull : DC.pull lv S0.card ≤ ap * S0.card + bp)
    (hdel : DC.del lv Ui.card ≤ ad * Ui.card + bd)
    (hins : DC.ins lv ≤ I)
    (hg : ∀ j, (σ.P j).card ≤ g)
    (hS0 : S0.card ≤ Ui.card)
    (hpulled : ∑ j ∈ pulledGroups σ S0, (σ.P j).card ≤
      Ui.card + g * ((markedGroups σ Ui).card + (emptiedGroups σ Ui).card))
    (hmeet : (markedGroups σ Ui).card + (emptiedGroups σ Ui).card ≤
      (Finset.univ.filter (fun j => (P0 j ∩ Ui).Nonempty)).card) :
    iterCost DC lv σ S0 Ui nL
        + I * (emptiedGroups σ Ui).card
      ≤
    (1 + bp + bd)
      + (ap + ad + 4) * Ui.card
      + (1 + I) * nL
      + (2 * g + 1 + I) *
          (Finset.univ.filter (fun j => (P0 j ∩ Ui).Nonempty)).card := by
  classical
  unfold iterCost

  let M := (markedGroups σ Ui).card
  let E := (emptiedGroups σ Ui).card
  let H := (Finset.univ.filter (fun j => (P0 j ∩ Ui).Nonempty)).card

  have hmarked :
      ∑ j ∈ markedGroups σ Ui,
        ((σ.P j \ Ui).card + 1 + DC.ins lv)
      ≤ M * (g + 1 + I) := by
    dsimp [M]
    calc
      ∑ j ∈ markedGroups σ Ui,
          ((σ.P j \ Ui).card + 1 + DC.ins lv)
        ≤ ∑ j ∈ markedGroups σ Ui, (g + 1 + I) :=
          Finset.sum_le_sum (fun j _ => by
            have hs :
                (σ.P j \ Ui).card ≤ (σ.P j).card :=
              Finset.card_le_card Finset.sdiff_subset
            have hg' := hg j
            omega)
      _ = (markedGroups σ Ui).card * (g + 1 + I) := by
          rw [Finset.sum_const, smul_eq_mul]

  have hgroup :
      g * (M + E) + M * (g + 1 + I) + I * E
        ≤ (2 * g + 1 + I) * H := by
    have hME : M + E ≤ H := by
      simpa [M, E, H] using hmeet
    -- Separate the insertion coefficient from the cheap scan terms:
    --
    --   g(M+E) + (g+1)M <= (2g+1)(M+E)
    --   I M + I E       = I(M+E)
    --
    -- then use M+E <= H.
    have hcheap :
        g * (M + E) + (g + 1) * M
          ≤ (2 * g + 1) * (M + E) := by
      nlinarith
    have hins' : I * M + I * E = I * (M + E) := by ring
    have hcoef :
        (2 * g + 1) * (M + E) + I * (M + E)
          = (2 * g + 1 + I) * (M + E) := by ring
    have hmono :
        (2 * g + 1 + I) * (M + E)
          ≤ (2 * g + 1 + I) * H :=
      Nat.mul_le_mul_left _ hME
    omega

  have h1 : ap * S0.card ≤ ap * Ui.card :=
    Nat.mul_le_mul_left _ hS0

  have h2 : nL * (1 + DC.ins lv) ≤ (1 + I) * nL := by
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_right _ (by omega)

  have hpulled' :
      ∑ j ∈ pulledGroups σ S0, (σ.P j).card
        ≤ Ui.card + g * (M + E) := by
    simpa [M, E] using hpulled

  have hmarked' :
      ∑ j ∈ markedGroups σ Ui,
        ((σ.P j \ Ui).card + 1 + DC.ins lv)
        ≤ M * (g + 1 + I) := hmarked

  have hdel' : DC.del lv Ui.card ≤ ad * Ui.card + bd := hdel
  have hpull' : DC.pull lv S0.card ≤ ap * S0.card + bp := hpull

  -- The remaining arithmetic is the same expansion as upstream
  -- `iterCost_le`, except the group-dependent terms are discharged by
  -- `hgroup`.
  omega

end IterCandidate

section LoopCandidate

variable {Φ Ω : Type} {DC : DCost}
variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s}
variable {p : ℕ} {P0 : Fin p → Finset (Fin G.n)}
variable {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- Schematic strengthened loop theorem.

The proof should follow upstream `loopC_cost` almost verbatim, replacing:
  * `iterCost_le` with `iterCost_le_with_empty_credit_candidate`;
  * one-sided `card_nonempty_next` with exact
    `card_nonempty_next_eq_candidate`.

At every step:
  c_step + I * emptied <= childCharge + ...
and
  nonempty(next) + emptied = nonempty(now).

Thus the I-weighted emptying terms telescope exactly.
-/
theorem loopC_cost_I_credit_candidate
    (hpre : CallPre B S d0)
    (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ}
    {Inv : Φ → Prop}
    {sub : SubRelC G s Φ Ω}
    {l : ℕ}
    (hsub : GoodSub G s τ Inv l sub)
    {τl : ℕ}
    {ap bp ad bd I g : ℕ}
    (hpull : ∀ x, DC.pull (l + 1) x ≤ ap * x + bp)
    (hdel : ∀ x, DC.del (l + 1) x ≤ ad * x + bd)
    (hins : DC.ins (l + 1) ≤ I)
    (hP0 : ∀ j, (P0 j).card ≤ g)
    (hMτ : DC.M (l + 1) ≤ τ l)
    (hgMτ : g * DC.M (l + 1) ≤ τ l) :
    ∀ i (σ : LState G s p) φ σ' φ' lg J cm c,
      LoopC G s DC sub (l + 1) B τl i σ φ σ' φ' lg J cm c →
      LInv G s B S d0 d1 P0 B'0 σ →
      Inv φ →
      c + I * nonemptyCount σ
        ≤
      1
        + childSum
            (childCharge P0
              (1 + bp + bd)
              (ap + ad + 4)
              (2 * g + 1 + I)) lg
        + (1 + I) * J.card
        + I * nonemptyCount σ' := by
  -- Proof plan:
  --
  -- induction hloop
  -- stop:
  --   simp
  --
  -- step:
  --   reuse upstream setup verbatim through hsubP/hpivP/hgP/hS0U
  --   have hmeet :=
  --     marked_emptied_card_le_meeting_candidate
  --       σ P0 hsubP hpivP Ui
  --
  --   have hit :=
  --     iterCost_le_with_empty_credit_candidate
  --       ... hS0U.1 hS0U.2 hmeet
  --
  --   have hpot := card_nonempty_next_eq_candidate σ Ui
  --
  --   use IH on the tail;
  --   rewrite next state's nonemptyCount exactly as upstream;
  --   rewrite childSum/window disjointness exactly as upstream;
  --   omega.
  sorry

end LoopCandidate

end BM
end CHD
end Frontier
