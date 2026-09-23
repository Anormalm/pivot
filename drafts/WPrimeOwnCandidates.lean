/-!
# Candidate W' ownership provenance for C-HD

Status: UNCOMPILED source-aligned draft.

Goal:
  expose, for every call record in a traced BMSSPC run, the vertex-level fact
  already used locally by upstream's `wr_own` proof:

    v ∈ r.W'  ->
      v ∈ r.U
      and v belongs to no direct child U.

This is deliberately separate from `LogInv` so the core log structure and
`CallRec` do not need new fields.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- Raw path-level W' ownership property for a log.

This mirrors `LogInv.wr`, but for every W' vertex rather than only sources
of edges in `Wr`.
-/
def WPrimeOwn (lg : Log G s (FPData G s)) : Prop :=
  ∀ q r, (q, r) ∈ lg →
    ∀ v ∈ r.W',
      v ∈ r.U ∧
      ∀ a r', (q ++ [a], r') ∈ lg → v ∉ r'.U

/-- A loop log whose sub-call logs already satisfy WPrimeOwn also satisfies
WPrimeOwn for all records it contains.

The proof shape is the same as `loopC_recall`:
- records in the current child's shifted log use the child's induction
  hypothesis;
- records in the tail use the loop induction hypothesis.
-/
theorem loopC_wprime_own_candidate
    {DC : DCost}
    {out : Fin G.n → List (Fin G.m)}
    {k hins hext : ℕ}
    {τ : ℕ → ℕ}
    {sub : SubRelC G s (Finset (Fin G.m)) (FPData G s)}
    {l : ℕ}
    (hsubW :
      ∀ Blow B S d φ res φ' lg,
        sub Blow B S d φ res φ' lg →
        WPrimeOwn lg)
    {B : WLab G s} {S : Finset (Fin G.n)}
    {d0 d1 : Labels G s} {p : ℕ}
    {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)}
    {B'0 : WLab G s} {τl : ℕ} :
    ∀ i (σ : LState G s p) φ σ' φ' lg J cm c,
      LoopC G s DC sub (l + 1) B τl i σ φ σ' φ' lg J cm c →
      WPrimeOwn lg := by
  intro i σ φ σ' φ' lg J cm c hloop
  induction hloop with
  | stop =>
      intro q r hqr
      exact absurd hqr List.not_mem_nil
  | step i σ σ' φ φ1 φ' S0 Bi D1 B'i Ui Di dsub L' piv'
      lg lg' J' cm c hcard hne hpull hSM hstrong hsubrel
      hnd hmem hres hrest ih =>
      intro q r hqr v hv
      rcases List.mem_append.mp hqr with hcur | htail
      · obtain ⟨q', hq, hqmem⟩ := mem_shift.mp hcur
        subst q
        have hcurOwn := hsubW _ _ _ _ _ _ _ _ hsubrel q' r hqmem v hv
        refine ⟨hcurOwn.1, ?_⟩
        intro a r' hchild
        -- A child of a record inside the shifted current-subcall log remains
        -- inside that shifted log; use hcurOwn.2 after stripping the prefix.
        -- This is the same path-prefix bookkeeping pattern used repeatedly in
        -- BMTrace.loopC_log.
        sorry
      · have htailOwn := ih q r htail v hv
        refine ⟨htailOwn.1, ?_⟩
        intro a r' hchild
        -- A direct child of a tail record cannot jump backwards into the
        -- already completed current child's shifted log because loop indices
        -- are monotone. Reuse the `shape` bookkeeping from loopC_log.
        sorry

/-- All W' vertices of every BMSSPC record are owned by that record.

Base case: W' is empty.
Recursive root:
  - r.U = sigma.U ∪ W';
  - W' definition gives v ∉ sigma.U;
  - every direct child root U is contained in sigma.U by LoopLog.root.
Recursive descendants inherit the property from the loop/subcall induction.
-/
theorem bmsspC_wprime_own_candidate
    {DC : DCost} {out : Fin G.n → List (Fin G.m)}
    {k hins hext : ℕ} (τ : ℕ → ℕ) :
    ∀ l Blow B S d φ res φ' lg,
      BMSSPC G s (fpC G s out k hins hext) DC τ l
        Blow B S d φ res φ' lg →
      WPrimeOwn lg := by
  intro l
  induction l with
  | zero =>
      intro Blow B S d φ res φ' lg hrel
      obtain ⟨st, c, hloop, h1, h2, h3, h4, h5, h6, rfl⟩ := hrel
      intro q r hqr v hv
      rcases List.mem_singleton.mp hqr with hqr
      obtain ⟨-, rfl⟩ := Prod.mk.inj hqr
      simp at hv
  | succ l ih =>
      intro Blow B S d φ res φ' lg hrel
      obtain ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, σ, lgc, J, cm, cl,
        L, B'f, T6, W', hfprel, hpiv, hloop, hB'e, hB'n, hT6, hW',
        hL, hres, hlg⟩ := hrel
      subst lg

      -- Obtain the loop log exactly as upstream callC_log does.  Its root
      -- field gives every direct child U ⊆ final sigma.U.
      -- Descendants use loopC_wprime_own_candidate / ih.

      intro q r hqr v hv
      rcases List.mem_cons.mp hqr with hroot | hdesc
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hroot
        refine ⟨?_, ?_⟩
        · exact Finset.mem_union_right _ hv
        · intro a r' hchild hvChild
          have hchild' := mem_cons_nonempty hchild (by simp)
          -- From LoopLog.root:
          --   r'.U ⊆ sigma.U.
          -- From hW':
          --   v ∈ W' -> v ∉ sigma.U.
          -- Contradiction.
          sorry
      · -- descendant record: inherited from loop/subcall recursion
        sorry

end BM
end CHD
end Frontier
