/-!
# Candidate credit-carrying CostLog relation

Status: UNCOMPILED source-aligned draft.
Upstream targets:
  Frontier/CHD/CostLog.lean
  Frontier/CHD/CostLe.lean

Purpose:
  preserve the useful full-call + I*p credit produced by the strengthened
  BM.23 loop telescope until the global Cr/Be home charging is available.

No graph/call semantics are changed.  CallRec and LogInv stay unchanged.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n} {Ω : Type}

/-- Credit-carrying analogue of upstream RecCost.

For each recursive record:
    cost + credit(record)
      <= budget(record, childSum)

The structural log machinery only transports this inequality; it does not
interpret the credit.
-/
def RecCostCredit
    (credit : CallRec G s Ω → ℕ)
    (chg : CallRec G s Ω → CallRec G s Ω → ℕ)
    (bud : CallRec G s Ω → ℕ → ℕ)
    (lg : Log G s Ω) : Prop :=
  ∀ q r, (q, r) ∈ lg → r.base = false →
    r.cost + credit r ≤ bud r (childSumAt (chg r) q lg)

theorem RecCostCredit.nil
    (credit : CallRec G s Ω → ℕ)
    (chg : CallRec G s Ω → CallRec G s Ω → ℕ)
    (bud : CallRec G s Ω → ℕ → ℕ) :
    RecCostCredit credit chg bud ([] : Log G s Ω) :=
  fun _ _ h => absurd h List.not_mem_nil

/-- Shifting a log preserves a record-local credit verbatim.

This is the same proof as upstream RecCost.shift: the record is unchanged,
and only the childSum path is rewritten.
-/
theorem RecCostCredit.shift
    {credit : CallRec G s Ω → ℕ}
    {chg : CallRec G s Ω → CallRec G s Ω → ℕ}
    {bud : CallRec G s Ω → ℕ → ℕ}
    {lg : Log G s Ω}
    (h : RecCostCredit credit chg bud lg)
    (i : ℕ) (lg' : Log G s Ω)
    (hsh : ∀ q r, (q, r) ∈ lg' →
      ∃ j q', q = j :: q' ∧ j ≠ i) :
    ∀ q r, (q, r) ∈ lg.shift i → r.base = false →
      r.cost + credit r
        ≤ bud r (childSumAt (chg r) q (lg.shift i ++ lg')) := by
  intro q r hqr hb
  obtain ⟨q', rfl, hq'⟩ := mem_shift.mp hqr
  rw [childSumAt_append, childSumAt_shift,
    childSumAt_of_shape _ i q' lg' hsh, Nat.add_zero]
  exact h q' r hq' hb

/-- Sub-call version of RecCostCredit. -/
def SubCostCredit {Φ : Type}
    (credit : CallRec G s Ω → ℕ)
    (chg : CallRec G s Ω → CallRec G s Ω → ℕ)
    (bud : CallRec G s Ω → ℕ → ℕ)
    (sub : SubRelC G s Φ Ω)
    (Inv : Φ → Prop) : Prop :=
  ∀ Blow B S d φ res φ' lg,
    CallPre B S d →
    Inv φ →
    (∀ x ∈ S, Blow ≤ dis (s := s) x) →
    Blow ≤ B →
    sub Blow B S d φ res φ' lg →
    RecCostCredit credit chg bud lg

/--
Recommended credit for the refined C-HD accounting.

Only FULL recursive calls receive the expensive insertion credit.
Partial calls keep zero credit and retain the existing t*|S| budget.
-/
def fullPivotCredit (I : ℕ)
    (r : CallRec G s Ω) : ℕ :=
  if r.B' = r.B then I * r.p else 0

/-
The next theorem should mirror CostLog.loopC_reccost exactly.

Because RecCostCredit.shift is structurally identical to RecCost.shift,
the only substantive new proof is the root record in callC_reccost:
the strengthened loop theorem supplies + I*p on the left for a full call.

Schematic target:

theorem callC_reccost_credit ...
  (hsubc : SubCostCredit (fullPivotCredit I) chg bud sub Inv)
  ...
  : RecCostCredit (fullPivotCredit I) chg bud lg := by
  ...
-/

/-- Original groups containing a parent-final W' vertex.

No CallRec field is added: W' and the pinned FindPivots groups already live
in the record.
-/
noncomputable noncomputable def ownGroupsCredit
    (k : ℕ) (r : CallRec G s (FPData G s)) : ℕ :=
  (groupsOf k r).countP
    (fun g => decide (g.toFinset ∩ r.W').Nonempty)

/--
Refined record budget shape.

This sketch intentionally does NOT include the old generic p*(2+I) term:
- BM.6 fresh insertion is priced O(p), not I*p;
- cheap O(k p) work remains explicitly cheap;
- full-call expensive I*p is carried as a left credit;
- the final nonempty-group potential is paid by I*ownGroups on full calls;
- on partial calls both markings and final residual groups are bounded by S.
-/
noncomputable def budCreditSketch
    (k hins hext ad bd initC I nw : ℕ)
    (r : CallRec G s (FPData G s))
    (cs : ℕ) : ℕ :=
  scanC * delCard r
    + fpA k hins hext * (tvLen r + k * r.Q.card)
    + 3 * r.S.card
    + (nw + r.S.card + initC * r.p)
    + (1 + 3 * k * r.p + cs + (1 + I) * r.J.card)
    + (if r.B' = r.B
        then I * ownGroupsCredit k r
        else I * r.S.card)
    + r.cMerge
    + (1 + r.S.card
        + (if r.B' = r.B then 0 else r.S.card) * I
        + r.W.card + r.W'.card
        + r.Wr.card * (1 + I)
        + (ad * r.W'.card + bd)
        + r.S.card)

/-
At CostLe, for a FULL call X:
  cost + I*p <= budCredit
  mkOf + ownGroups <= p + Cr + Be

The child/loop algebra is arranged so that the I-weighted part of budCredit
contains:
  I*mkOf from the child meeting sum, and
  I*ownGroupsCredit from the final nonempty-group potential.

Thus a FULL call has
  cost + I*p
    <= cheap + I*(mkOf + ownGroupsCredit) + ...
and the refined colour lemma
  mkOf + ownGroupsCredit <= p + Cr + Be
supplies the matching RHS I*p, which cancels the record credit.

For a PARTIAL call:
  fullPivotCredit = 0,
  p <= |S|,
  mkOf <= |S|,
  final nonempty groups <= p <= |S|,
  3k <= t.
So all remaining O(k p), I*mkOf, and I*finalNonempty work is absorbed by
a constant number of existing t*|S| terms.

The final CostAggregate.Valid target therefore needs no unconditional t*p.
-/

end BM
end CHD
end Frontier
