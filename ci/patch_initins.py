#!/usr/bin/env python3
from pathlib import Path

ROOT = Path("upstream/formal/lean")

def replace(path, old, new, count=1):
    p = ROOT / path
    s = p.read_text()
    if old not in s:
        raise SystemExit(f"pattern not found in {path}: {old[:120]!r}")
    p.write_text(s.replace(old, new, count))

# 1. Split fresh BM.6 insertion from ordinary evolved insertion.
replace(
    "Frontier/CHD/BMCost.lean",
    """  /-- create an empty level-`l` structure -/
  new : ℕ → ℕ
  /-- one `Insert` (or decrease) at level `l` -/
  ins : ℕ → ℕ""",
    """  /-- create an empty level-`l` structure -/
  new : ℕ → ℕ
  /-- one BM.6 insertion into a freshly-created level-`l` structure -/
  initIns : ℕ → ℕ
  /-- one ordinary `Insert` (or decrease) at level `l` -/
  ins : ℕ → ℕ"""
)

replace(
    "Frontier/CHD/BMCost.lean",
    """  DC.new lv + ∑ j, (P j).card + p * (2 + DC.ins lv)""",
    """  DC.new lv + ∑ j, (P j).card + p * (2 + DC.initIns lv)"""
)

# 2. The abstract call-cost theorem now gets separate bounds I0 (fresh) and I
#    (ordinary evolved inserts).
replace(
    "Frontier/CHD/LoopCost.lean",
    """    {ap bp ad bd I nw : ℕ}
    (hpull : ∀ x, DC.pull (l + 1) x ≤ ap * x + bp) (hdel : ∀ x, DC.del (l + 1) x ≤ ad * x + bd)
    (hinsI : DC.ins (l + 1) ≤ I) (hnew : DC.new (l + 1) ≤ nw)""",
    """    {ap bp ad bd I I0 nw : ℕ}
    (hpull : ∀ x, DC.pull (l + 1) x ≤ ap * x + bp) (hdel : ∀ x, DC.del (l + 1) x ≤ ad * x + bd)
    (hinsI : DC.ins (l + 1) ≤ I) (hinitI : DC.initIns (l + 1) ≤ I0)
    (hnew : DC.new (l + 1) ≤ nw)"""
)

replace(
    "Frontier/CHD/LoopCost.lean",
    """        + (nw + r.S.card + p * (2 + I))""",
    """        + (nw + r.S.card + p * (2 + I0))"""
)

replace(
    "Frontier/CHD/LoopCost.lean",
    """    have e4 : p * (2 + DC.ins (l + 1)) ≤ p * (2 + I) := Nat.mul_le_mul_left _ (by omega)""",
    """    have e4 : p * (2 + DC.initIns (l + 1)) ≤ p * (2 + I0) :=
      Nat.mul_le_mul_left _ (by omega)"""
)

# 3. Real C-HD instance and placeholder capacity instance.
replace(
    "Frontier/CHD/BMTeleChd.lean",
    """  new := fun _ => 3
  ins := chdIns t k δ L0""",
    """  new := fun _ => 3
  initIns := fun _ => 4
  ins := chdIns t k δ L0"""
)

replace(
    "Frontier/CHD/L6/DCap.lean",
    """  new := fun _ => 0
  ins := fun _ => 0""",
    """  new := fun _ => 0
  initIns := fun _ => 0
  ins := fun _ => 0"""
)

# 4. Positional zero-cost DCost constructors used only for simulation/
#    totality glue. Add one unary zero field after `new`.
for path in [
    "Frontier/CHD/BMLazy.lean",
    "Frontier/CHD/RamBodyA.lean",
    "Frontier/CHD/BMPlace.lean",
]:
    p = ROOT / path
    s = p.read_text()
    old1 = "⟨Mf, fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, 0, 0⟩"
    new1 = "⟨Mf, fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, 0, 0⟩"
    s = s.replace(old1, new1)
    old2 = "⟨fun _ => 1, fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0,\n      fun _ _ => 0, 0, 0⟩"
    new2 = "⟨fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0,\n      fun _ _ => 0, 0, 0⟩"
    s = s.replace(old2, new2)
    p.write_text(s)

print("patched stage-1 DCost.initIns interface")


# 5. Thread the fresh insertion coefficient through CostLog's record budget.
replace(
    "Frontier/CHD/CostLog.lean",
    """noncomputable def budOf (k hins hext ad bd I nw : ℕ) (r : CallRec G s (FPData G s)) (cs : ℕ) : ℕ :=""",
    """noncomputable def budOf (k hins hext ad bd I I0 nw : ℕ) (r : CallRec G s (FPData G s)) (cs : ℕ) : ℕ :="""
)

replace(
    "Frontier/CHD/CostLog.lean",
    """    + (nw + r.S.card + r.p * (2 + I))""",
    """    + (nw + r.S.card + r.p * (2 + I0))"""
)

replace(
    "Frontier/CHD/CostLog.lean",
    """    {ap bp ad bd I nw : ℕ}
    (hsubc : SubCost (chgOf k (1 + bp + bd) (ap + ad + 4) (2 * (3 * k) + 1 + I))
      (budOf k hins hext ad bd I nw) sub (DelInv G s))""",
    """    {ap bp ad bd I I0 nw : ℕ}
    (hsubc : SubCost (chgOf k (1 + bp + bd) (ap + ad + 4) (2 * (3 * k) + 1 + I))
      (budOf k hins hext ad bd I I0 nw) sub (DelInv G s))"""
)

replace(
    "Frontier/CHD/CostLog.lean",
    """    (hinsI : DC.ins (l + 1) ≤ I) (hnew : DC.new (l + 1) ≤ nw)
    (hMτ : DC.M (l + 1) ≤ τ l)""",
    """    (hinsI : DC.ins (l + 1) ≤ I) (hinitI : DC.initIns (l + 1) ≤ I0)
    (hnew : DC.new (l + 1) ≤ nw)
    (hMτ : DC.M (l + 1) ≤ τ l)"""
)

replace(
    "Frontier/CHD/CostLog.lean",
    """    RecCost (chgOf k (1 + bp + bd) (ap + ad + 4) (2 * (3 * k) + 1 + I)) (budOf k hins hext ad bd I nw) lg := by""",
    """    RecCost (chgOf k (1 + bp + bd) (ap + ad + 4) (2 * (3 * k) + 1 + I)) (budOf k hins hext ad bd I I0 nw) lg := by"""
)

replace(
    "Frontier/CHD/CostLog.lean",
    """    callC_cost hout hsort hsimp hk hsub hpre hI hlow hrel hpull hdel hinsI hnew hMτ hgMτ""",
    """    callC_cost hout hsort hsimp hk hsub hpre hI hlow hrel hpull hdel hinsI hinitI hnew hMτ hgMτ"""
)

replace(
    "Frontier/CHD/CostLog.lean",
    """    {ap bp ad bd I nw : ℕ}
    (hpull : ∀ l x, DC.pull (l + 1) x ≤ ap * x + bp) (hdel : ∀ l x, DC.del (l + 1) x ≤ ad * x + bd)
    (hinsI : ∀ l, DC.ins (l + 1) ≤ I) (hnew : ∀ l, DC.new (l + 1) ≤ nw)""",
    """    {ap bp ad bd I I0 nw : ℕ}
    (hpull : ∀ l x, DC.pull (l + 1) x ≤ ap * x + bp) (hdel : ∀ l x, DC.del (l + 1) x ≤ ad * x + bd)
    (hinsI : ∀ l, DC.ins (l + 1) ≤ I) (hinitI : ∀ l, DC.initIns (l + 1) ≤ I0)
    (hnew : ∀ l, DC.new (l + 1) ≤ nw)"""
)

replace(
    "Frontier/CHD/CostLog.lean",
    """    ∀ l, SubCost (chgOf k (1 + bp + bd) (ap + ad + 4) (2 * (3 * k) + 1 + I)) (budOf k hins hext ad bd I nw)""",
    """    ∀ l, SubCost (chgOf k (1 + bp + bd) (ap + ad + 4) (2 * (3 * k) + 1 + I)) (budOf k hins hext ad bd I I0 nw)"""
)

replace(
    "Frontier/CHD/CostLog.lean",
    """      (bmsspC_reccost hout hsort hsimp hk τ hpull hdel hinsI hnew hMτ hgMτ l) hpre hI hlow hrel
      (hpull l) (hdel l) (hinsI l) (hnew l) (hMτ l) (hgMτ l)""",
    """      (bmsspC_reccost hout hsort hsimp hk τ hpull hdel hinsI hinitI hnew hMτ hgMτ l) hpre hI hlow hrel
      (hpull l) (hdel l) (hinsI l) (hinitI l) (hnew l) (hMτ l) (hgMτ l)"""
)

print("patched stage-2 CostLog fresh-init propagation")


# 6. Preserve the existing coarse CostLe theorem with a separate fresh
#    insertion coefficient.  The old target still contains t*p; this stage
#    only makes the interface coherent before the refined CostLe is added.
replace(
    "Frontier/CHD/CostLe.lean",
    """theorem budget_arith {Del A tv k Q S nw p I cs J cm W W' Wr ad bd U Fo t Cr Be mk nch C0 C1 C2 a cI cn c9 pS : ℕ}""",
    """theorem budget_arith {Del A tv k Q S nw p I I0 cs J cm W W' Wr ad bd U Fo t Cr Be mk nch C0 C1 C2 a cI cn c9 pS : ℕ}"""
)

replace(
    "Frontier/CHD/CostLe.lean",
    """    (hI : I ≤ cI * t) (hnw : nw ≤ cn * t) (hC2 : C2 ≤ 6 * k + 1 + I) :""",
    """    (hI : I ≤ cI * t) (hI0 : I0 ≤ cI * t)
    (hnw : nw ≤ cn * t) (hC2 : C2 ≤ 6 * k + 1 + I) :"""
)

replace(
    "Frontier/CHD/CostLe.lean",
    """    scanC * Del + A * (tv + k * Q) + 3 * S + (nw + S + p * (2 + I)) +""",
    """    scanC * Del + A * (tv + k * Q) + 3 * S + (nw + S + p * (2 + I0)) +"""
)

replace(
    "Frontier/CHD/CostLe.lean",
    """  have eI : ∀ x, t * x ≤ R → x * I ≤ cI * R := fun x hx => by
    calc x * I ≤ x * (cI * t) := Nat.mul_le_mul_left _ hI
      _ = cI * (t * x) := by ring
      _ ≤ cI * R := Nat.mul_le_mul_left _ hx""",
    """  have eI : ∀ x, t * x ≤ R → x * I ≤ cI * R := fun x hx => by
    calc x * I ≤ x * (cI * t) := Nat.mul_le_mul_left _ hI
      _ = cI * (t * x) := by ring
      _ ≤ cI * R := Nat.mul_le_mul_left _ hx
  have eI0 : ∀ x, t * x ≤ R → x * I0 ≤ cI * R := fun x hx => by
    calc x * I0 ≤ x * (cI * t) := Nat.mul_le_mul_left _ hI0
      _ = cI * (t * x) := by ring
      _ ≤ cI * R := Nat.mul_le_mul_left _ hx"""
)

replace(
    "Frontier/CHD/CostLe.lean",
    """  have epI : p * (2 + I) ≤ 2 * R + cI * R := by
    have := eI p rtp
    have : p * (2 + I) = 2 * p + p * I := by ring""",
    """  have epI : p * (2 + I0) ≤ 2 * R + cI * R := by
    have := eI0 p rtp
    have : p * (2 + I0) = 2 * p + p * I0 := by ring"""
)

replace(
    "Frontier/CHD/CostLe.lean",
    """    (hk : 2 ≤ k) {C0 C1 I ad bd nw a cI cn c9 t c : ℕ}
    (hRC : RecCost (chgOf k C0 C1 (2 * (3 * k) + 1 + I)) (budOf k hins hext ad bd I nw) lg)""",
    """    (hk : 2 ≤ k) {C0 C1 I I0 ad bd nw a cI cn c9 t c : ℕ}
    (hRC : RecCost (chgOf k C0 C1 (2 * (3 * k) + 1 + I)) (budOf k hins hext ad bd I I0 nw) lg)"""
)

replace(
    "Frontier/CHD/CostLe.lean",
    """    (hI : I ≤ cI * t) (hnw : nw ≤ cn * t) (hC0 : C0 ≤ c9)""",
    """    (hI : I ≤ cI * t) (hI0 : I0 ≤ cI * t)
    (hnw : nw ≤ cn * t) (hC0 : C0 ≤ c9)"""
)

replace(
    "Frontier/CHD/CostLe.lean",
    """    (S := r.S.card) (nw := nw) (p := r.p) (I := I) (J := r.J.card)""",
    """    (S := r.S.card) (nw := nw) (p := r.p) (I := I) (I0 := I0) (J := r.J.card)"""
)

replace(
    "Frontier/CHD/CostLe.lean",
    """    htv hA hW hW' hcs hmk hnch hS1 hpQ hkk h3k (by omega) hI hnw (by omega)""",
    """    htv hA hW hW' hcs hmk hnch hS1 hpQ hkk h3k (by omega) hI hI0 hnw (by omega)"""
)

print("patched stage-3 CostLe fresh-init propagation")


# 7. Instantiate the separated fresh insertion cost in MasterCost.
replace(
    "Frontier/CHD/MasterCost.lean",
    """    (I := 211 * Nat.log 2 (8 * chdRho (tF n m) δ (LF n m) + 8) + 441) (nw := 3)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun l => chdIns_le (by omega) l) (fun _ => le_rfl) hMτ hgMτ""",
    """    (I := 211 * Nat.log 2 (8 * chdRho (tF n m) δ (LF n m) + 8) + 441) (I0 := 4) (nw := 3)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun l => chdIns_le (by omega) l)
    (fun _ => le_rfl) (fun _ => le_rfl) hMτ hgMτ"""
)

replace(
    "Frontier/CHD/MasterCost.lean",
    """    (I := 211 * Nat.log 2 (8 * chdRho (tF n m) δ (LF n m) + 8) + 441) (ad := 5) (bd := 1) (nw := 3)
    (a := a) (cI := 3826) (cn := 1) (c9 := 952) (t := tF n m)
    (c := cValid a) hRC hRA hS hτ ha (mc_kk n m) h3k (mc_ins_le n m δ hδ hdd) (by omega) le_rfl""",
    """    (I := 211 * Nat.log 2 (8 * chdRho (tF n m) δ (LF n m) + 8) + 441) (I0 := 4)
    (ad := 5) (bd := 1) (nw := 3)
    (a := a) (cI := 3826) (cn := 1) (c9 := 952) (t := tF n m)
    (c := cValid a) hRC hRA hS hτ ha (mc_kk n m) h3k (mc_ins_le n m δ hδ hdd)
    (by have ht := sixteen_le_tF n m; nlinarith) (by omega) le_rfl"""
)

print("patched stage-4 MasterCost fresh-init instantiation")
