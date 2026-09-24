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
