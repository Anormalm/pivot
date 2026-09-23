#!/usr/bin/env python3
from pathlib import Path

ROOT = Path("upstream/formal/lean")

def replace(path, old, new):
    p = ROOT / path
    s = p.read_text()
    if old not in s:
        raise SystemExit(f"pattern not found in {path}: {old[:80]!r}")
    p.write_text(s.replace(old, new, 1))

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

print("patched DCost.initIns and initCost")
