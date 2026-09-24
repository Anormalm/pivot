/-!
# Full-call refined budget arithmetic

Pure natural-number theorem converting the credit-aware full-call record
budget into the refined per-call menu with k*p (cheap) and no t*p term.
-/

namespace Frontier
namespace CHD
namespace BM

theorem budget_arith_full_credit_candidate
    {cost Del A tv k Q S nw p I I0 cs J cm W W' Wr ad bd U Fo t
      Cr Be mk own nch C0 C1 a cI cI0 cn c9 : ℕ}
    (hcost :
      cost + I * p ≤
        scanC * Del
          + A * (tv + k * Q)
          + 3 * S
          + (nw + S + p * (2 + I0))
          + (1 + cs + (1 + I) * J + I * own)
          + cm
          + (1 + S + W + W'
              + Wr * (1 + I)
              + (ad * W' + bd)
              + S))
    (htv : tv ≤ U + Fo)
    (hA : A ≤ a * (k + 1))
    (hW : W ≤ k * Q)
    (hW' : W' ≤ U)
    (hcs : cs ≤ C0 * nch + C1 * U + (6 * k + 1 + I) * mk)
    (hnch : nch ≤ U)
    (hmk : mk ≤ p + Cr + Be)
    (hmkOwn : mk + own ≤ p + Cr + Be)
    (hS1 : 1 ≤ S)
    (hkk : k * (k + 1) ≤ 2 * t)
    (hk1 : 1 ≤ k)
    (hkt : k ≤ t)
    (hI : I ≤ cI * t)
    (hI0 : I0 ≤ cI0 * k)
    (hnw : nw ≤ cn)
    (hC0 : C0 ≤ c9) :
    cost ≤
      (scanC + 3 * a + cn + c9 + C1 + cI0 + 4 * cI
        + 2 * ad + 2 * bd + 40) *
      ((k + 1) * (U + Fo)
        + S
        + t * Q
        + t * (J + Wr + Cr + Be)
        + k * p
        + cm
        + Del) := by
  set R :=
      (k + 1) * (U + Fo)
        + S
        + t * Q
        + t * (J + Wr + Cr + Be)
        + k * p
        + cm
        + Del with hR

  have ht1 : 1 ≤ t := le_trans hk1 hkt

  have rS : S ≤ R := by rw [hR]; omega
  have rUF : (k + 1) * (U + Fo) ≤ R := by rw [hR]; omega
  have rU : U ≤ R := by
    have h1 : U ≤ U + Fo := by omega
    have h2 : U + Fo ≤ (k + 1) * (U + Fo) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have rtQ : t * Q ≤ R := by rw [hR]; omega
  have rtJ : t * J ≤ R := by
    have hs :
        t * (J + Wr + Cr + Be)
          = t * J + t * Wr + t * (Cr + Be) := by ring
    rw [hR, hs]
    omega
  have rtWr : t * Wr ≤ R := by
    have hs :
        t * (J + Wr + Cr + Be)
          = t * J + t * Wr + t * (Cr + Be) := by ring
    rw [hR, hs]
    omega
  have rtCB : t * (Cr + Be) ≤ R := by
    have hs :
        t * (J + Wr + Cr + Be)
          = t * J + t * Wr + t * (Cr + Be) := by ring
    rw [hR, hs]
    omega
  have rkp : k * p ≤ R := by rw [hR]; omega
  have rcm : cm ≤ R := by rw [hR]; omega
  have rDel : Del ≤ R := by rw [hR]; omega
  have r1 : 1 ≤ R := le_trans hS1 rS
  have rp : p ≤ R := by
    have hp : p ≤ k * p := Nat.le_mul_of_pos_left _ hk1
    omega
  have rJ : J ≤ R := by
    have : J ≤ t * J := Nat.le_mul_of_pos_left _ ht1
    omega
  have rWr : Wr ≤ R := by
    have : Wr ≤ t * Wr := Nat.le_mul_of_pos_left _ ht1
    omega
  have rCB : Cr + Be ≤ R := by
    have : Cr + Be ≤ t * (Cr + Be) :=
      Nat.le_mul_of_pos_left _ ht1
    omega

  -- FindPivots term.
  have hk2 : (k + 1) * k ≤ 2 * t := by
    rw [Nat.mul_comm]
    exact hkk
  have eA1 : A * tv ≤ a * R := by
    calc
      A * tv ≤ a * (k + 1) * (U + Fo) :=
        Nat.mul_le_mul hA htv
      _ = a * ((k + 1) * (U + Fo)) := by ring
      _ ≤ a * R := Nat.mul_le_mul_left _ rUF
  have eA2 : A * (k * Q) ≤ 2 * a * R := by
    calc
      A * (k * Q) ≤ a * (k + 1) * (k * Q) :=
        Nat.mul_le_mul_right _ hA
      _ = a * ((k + 1) * k) * Q := by ring
      _ ≤ a * (2 * t) * Q :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk2)
      _ = 2 * a * (t * Q) := by ring
      _ ≤ 2 * a * R := Nat.mul_le_mul_left _ rtQ
  have eA : A * (tv + k * Q) ≤ 3 * a * R := by
    rw [Nat.mul_add]
    omega

  -- Constant new/init terms.
  have enw : nw ≤ cn * R := by
    calc nw ≤ cn := hnw
      _ ≤ cn * R := Nat.le_mul_of_pos_right _ r1

  have epI0 : p * (2 + I0) ≤ (2 + cI0) * R := by
    have hpI0 : p * I0 ≤ cI0 * R := by
      calc
        p * I0 ≤ p * (cI0 * k) := Nat.mul_le_mul_left _ hI0
        _ = cI0 * (k * p) := by ring
        _ ≤ cI0 * R := Nat.mul_le_mul_left _ rkp
    have hs : p * (2 + I0) = 2 * p + p * I0 := by ring
    rw [hs]
    omega

  -- Child constants and cheap/expensive marking split.
  have enchild : C0 * nch ≤ c9 * R := by
    calc
      C0 * nch ≤ c9 * U := Nat.mul_le_mul hC0 hnch
      _ ≤ c9 * R := Nat.mul_le_mul_left _ rU

  have eC1 : C1 * U ≤ C1 * R :=
    Nat.mul_le_mul_left _ rU

  have hcs' :
      cs ≤ C0 * nch + C1 * U
        + (6 * k + 1) * mk + I * mk := by
    have he :
        (6 * k + 1 + I) * mk
          = (6 * k + 1) * mk + I * mk := by ring
    rw [he] at hcs
    simpa [Nat.add_assoc] using hcs

  -- Move all non-marking terms into a base, then use the already-checked
  -- credit cancellation on the marking terms.
  set base :=
      scanC * Del
        + A * (tv + k * Q)
        + 3 * S
        + (nw + S + p * (2 + I0))
        + (1 + C0 * nch + C1 * U + (1 + I) * J)
        + cm
        + (1 + S + W + W'
            + Wr * (1 + I)
            + (ad * W' + bd)
            + S) with hbase

  have hchild :
      1 + cs + (1 + I) * J + I * own ≤
        1 + C0 * nch + C1 * U + (1 + I) * J
          + (6 * k + 1) * mk + I * mk + I * own := by
    omega

  set pre :=
      scanC * Del
        + A * (tv + k * Q)
        + 3 * S
        + (nw + S + p * (2 + I0)) with hpre
  set fin :=
      cm
        + (1 + S + W + W'
            + Wr * (1 + I)
            + (ad * W' + bd)
            + S) with hfin

  have horig :
      scanC * Del
          + A * (tv + k * Q)
          + 3 * S
          + (nw + S + p * (2 + I0))
          + (1 + cs + (1 + I) * J + I * own)
          + cm
          + (1 + S + W + W'
              + Wr * (1 + I)
              + (ad * W' + bd)
              + S)
        =
      pre + (1 + cs + (1 + I) * J + I * own) + fin := by
    rw [hpre, hfin]
    ring

  have htarget :
      base + (6 * k + 1) * mk + I * mk + I * own
        =
      pre
        + (1 + C0 * nch + C1 * U + (1 + I) * J
            + (6 * k + 1) * mk + I * mk + I * own)
        + fin := by
    rw [hbase, hpre, hfin]
    ring

  have hcost' :
      cost + I * p ≤
        base + (6 * k + 1) * mk + I * mk + I * own := by
    rw [horig] at hcost
    rw [htarget]
    exact hcost.trans
      (Nat.add_le_add_right (Nat.add_le_add_left hchild pre) fin)

  have hcancel :=
    full_credit_cancel_candidate
      (cost := cost) (base := base) (C := 6 * k + 1)
      (I := I) (p := p) (mk := mk) (own := own)
      (Cr := Cr) (Be := Be)
      hcost' hmk hmkOwn

  -- Cheap marking coefficient: O(k p + t(Cr+Be)).
  have hcheapP :
      (6 * k + 1) * p ≤ 7 * R := by
    have hc : 6 * k + 1 ≤ 7 * k := by
      omega
    calc
      (6 * k + 1) * p ≤ (7 * k) * p :=
        Nat.mul_le_mul_right _ hc
      _ = 7 * (k * p) := by ring
      _ ≤ 7 * R := Nat.mul_le_mul_left _ rkp

  have hcheapCB :
      (6 * k + 1) * (Cr + Be) ≤ 7 * R := by
    have hc : 6 * k + 1 ≤ 7 * k := by
      omega
    calc
      (6 * k + 1) * (Cr + Be)
        ≤ (7 * k) * (Cr + Be) :=
          Nat.mul_le_mul_right _ hc
      _ = 7 * (k * (Cr + Be)) := by ring
      _ ≤ 7 * (t * (Cr + Be)) := by
          exact Nat.mul_le_mul_left 7
            (Nat.mul_le_mul_right _ hkt)
      _ ≤ 7 * R := Nat.mul_le_mul_left _ rtCB

  have hcheap :
      (6 * k + 1) * (p + Cr + Be) ≤ 14 * R := by
    have hs :
        (6 * k + 1) * (p + Cr + Be)
          = (6 * k + 1) * p + (6 * k + 1) * (Cr + Be) := by
      ring
    rw [hs]
    exact Nat.add_le_add hcheapP hcheapCB

  have hICB : I * (Cr + Be) ≤ cI * R := by
    calc
      I * (Cr + Be) ≤ (cI * t) * (Cr + Be) :=
        Nat.mul_le_mul_right _ hI
      _ = cI * (t * (Cr + Be)) := by ring
      _ ≤ cI * R := Nat.mul_le_mul_left _ rtCB

  -- Remaining window/finalization terms.
  have eJI : (1 + I) * J ≤ (1 + cI) * R := by
    have hIJ : J * I ≤ cI * R := by
      calc
        J * I ≤ J * (cI * t) := Nat.mul_le_mul_left _ hI
        _ = cI * (t * J) := by ring
        _ ≤ cI * R := Nat.mul_le_mul_left _ rtJ
    have hs : (1 + I) * J = J + J * I := by ring
    rw [hs]
    omega

  have eWrI : Wr * (1 + I) ≤ (1 + cI) * R := by
    have hWI : Wr * I ≤ cI * R := by
      calc
        Wr * I ≤ Wr * (cI * t) := Nat.mul_le_mul_left _ hI
        _ = cI * (t * Wr) := by ring
        _ ≤ cI * R := Nat.mul_le_mul_left _ rtWr
    have hs : Wr * (1 + I) = Wr + Wr * I := by ring
    rw [hs]
    omega

  have eW : W ≤ R := by
    have hkq : k * Q ≤ t * Q := Nat.mul_le_mul_right _ hkt
    omega
  have eW' : W' ≤ R := le_trans hW' rU
  have eadW : ad * W' ≤ ad * R :=
    Nat.mul_le_mul_left _ eW'
  have ebd : bd ≤ bd * R := Nat.le_mul_of_pos_right _ r1
  have escan : scanC * Del ≤ scanC * R :=
    Nat.mul_le_mul_left _ rDel

  have hbase_le :
      base ≤
        scanC * R
          + 3 * a * R
          + 3 * R
          + (cn * R + R + (2 + cI0) * R)
          + (R + c9 * R + C1 * R + (1 + cI) * R)
          + R
          + (R + R + R + R
              + (1 + cI) * R
              + (ad * R + bd * R)
              + R) := by
    rw [hbase]
    omega

  have hmark_le :
      (6 * k + 1) * (p + Cr + Be) + I * (Cr + Be)
        ≤ 14 * R + cI * R :=
    Nat.add_le_add hcheap hICB

  have hcombined :
      cost ≤
        (scanC * R
          + 3 * a * R
          + 3 * R
          + (cn * R + R + (2 + cI0) * R)
          + (R + c9 * R + C1 * R + (1 + cI) * R)
          + R
          + (R + R + R + R
              + (1 + cI) * R
              + (ad * R + bd * R)
              + R))
        + (14 * R + cI * R) := by
    exact le_trans hcancel
      (Nat.add_le_add hbase_le hmark_le)

  have hcoef :
      (scanC + 3 * a + cn + c9 + C1 + cI0 + 4 * cI
        + 2 * ad + 2 * bd + 40) * R
      =
        scanC * R
          + 3 * a * R
          + cn * R
          + c9 * R
          + C1 * R
          + cI0 * R
          + 4 * cI * R
          + 2 * ad * R
          + 2 * bd * R
          + 40 * R := by
    ring

  rw [hcoef]
  omega

end BM
end CHD
end Frontier
