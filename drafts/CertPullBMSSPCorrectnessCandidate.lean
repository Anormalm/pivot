open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

variable (G s)

/-- BMSSP loop with the weaker certificate-oriented pull contract. -/
inductive LoopRelCert {p : ℕ}
    (sub : WLab G s → Finset (Fin G.n) → Labels G s → Result G s → Prop)
    (B : WLab G s) (τ : ℕ) : LState G s p → LState G s p → Prop
  | stop (σ : LState G s p) :
      (τ < σ.U.card ∨ σ.D.IsEmpty) →
      LoopRelCert sub B τ σ σ
  | step (σ σ' : LState G s p)
      (S0 : Finset (Fin G.n)) (Bi : WLab G s) (D1 : DS G s)
      (B'i : WLab G s) (Ui : Finset (Fin G.n)) (Di : DS G s)
      (d1 : Labels G s) (L : List (Fin G.m))
      (piv' : Fin p → Fin G.n) :
      σ.U.card ≤ τ →
      ¬ σ.D.IsEmpty →
      CertPullSpec (G := G) (s := s) σ B S0 Bi D1 →
      sub Bi (expand σ S0 Bi) σ.d (B'i, Ui, Di, d1) →
      Enumerates G L Ui →
      Reselect σ Ui
        (L.foldl (relaxIns G s B (some Bi))
          (d1, (D1.merge Di).deleteSet Ui)).1 piv' →
      LoopRelCert sub B τ
        { d := (L.foldl (relaxIns G s B (some Bi))
            (d1, (D1.merge Di).deleteSet Ui)).1
          D := insertMany G s
            (L.foldl (relaxIns G s B (some Bi))
              (d1, (D1.merge Di).deleteSet Ui)).2
            (reselected σ Ui piv')
            (L.foldl (relaxIns G s B (some Bi))
              (d1, (D1.merge Di).deleteSet Ui)).1
          P := fun j => σ.P j \ Ui
          piv := piv'
          U := σ.U ∪ Ui
          B' := B'i } σ' →
      LoopRelCert sub B τ σ σ'

/-- Recursive call relation using LoopRelCert. -/
def CallRelCert
    (FP : FPRel G s)
    (sub : WLab G s → Finset (Fin G.n) → Labels G s → Result G s → Prop)
    (B : WLab G s) (S : Finset (Fin G.n))
    (d0 : Labels G s) (τ : ℕ) (res : Result G s) : Prop :=
  ∃ (d1 : Labels G s) (p : ℕ)
    (P : Fin p → Finset (Fin G.n)) (Q W : Finset (Fin G.n))
    (piv : Fin p → Fin G.n) (σ : LState G s p)
    (L : List (Fin G.m)) (B'f : WLab G s)
    (T6 W' : Finset (Fin G.n)),
    FP B S d0 d1 p P Q W ∧
    (∀ j, piv j ∈ P j ∧ ∀ x ∈ P j, d1 (piv j) ≤ d1 x) ∧
    LoopRelCert G s sub B τ
      { d := d1
        D := insertMany G s DS.empty (Finset.univ.image piv) d1
        P := P
        piv := piv
        U := ∅
        B' := min B (Finset.univ.inf fun j => d1 (piv j)) } σ ∧
    (σ.D.IsEmpty → B'f = B) ∧
    (¬ σ.D.IsEmpty → B'f = σ.B') ∧
    (∀ x, x ∈ T6 ↔ x ∈ S ∧ B'f ≤ σ.d x ∧ σ.d x < B) ∧
    (∀ x, x ∈ W' ↔ (x ∈ W ∧ x ∉ σ.U) ∧ σ.d x < B'f) ∧
    Enumerates G L W' ∧
    res =
      (B'f, σ.U ∪ W',
        ((L.foldl (relaxIns G s B (some B'f))
          (σ.d, insertMany G s σ.D T6 σ.d)).2).deleteSet W',
        (L.foldl (relaxIns G s B (some B'f))
          (σ.d, insertMany G s σ.D T6 σ.d)).1)

/-- All-level BMSSP relation with certificate-oriented pulls. -/
def BMSSPRelCert (FP : FPRel G s) (τ : ℕ → ℕ) :
    ℕ → WLab G s → Finset (Fin G.n) →
      Labels G s → Result G s → Prop
  | 0 => fun B S d res => BaseRel G s B S d (τ 0) res
  | l + 1 => fun B S d res =>
      CallRelCert G s FP (BMSSPRelCert FP τ l)
        B S d (τ (l + 1)) res

variable {G s}

/-- The weaker-pull loop preserves exactly the same invariant. -/
theorem loop_inv_cert_candidate
    {B : WLab G s} {S : Finset (Fin G.n)}
    {d0 d1 : Labels G s} {p : ℕ}
    {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)}
    {B'0 : WLab G s}
    (hpre : CallPre B S d0)
    (hfp : FPContract B S d0 d1 p P0 Q W)
    {cap : ℕ}
    {sub : WLab G s → Finset (Fin G.n) →
      Labels G s → Result G s → Prop}
    (hsub : ∀ B S d res,
      CallPre B S d → sub B S d res →
      CallPost G s B S d cap res)
    {τ : ℕ} :
    ∀ σ σ' : LState G s p,
      LoopRelCert G s sub B τ σ σ' →
      LInv G s B S d0 d1 P0 B'0 σ →
      LInv G s B S d0 d1 P0 B'0 σ' ∧
        (τ < σ'.U.card ∨ σ'.D.IsEmpty) := by
  intro σ σ' hloop
  induction hloop with
  | stop σ hstop =>
      exact fun h => ⟨h, hstop⟩
  | step σ σ' S0 Bi D1 B'i Ui Di dsub L piv'
      _ hne hpull hsubrel hL hres _ ih =>
    intro h
    have hsp :=
      step_pre_cert_candidate hpre hfp h hpull
    have hpost := hsub _ _ _ _ hsp hsubrel
    exact ih
      (step_post_cert_candidate
        hpre hfp h hne hpull hpost hL hres)

/-- Recursive Lemma S2.1 under the weaker pull relation. -/
theorem callRel_post_cert_candidate
    {FP : FPRel G s} (hFP : FPSound G s FP)
    {sub : WLab G s → Finset (Fin G.n) →
      Labels G s → Result G s → Prop}
    {cap : ℕ}
    (hsub : ∀ B S d res,
      CallPre B S d → sub B S d res →
      CallPost G s B S d cap res)
    {B : WLab G s} {S : Finset (Fin G.n)}
    {d0 : Labels G s} {τ : ℕ} {res : Result G s}
    (hpre : CallPre B S d0)
    (hrel : CallRelCert G s FP sub B S d0 τ res) :
    CallPost G s B S d0 (τ + 1) res := by
  obtain ⟨d1, p, P, Q, W, piv, σ, L, B'f, T6, W',
    hfprel, hpiv, hloop, hB'e, hB'n, hT6, hW',
    hL, rfl⟩ := hrel
  have hfp : FPContract B S d0 d1 p P Q W :=
    hFP B S d0 d1 p P Q W hpre hfprel
  have h0 := linv_init hpre hfp hpiv
  obtain ⟨h, hstop⟩ :=
    loop_inv_cert_candidate hpre hfp hsub _ _ hloop h0
  exact final_post hpre hfp hpiv h hstop
    hB'e hB'n hT6 hW' hL

/-- All levels of the relational BMSSP remain correct under CertPullSpec. -/
theorem bmssp_post_cert_candidate
    {FP : FPRel G s} (hFP : FPSound G s FP)
    (τ : ℕ → ℕ) :
    ∀ (l : ℕ) (B : WLab G s)
      (S : Finset (Fin G.n)) (d : Labels G s)
      (res : Result G s),
      CallPre B S d →
      BMSSPRelCert G s FP τ l B S d res →
      CallPost G s B S d (τ l) res
  | 0, B, S, d, res, hpre, hrel =>
      baseRel_post hpre hrel
  | l + 1, B, S, d, res, hpre, hrel =>
      (callRel_post_cert_candidate
        hFP (bmssp_post_cert_candidate hFP τ l)
        hpre hrel).of_cap_le (Nat.le_succ _)

end BM
end CHD
end Frontier
