/-!
# Candidate full-call cost assembly under a fresh-init bound

Purpose: prove that once BM.6 initCost is repriced linearly in p, the
existing CallC relation plus the compiled terminal loop credit yields the
refined full-call record cost with +I*p credit on the left.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}
variable {DC : DCost} {out : Fin G.n → List (Fin G.m)}
variable {k hins hext : ℕ}

theorem callC_cost_full_credit_given_init_candidate
    (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hsimp : ∀ u, ((out u).map G.dst).Nodup)
    (hk : 2 ≤ k)
    {τ : ℕ → ℕ}
    {sub : SubRelC G s (Finset (Fin G.m)) (FPData G s)}
    {l : ℕ}
    (hsub : GoodSub G s τ (DelInv G s) l sub)
    {Blow B : WLab G s} {S : Finset (Fin G.n)}
    {d0 : Labels G s} {φ0 φ2 : Finset (Fin G.m)}
    {τl : ℕ} {res : Result G s}
    {lg : Log G s (FPData G s)}
    (hpre : CallPre B S d0)
    (hI : DelInv G s φ0)
    (hlow : ∀ x ∈ S, Blow ≤ dis (s := s) x)
    (hrel : CallC G s (fpC G s out k hins hext) DC sub
      (l + 1) Blow B S d0 φ0 τl res φ2 lg)
    (hfull : res.1 = B)
    {ap bp ad bd I nw initI : ℕ}
    (hpull : ∀ x, DC.pull (l + 1) x ≤ ap * x + bp)
    (hdel : ∀ x, DC.del (l + 1) x ≤ ad * x + bd)
    (hinsI : DC.ins (l + 1) ≤ I)
    (hMτ : DC.M (l + 1) ≤ τ l)
    (hgMτ : 3 * k * DC.M (l + 1) ≤ τ l)
    (hinit : ∀ (p : ℕ) (P : Fin p → Finset (Fin G.n)),
      initCost DC (l + 1) p P ≤
        nw + (∑ j, (P j).card) + p * (2 + initI)) :
    ∃ (r : CallRec G s (FPData G s))
      (lgc : Log G s (FPData G s))
      (ω : FPData G s) (p : ℕ)
      (P : Fin p → Finset (Fin G.n))
      (W' : Finset (Fin G.n)),
      lg = ([], r) :: lgc ∧
      r.fp = some ω ∧ r.p = p ∧ r.B' = r.B ∧ r.W' = W' ∧
      (∀ j, P j ⊆ r.S) ∧
      (∃ hp : p = (forestGroups r.S r.Q k ω.trees).length,
        ∀ j, P j =
          ((forestGroups r.S r.Q k ω.trees).get (Fin.cast hp j)).toFinset) ∧
      r.cost + I * p ≤
        scanC * (ω.Dout \ ω.Din).card
          + fpA k hins hext *
              ((ω.trees.flatMap (fun T => T.ord)).length + k * r.Q.card)
          + 3 * r.S.card
          + (nw + r.S.card + p * (2 + initI))
          + (1 + childSum
              (childCharge P
                (1 + bp + bd) (ap + ad + 4)
                (2 * (3 * k) + 1 + I)) lgc
              + (1 + I) * r.J.card
              + I * terminalOwnGroups P W')
          + r.cMerge
          + (1 + r.S.card + r.W.card + r.W'.card
              + r.Wr.card * (1 + I)
              + (ad * r.W'.card + bd)
              + r.S.card) := by
  classical
  obtain ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, σ, lgc, J, cm, cl, L,
    B'f, T6, W', hfprel, hpiv, hloop, hB'e, hB'n, hT6, hW', hL,
    hres, hlg⟩ := hrel
  have hlow' : ∀ x ∈ S, Blow ≤ d0 x :=
    fun x hx => (hlow x hx).trans (hpre.walk.sound x)
  obtain ⟨hfp, hI1⟩ :=
    fpC_sound hout hsort hsimp hk
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hI hlow' hfprel
  obtain ⟨-, -, hsz, -, -⟩ :=
    fpC_spec hout hsort hsimp hk hpre hI hfprel
  have hcfp := fpC_cost_del hout hsort hsimp hk hpre hI hfprel
  have h0 := linv_init hpre hfp hpiv
  obtain ⟨hfinal, hstop, -, -⟩ :=
    loopC_log hpre hfp hsub
      0 (initState B d1 P piv) φ1 σ φ2 lgc J cm cl
      hloop h0 hI1
  have hpost : CallPost G s B S d0 (τl + 1)
      (B'f, σ.U ∪ W',
        ((L.foldl (relaxIns G s B (some B'f))
          (σ.d, insertMany G s σ.D T6 σ.d)).2).deleteSet W',
        (L.foldl (relaxIns G s B (some B'f))
          (σ.d, insertMany G s σ.D T6 σ.d)).1) :=
    final_post hpre hfp hpiv hfinal hstop hB'e hB'n hT6 hW' hL
  have hfull' : B'f = B := by
    have := hfull
    rw [hres] at this
    exact this
  have hfullS : S ⊆ σ.U ∪ W' := by
    intro x hx
    have hx0 := S_sub_of_pre hpre x hx
    have hx1 : x ∈ Utilde B'f (S : Set (Fin G.n)) := by
      rw [hfull']
      exact hx0
    exact (hpost.U_eq x).mpr hx1
  have hP0 : ∀ j, (P j).card ≤ 3 * k :=
    fun j => le_of_lt (hsz j)
  have hlc :=
    loopC_cost_full_terminal_credit_candidate
      (DC := DC) hpre hfp hsub hpull hdel hinsI hP0 hMτ hgMτ
      hpiv hloop hI1 hfullS
  have hsumP : ∑ j, (P j).card ≤ S.card :=
    sum_card_le_of_disjoint (fun j => (hfp.groups j).2) hfp.gdisj
  have hinit' : initCost DC (l + 1) p P ≤
      nw + S.card + p * (2 + initI) := by
    have hi := hinit p P
    omega
  have hT6empty : T6 = ∅ := by
    ext x
    simp only [Finset.notMem_empty, iff_false]
    intro hx
    obtain ⟨-, h1, h2⟩ := (hT6 x).mp hx
    rw [hfull'] at h1
    exact (lt_irrefl _ (lt_of_le_of_lt h1 h2))
  have hLlen : L.length = L.toFinset.card :=
    (List.toFinset_card_of_nodup hL.1).symm
  have e1 : DC.del (l + 1) W'.card ≤ ad * W'.card + bd := hdel _
  have e3 : L.length * (1 + DC.ins (l + 1)) ≤
      L.toFinset.card * (1 + I) := by
    rw [hLlen]
    exact Nat.mul_le_mul_left _ (by omega)
  have hsumP' : ∑ j, (P j).card ≤ S.card := hsumP
  have hpin := hfprel.2.2.1
  subst lg
  rw [hres] at hfull
  refine ⟨_, lgc, ω, p, P, W', rfl, rfl, rfl, ?_, rfl,
    fun j => (hfp.groups j).2, hpin, ?_⟩
  · exact hfull'
  · simp only
    unfold finCost
    rw [hT6empty]
    simp only [Finset.card_empty, zero_mul, Nat.zero_add]
    omega

end BM
end CHD
end Frontier