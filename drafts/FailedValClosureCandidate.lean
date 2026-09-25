/-!
# Reusing the final val-region of a failed FindPivots search

Upstream Search.failed_complete assumes the complete canonical witness is the
initial search root.  The path induction after failure needs only that the
witness belongs to the FINAL val set and is complete there.

This strengthening is useful for dormant-component batching: a later S-root
that already lies in an old failed component's final val set can share that
component's closure.  The implementation does not need to decide whether the
root is complete; FPContract only invokes the closure obligation when it is.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- Final-state form of failed-search completeness.

No distinguished initial root appears.  Any complete x in final val has all
below-B canonical descendants in final val with exact labels. -/
theorem failed_state_complete_from_val_candidate
    {c : FPCtx G s} (hout : OutOK c)
    {σ : SSt G s}
    (hI : SInv c σ)
    (hH : σ.H = ∅)
    (hcl :
      ∀ w ∈ σ.done, ∀ e ∈ c.out w, Closed c σ w e)
    (hD :
      ∀ e ∈ σ.D,
        dis (s := s) (G.dst e) < dis (s := s) (G.src e))
    {x v : Fin G.n}
    (hxval : x ∈ σ.val)
    (hx : Complete σ.d x)
    (hvis : OnPath (s := s) x v)
    (hvB : dis (s := s) v < c.B) :
    v ∈ σ.val ∧ Complete σ.d v := by
  have hsound : Sound σ.d := hI.walk.sound
  obtain ⟨R, hR, hwR⟩ := hvis.path_prefix
  have hPx : G.IsWalk s x (path (s := s) x) :=
    (path_isMinWalk hvis.reachable_left).1

  have main :
      ∀ R1 R2 : List (Fin G.m),
        R = R1 ++ R2 →
        ∀ z, G.IsWalk x z R1 →
          z ∈ σ.val ∧
          Complete σ.d z ∧
          dis (s := s) x ≤ dis (s := s) z ∧
          OnPath (s := s) z v := by
    intro R1
    induction R1 using List.reverseRecOn with
    | nil =>
        intro R2 _ z hz
        rw [isWalk_nil_iff] at hz
        subst hz
        exact ⟨hxval, hx, le_rfl, hvis⟩
    | append_singleton R0 e ih =>
        intro R2 hR12 z hz
        obtain ⟨hR0, rfl⟩ := IsWalk.concat_iff.mp hz
        obtain ⟨hyval, hyc, hxy, -⟩ :=
          ih ([e] ++ R2)
            (by rw [hR12, List.append_assoc]) _ hR0
        have hR2 : G.IsWalk (G.dst e) v R2 := by
          rw [hR12] at hwR
          obtain ⟨w, hw1, hw2⟩ := hwR.of_append
          obtain ⟨-, rfl⟩ := IsWalk.concat_iff.mp hw1
          exact hw2
        have hPR :
            path (s := s) v =
              (path (s := s) x ++ R0) ++ e :: R2 := by
          rw [hR, hR12]
          simp [List.append_assoc]
        obtain ⟨hdis, hon2, -⟩ :=
          dis_succ_on_path hvis.1 hPR
            (hPx.append hR0) hR2
        have hyext : G.src e ∈ σ.done := by
          rcases Finset.mem_union.mp (hI.valDone hyval) with h1 | h1
          · exact h1
          · rw [hH] at h1
            exact absurd h1 (Finset.notMem_empty _)
        have he : e ∈ c.out (G.src e) :=
          (hout _ e).mpr rfl
        have hcand :
            ext (σ.d (G.src e)) e =
              dis (s := s) (G.dst e) := by
          rw [hyc, hdis]
        have hzB :
            dis (s := s) (G.dst e) < c.B :=
          lt_of_le_of_lt hon2.dis_le hvB
        have hyfin :
            dis (s := s) (G.src e) ≠ ⊤ := by
          rw [dis_of_reachable ⟨_, hPx.append hR0⟩]
          exact WithTop.coe_ne_top
        have hxz :
            dis (s := s) x ≤
              dis (s := s) (G.dst e) := by
          rw [hdis]
          exact hxy.trans (lt_ext_of_ne_top hyfin e).le
        rcases hcl _ hyext e he
            (by rw [hcand]; exact hzB) with hF | ⟨hle', heq⟩
        · exfalso
          have h1 := hD e hF
          rw [hdis] at h1
          exact absurd h1
            (not_lt_of_ge (lt_ext_of_ne_top hyfin e).le)
        · rw [hcand] at hle' heq
          have hdeq :
              σ.d (G.dst e) =
                dis (s := s) (G.dst e) :=
            le_antisymm hle' (hsound _)
          exact ⟨heq hdeq, hdeq, hxz, hon2⟩

  obtain ⟨hvval, hvc, -, -⟩ :=
    main R [] (by simp) v hwR
  exact ⟨hvval, hvc⟩

/-- Corollary for an actual failed Search execution. -/
theorem Search.failed_complete_from_final_val_candidate
    {c : FPCtx G s}
    (hout : OutOK c) (hsort : OutSorted c)
    {T : Finset (Fin G.n)}
    {σ0 σ' : SSt G s} {n : ℕ}
    (h : Search c T σ0 σ' .failed n)
    (hI : SInv c σ0)
    (hCl :
      ∀ w ∈ σ0.done, ∀ e ∈ c.out w, Closed c σ0 w e)
    (hD :
      ∀ e ∈ σ'.D,
        dis (s := s) (G.dst e) < dis (s := s) (G.src e))
    {x v : Fin G.n}
    (hxval : x ∈ σ'.val)
    (hx : Complete σ'.d x)
    (hvis : OnPath (s := s) x v)
    (hvB : dis (s := s) v < c.B) :
    v ∈ σ'.val ∧ Complete σ'.d v := by
  obtain ⟨hI', -, -, -, hf⟩ :=
    Search.inv hout hsort h hI hCl
  obtain ⟨hH, -, hclosed⟩ := hf rfl
  exact failed_state_complete_from_val_candidate
    hout hI' hH hclosed hD hxval hx hvis hvB

/-- One failed final val-region may certify arbitrarily many Q roots at once.
The algorithm only needs to record that each such root lies in final val; no
runtime completeness test is required. -/
theorem failed_val_qroots_candidate
    {c : FPCtx G s} (hout : OutOK c)
    {σ : SSt G s}
    (hI : SInv c σ)
    (hH : σ.H = ∅)
    (hcl :
      ∀ w ∈ σ.done, ∀ e ∈ c.out w, Closed c σ w e)
    (hD :
      ∀ e ∈ σ.D,
        dis (s := s) (G.dst e) < dis (s := s) (G.src e))
    {Q : Finset (Fin G.n)}
    (hQ : Q ⊆ σ.val) :
    ∀ q ∈ Q, ∀ v,
      Complete σ.d q →
      OnPath (s := s) q v →
      dis (s := s) v < c.B →
      v ∈ σ.val ∧ Complete σ.d v := by
  intro q hq v hqc hqv hvB
  exact failed_state_complete_from_val_candidate
    hout hI hH hcl hD (hQ hq) hqc hqv hvB

end CHD
end Frontier
