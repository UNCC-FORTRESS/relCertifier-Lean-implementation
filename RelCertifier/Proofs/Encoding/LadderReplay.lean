/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The rover ladders' switching choreography for the cover replay

Every rover-ladder benchmark's right automaton is the one-way chain `STEEP → MODER → FLAT`
(bands of the odometer `s = Rv 1`: `[0, 0.6)`, `[0.6, 1.4)`, `[1.4, ∞)`), with or without a
speed cap `v ≤ c_q` in each band's guard (`Cap`). The cover replay (`ReplayEngine`) takes its
preservation facts from the packs; this file supplies, once for all ladders, the part the cover
does not: where the right switches, and that every switch is legal.

* `ladder_hmove`: at a joint node, the right runs its band; if its odometer reaches the next
  band's floor within the remaining time it switches there (legal: the floor is in the entered
  band, the cap is inherited), otherwise it takes its band's self-loop at the end (legal: it is
  still in its band). The runs are the benchmark's explicit band runs (`LadderRun`).
* `ladder_hexit`: at a reposition node, the right runs its band alone to the next floor and
  switches up (the only exit of a chain node).

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.ReplayEngine
import RelCertifier.Proofs.Encoding.LadderSync

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

/-- The ladder's right-only precondition at band `q`: the band, the cap, the envelope. -/
def ladPre (Cap : ℕ → State (Var (n+2)) → Prop) (dom : Formula (Var (n+2))) (q : ℕ)
    (x : State (Var (n+2))) : Prop :=
  q < 3 ∧ ladBand q x ∧ Cap q x ∧ Formula.sat dom x

section
variable {G : SearchGraph (Var (n+2))} {dom : Formula (Var (n+2))} (LR : LadderRun G dom)
  (Cap : ℕ → State (Var (n+2)) → Prop)
  (hCapRun : ∀ q < 3, ∀ ρ, Formula.sat dom ρ → Cap q ρ → ∀ τ, 0 ≤ τ → Cap q (LR.run q ρ τ))
  (hCapUp : ∀ q < 2, ∀ x, Cap q x → Cap (q+1) x)
  (e00 e11 : REdge (Var (n+2))) (m00 : e00 ∈ G.edgesFrom 0) (m11 : e11 ∈ G.edgesFrom 1)
  (t00 : e00.tgt = 0) (t11 : e11.tgt = 1)
  (leg00 : ∀ x, 0 ≤ x (Rv 1) → x (Rv 1) < 3/5 → Cap 0 x → SwitchLegal e00 x)
  (leg01 : ∀ x, x (Rv 1) = 3/5 → Cap 0 x → SwitchLegal LR.e01 x)
  (leg11 : ∀ x, 3/5 ≤ x (Rv 1) → x (Rv 1) < 7/5 → Cap 1 x → SwitchLegal e11 x)
  (leg12 : ∀ x, x (Rv 1) = 7/5 → Cap 1 x → SwitchLegal LR.e12 x)
  (leg22 : ∀ x, 7/5 ≤ x (Rv 1) → Cap 2 x → SwitchLegal LR.e22 x)

include hCapRun hCapUp m00 m11 t00 t11 leg00 leg01 leg11 leg12 leg22 in
/-- **The ladder choreography at joint nodes.** Joint nodes `J` closed upward along the chain;
`E` any end condition implied by the precondition at the entered band. -/
theorem ladder_hmove (J : ℕ → Prop)
    (hJup : ∀ q, J q → q < 2 → J (q+1)) (E : ℕ → State (Var (n+2)) → Prop)
    (hE : ∀ q x, J q → ladPre Cap dom q x → E q x) :
    HMove G LR.m J (fun q => q) (ladPre Cap dom) E := by
  intro q hq ρ ⟨hq3, hband, hcap, hdom⟩ T hT
  have hsol := LR.sol q hq3 ρ hdom T hT
  have hsT := (LR.s_low q hq3 ρ hdom T hT).2
  have hcapT := hCapRun q hq3 ρ hdom hcap T hT
  have hdomT := LR.end_dom q hq3 ρ hdom T hT
  -- the step into the next band at its floor, inside the remaining time
  have hit : ∀ (hq2 : q < 2) (e : REdge (Var (n+2))), e ∈ G.edgesFrom q → e.tgt = q + 1 →
      (∀ x, x (Rv 1) = (if q = 0 then 3/5 else 7/5) → Cap q x → SwitchLegal e x) →
      ρ (Rv 1) ≤ (if q = 0 then 3/5 else 7/5) →
      (if q = 0 then (3:ℝ)/5 else 7/5) ≤ LR.run q ρ T (Rv 1) →
      (∃ τ, 0 ≤ τ ∧ τ ≤ T ∧ ∃ Φ, ODESol (LR.m q).sys (LR.m q).dom ρ τ Φ ∧
        ∃ e ∈ G.edgesFrom q, SwitchLegal e (Φ τ) ∧ J e.tgt ∧ q < e.tgt ∧
          ladPre Cap dom e.tgt (Φ τ)) := by
    intro hq2 e he het hleg hlo hhi
    have hcont : ContinuousOn (fun t => LR.run q ρ t (Rv 1)) (Icc 0 T) :=
      (LR.s_cont q hq3 ρ).continuousOn
    obtain ⟨τ, hτ, hτs⟩ := intermediate_value_Icc hT hcont
      ⟨by rw [LR.zero q ρ]; exact hlo, hhi⟩
    simp only at hτs
    refine ⟨τ, hτ.1, hτ.2, fun t => LR.run q ρ t, LR.sol q hq3 ρ hdom τ hτ.1, e, he, ?_, ?_, ?_, ?_⟩
    · exact hleg _ hτs (hCapRun q hq3 ρ hdom hcap τ hτ.1)
    · rw [het]; exact hJup q hq hq2
    · rw [het]; omega
    · rw [het]
      refine ⟨by omega, ?_, hCapUp q hq2 _ (hCapRun q hq3 ρ hdom hcap τ hτ.1),
        LR.end_dom q hq3 ρ hdom τ hτ.1⟩
      refine ⟨fun h => absurd h (by omega), fun h => ?_, fun h => ?_⟩
      · have : q = 0 := by omega
        subst this; simp at hτs; show _ ≤ LR.run 0 ρ τ (Rv 1) ∧ LR.run 0 ρ τ (Rv 1) < _
        rw [hτs]; norm_num
      · have : q = 1 := by omega
        subst this; simp at hτs; show _ ≤ LR.run 1 ρ τ (Rv 1)
        rw [hτs]
  interval_cases q
  · -- STEEP
    obtain ⟨hlo0, hhi0⟩ := hband.1 rfl
    by_cases hend : LR.run 0 ρ T (Rv 1) < 3/5
    · left
      refine ⟨fun t => LR.run 0 ρ t, hsol, e00, m00, leg00 _ (by linarith) hend hcapT, ?_⟩
      rw [t00]
      refine hE 0 _ hq ⟨by norm_num, ⟨fun _ => ⟨by linarith, hend⟩, fun h => absurd h (by norm_num),
        fun h => absurd h (by norm_num)⟩, hcapT, hdomT⟩
    · right
      exact hit (by norm_num) LR.e01 LR.e01_mem LR.e01_tgt (by simpa using leg01)
        (by simp; linarith) (by simpa using not_lt.mp hend)
  · -- MODER
    obtain ⟨hlo1, hhi1⟩ := hband.2.1 rfl
    by_cases hend : LR.run 1 ρ T (Rv 1) < 7/5
    · left
      refine ⟨fun t => LR.run 1 ρ t, hsol, e11, m11, leg11 _ (by linarith) hend hcapT, ?_⟩
      rw [t11]
      refine hE 1 _ hq ⟨by norm_num, ⟨fun h => absurd h (by norm_num), fun _ => ⟨by linarith, hend⟩,
        fun h => absurd h (by norm_num)⟩, hcapT, hdomT⟩
    · right
      exact hit (by norm_num) LR.e12 LR.e12_mem LR.e12_tgt (by simpa using leg12)
        (by simp; linarith) (by simpa using not_lt.mp hend)
  · -- FLAT
    have hlo2 := hband.2.2 rfl
    left
    refine ⟨fun t => LR.run 2 ρ t, hsol, LR.e22, LR.e22_mem, leg22 _ (by linarith) hcapT, ?_⟩
    rw [LR.e22_tgt]
    exact hE 2 _ hq ⟨by norm_num, ⟨fun h => absurd h (by norm_num),
      fun h => absurd h (by norm_num), fun _ => by linarith⟩, hcapT, hdomT⟩

include hCapRun hCapUp leg01 leg12 in
/-- **The ladder's reposition exits.** A reposition node below the joint nodes runs its band
alone to the next floor and switches up (the chain's only exit); reposition rank `2 − q`. -/
theorem ladder_hexit (J D : ℕ → Prop)
    (hnext : ∀ q, D q → ¬ J q → q < 2 ∧ (J (q+1) ∨ (D (q+1) ∧ ¬ J (q+1)))) :
    HExit G LR.m J D (fun q => 2 - q) (ladPre Cap dom) (ladPre Cap dom) := by
  intro q hD hnJ ρ ⟨hq3, hband, hcap, hdom⟩
  obtain ⟨hq2, hnx⟩ := hnext q hD hnJ
  have hlo : ρ (Rv 1) ≤ (if q = 0 then 3/5 else 7/5) := by
    interval_cases q
    · simp; linarith [(hband.1 rfl).2]
    · simp; linarith [(hband.2.1 rfl).2]
  obtain ⟨τ, hτ, hτs⟩ := LR.reach q hq3 ρ hdom _ hlo
  have hcapτ := hCapRun q hq3 ρ hdom hcap τ hτ
  have hpre : ladPre Cap dom (q+1) (LR.run q ρ τ) := by
    refine ⟨by omega, ?_, hCapUp q hq2 _ hcapτ, LR.end_dom q hq3 ρ hdom τ hτ⟩
    refine ⟨fun h => absurd h (by omega), fun h => ?_, fun h => ?_⟩
    · have : q = 0 := by omega
      subst this; simp at hτs; rw [hτs]; norm_num
    · have : q = 1 := by omega
      subst this; simp at hτs; rw [hτs]
  refine ⟨τ, fun t => LR.run q ρ t, LR.sol q hq3 ρ hdom τ hτ, ?_⟩
  interval_cases q
  · refine ⟨LR.e01, LR.e01_mem, leg01 _ (by simpa using hτs) hcapτ, by rw [LR.e01_tgt]; omega,
      by rw [LR.e01_tgt]; show 2 - 1 < 2 - 0; omega, ?_⟩
    rw [LR.e01_tgt]
    rcases hnx with h | ⟨h, h'⟩
    · exact Or.inl ⟨h, hpre⟩
    · exact Or.inr ⟨h, h', hpre⟩
  · refine ⟨LR.e12, LR.e12_mem, leg12 _ (by simpa using hτs) hcapτ, by rw [LR.e12_tgt]; omega,
      by rw [LR.e12_tgt]; show 2 - 2 < 2 - 1; omega, ?_⟩
    rw [LR.e12_tgt]
    rcases hnx with h | ⟨h, h'⟩
    · exact Or.inl ⟨h, hpre⟩
    · exact Or.inr ⟨h, h', hpre⟩

end

/-- The speed cap of the capped ladders (`v ≤ c_q`), kept along every band run. -/
theorem ladCap_run {G : SearchGraph (Var (n+2))} {dom : Formula (Var (n+2))} (LR : LadderRun G dom) :
    ∀ q < 3, ∀ ρ, Formula.sat dom ρ → ρ (Rv 0) ≤ ladC q → ∀ τ, 0 ≤ τ →
      LR.run q ρ τ (Rv 0) ≤ ladC q :=
  fun q hq ρ _ hv _ hτ => (LR.v_mono q hq ρ hv hτ).2

theorem ladCap_up : ∀ q < 2, ∀ x : State (Var (n+2)), x (Rv 0) ≤ ladC q → x (Rv 0) ≤ ladC (q+1) :=
  fun q _ x h => le_trans h (ladC_mono_le q (q+1) (by omega))

end RelCertifier
