/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The synchronized climb of the rover ladders' reference chain

When the declared rows tie the reference's attitude to the deployed's clock (energy rows in
`ψ_L − ψ_R`, `θ_L − θ_R`), the reference cannot run ahead: it answers a left window by running
for exactly the window's duration. Its band guards (`STEEP`: `s < 0.6`, `MODER`:
`0.6 ≤ s < 1.4`, `FLAT`: `s ≥ 1.4`) then force switches INSIDE the window: the reference runs
its band until its odometer reaches the next band's floor, switches there (legal: the floor is
in the entered band's guard), and goes on in the next band, until the window's end, where it
takes the self-loop of the band it is in (legal: its odometer is in that band).

The anchors (one per right band, for the window's left mode) are box invariants of the joint
flows (`couple_box_cutX` for a certified pair); at a switch point the anchor of the entered
band holds (`hhand`: the entered band's kept atom is the odometer floor, which the reference
sits on). Along every stretch the joint trajectory is a run of the pair's joint system
(`joint_of_sols`), so the anchor holds at the window's end for the band the reference ends in.

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.LadderClimb
import RelCertifier.Proofs.Encoding.SyncSwitch

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

/-- The band of `q` on the odometer `s = Rv 1` (`STEEP` `[0, 0.6)`, `MODER` `[0.6, 1.4)`,
`FLAT` `[1.4, ∞)`). -/
def ladBand (q : ℕ) (x : State (Var (n+2))) : Prop :=
  (q = 0 → 0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5) ∧ (q = 1 → 3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5) ∧
    (q = 2 → 7/5 ≤ x (Rv 1))

section
variable {G : SearchGraph (Var (n+2))} {domR : Formula (Var (n+2))} (LR : LadderRun G domR)
  (fR : ℕ → Fin (n+2) → Term (Var (n+2)))
  (hsys : ∀ q < 3, (LR.m q).sys = rightBlock (fR q) (Term.const 1))
  (fL : Fin (n+2) → Term (Var (n+2))) (domL : Formula (Var (n+2))) (tg : Var (n+2))
  (htgL : ∀ i, tg ≠ Lv i) (htgR : ∀ i, tg ≠ Rv i)
  (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hfR : ∀ q < 3, ∀ i, (fR q i).fv ⊆ range Rv)
  (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv)
  {x : State (Var (n+2))} {r : ℝ} {ΦL : ℝ → State (Var (n+2))}
  (hL : ODESol (clk tg (leftBlock fL)) domL x r ΦL) (ω₀ : State (Var (n+2)))
  (A : ℕ → Formula (Var (n+2)))
  (hbox : ∀ q < 3, ∀ σ ω, Formula.sat (A q) σ →
    Program.sem (Program.ode (jointSys fL (fR q) (Term.const 1)) (Formula.and domL domR)) σ ω →
    Formula.sat (A q) ω)

include hsys htgL htgR hfL hfR hdomL hdomR hL hbox in
/-- **One synchronized stretch.** The anchor of band `q` at the merged state at time `a`
(left from the left run, right `ρ`) holds at time `b` with the right at the end of `q`'s run
of duration `b − a`. -/
theorem sync_stretch (q : ℕ) (hq : q < 3) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ r)
    (ρ : State (Var (n+2))) (hρ : Formula.sat domR ρ)
    (hA : Formula.sat (A q) (mergeLR ω₀ (ΦL a) ρ)) :
    Formula.sat (A q) (mergeLR ω₀ (ΦL b) (LR.run q ρ (b - a))) := by
  have hLs := odeSol_shift hL ha hab hb
  have hRs := LR.sol q hq ρ hρ (b - a) (by linarith)
  rw [hsys q hq, LR.dom_m q hq] at hRs
  have hj := joint_of_sols tg htgL htgR hfL (hfR q hq) hdomL hdomR hLs hRs ω₀
  have h0 : (fun t => ΦL (a + t)) 0 = ΦL a := by simp
  have h1 : (fun t => ΦL (a + t)) (b - a) = ΦL b := by simp
  have h2 : (fun t => LR.run q ρ t) 0 = ρ := hRs.hΦ0
  simp only [h0, h1, h2] at hj
  exact hbox q hq _ _ hA hj

end

/-- **The synchronized climb.** From band `q` at time `a` of the left window (right state `ρ`
in the band, the anchor of `q` at the merged state), the reference answers the rest of the
window `[a, r]` legally (switching at the band floors it reaches, the self-loop at the end)
and ends at a state `μ` whose merged state with the left window's end satisfies the anchor
of the band it ends in. -/
theorem syncClimb {G : SearchGraph (Var (n+2))} {domR : Formula (Var (n+2))}
    (LR : LadderRun G domR) (fR : ℕ → Fin (n+2) → Term (Var (n+2)))
    (hsys : ∀ q < 3, (LR.m q).sys = rightBlock (fR q) (Term.const 1))
    (fL : Fin (n+2) → Term (Var (n+2))) (domL : Formula (Var (n+2))) (tg : Var (n+2))
    (htgL : ∀ i, tg ≠ Lv i) (htgR : ∀ i, tg ≠ Rv i)
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hfR : ∀ q < 3, ∀ i, (fR q i).fv ⊆ range Rv)
    (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv)
    {x : State (Var (n+2))} {r : ℝ} {ΦL : ℝ → State (Var (n+2))}
    (hL : ODESol (clk tg (leftBlock fL)) domL x r ΦL) (ω₀ : State (Var (n+2)))
    (A : ℕ → Formula (Var (n+2)))
    (hbox : ∀ q < 3, ∀ σ ω, Formula.sat (A q) σ →
      Program.sem (Program.ode (jointSys fL (fR q) (Term.const 1)) (Formula.and domL domR)) σ ω →
      Formula.sat (A q) ω)
    (hhand : ∀ q < 2, ∀ y, Formula.sat (A q) y → y (Rv 1) = (if q = 0 then 3/5 else 7/5) →
      Formula.sat (A (q+1)) y)
    (e00 e01 e11 e12 e22 : REdge (Var (n+2)))
    (m00 : e00 ∈ G.edgesFrom 0) (m01 : e01 ∈ G.edgesFrom 0) (m11 : e11 ∈ G.edgesFrom 1)
    (m12 : e12 ∈ G.edgesFrom 1) (m22 : e22 ∈ G.edgesFrom 2)
    (t00 : e00.tgt = 0) (t01 : e01.tgt = 1) (t11 : e11.tgt = 1) (t12 : e12.tgt = 2)
    (t22 : e22.tgt = 2)
    (leg00 : ∀ y, 0 ≤ y (Rv 1) → y (Rv 1) < 3/5 → SwitchLegal e00 y)
    (leg01 : ∀ y, y (Rv 1) = 3/5 → SwitchLegal e01 y)
    (leg11 : ∀ y, 3/5 ≤ y (Rv 1) → y (Rv 1) < 7/5 → SwitchLegal e11 y)
    (leg12 : ∀ y, y (Rv 1) = 7/5 → SwitchLegal e12 y)
    (leg22 : ∀ y, 7/5 ≤ y (Rv 1) → SwitchLegal e22 y)
    (x₀ : State (Var (n+2))) (post : ℕ → Formula (Var (n+2)))
    (hpost : ∀ q < 3, ∀ μ, (∀ i, μ (Lv i) = x₀ (Lv i)) → Formula.sat domR μ → ladBand q μ →
      Formula.sat (A q) (mergeLR ω₀ (ΦL r) μ) → Formula.sat (post q) μ) :
    ∀ q < 3, ∀ a, 0 ≤ a → a ≤ r → ∀ ρ, (∀ i, ρ (Lv i) = x₀ (Lv i)) → Formula.sat domR ρ →
      ladBand q ρ → Formula.sat (A q) (mergeLR ω₀ (ΦL a) ρ) → RResp G q post ρ := by
  have stretch := fun q hq a b ha hab hb ρ hρ hA =>
    sync_stretch LR fR hsys fL domL tg htgL htgR hfL hfR hdomL hdomR hL ω₀ A hbox q hq
      (a := a) (b := b) ha hab hb ρ hρ hA
  -- band `q`'s run to the window's end, the self-loop `e` legal at the end
  have toEnd : ∀ q (hq : q < 3) (e : REdge (Var (n+2))), e ∈ G.edgesFrom q → e.tgt = q →
      ∀ a, 0 ≤ a → a ≤ r → ∀ ρ, (∀ i, ρ (Lv i) = x₀ (Lv i)) → Formula.sat domR ρ →
      Formula.sat (A q) (mergeLR ω₀ (ΦL a) ρ) →
      SwitchLegal e (LR.run q ρ (r - a)) → ladBand q (LR.run q ρ (r - a)) →
      RResp G q post ρ := by
    intro q hq e he het a ha har ρ hρL hρ hA hleg hband
    have hrun := LR.sem q hq ρ hρ (r - a) (by linarith)
    have hstep := rresp_step (post := post) (LR.modeAt q hq) he hrun hleg
    rw [het] at hstep
    refine hstep (rresp_stop (hpost q hq _ (fun i => (LR.left q ρ (r - a) i).trans (hρL i))
      (LR.end_dom q hq ρ hρ (r - a) (by linarith)) hband ?_))
    exact stretch q hq a r ha har le_rfl ρ hρ hA
  -- band `q` up to the floor `L` of band `q+1` (reached inside the window), the switch `e`,
  -- then the rest from band `q+1`
  have hit : ∀ q (hq : q < 2) (e : REdge (Var (n+2))), e ∈ G.edgesFrom q → e.tgt = q + 1 →
      ∀ L : ℝ, L = (if q = 0 then 3/5 else 7/5) → (∀ y, y (Rv 1) = L → SwitchLegal e y) →
      (∀ a, 0 ≤ a → a ≤ r → ∀ ρ, (∀ i, ρ (Lv i) = x₀ (Lv i)) → Formula.sat domR ρ →
        ladBand (q+1) ρ → Formula.sat (A (q+1)) (mergeLR ω₀ (ΦL a) ρ) →
        RResp G (q+1) post ρ) →
      ∀ a, 0 ≤ a → a ≤ r → ∀ ρ, (∀ i, ρ (Lv i) = x₀ (Lv i)) → Formula.sat domR ρ →
      ρ (Rv 1) ≤ L → L ≤ LR.run q ρ (r - a) (Rv 1) →
      Formula.sat (A q) (mergeLR ω₀ (ΦL a) ρ) → RResp G q post ρ := by
    intro q hq e he het L hL0 hlegL hnext a ha har ρ hρL hρ hlo hhi hA
    have hcont : ContinuousOn (fun t => LR.run q ρ t (Rv 1)) (Icc 0 (r - a)) :=
      (LR.s_cont q (by omega) ρ).continuousOn
    have h0 : LR.run q ρ 0 (Rv 1) = ρ (Rv 1) := LR.zero q ρ
    obtain ⟨τ, hτ, hτs⟩ := intermediate_value_Icc (by linarith) hcont
      ⟨by rw [h0]; exact hlo, hhi⟩
    simp only at hτs
    have hrun := LR.sem q (by omega) ρ hρ τ hτ.1
    have hstep := rresp_step (post := post) (LR.modeAt q (by omega)) he hrun (hlegL _ hτs)
    rw [het] at hstep
    refine hstep (hnext (a + τ) (by linarith [hτ.1]) (by linarith [hτ.2]) _
      (fun i => (LR.left q ρ τ i).trans (hρL i)) (LR.end_dom q (by omega) ρ hρ τ hτ.1) ?_ ?_)
    · -- the floor of band `q+1` is in its band
      refine ⟨fun h => absurd h (by omega), fun h => ?_, fun h => ?_⟩
      · have : q = 0 := by omega
        subst this; simp at hL0; rw [hτs, hL0]; norm_num
      · have : q = 1 := by omega
        subst this; simp at hL0; rw [hτs, hL0]
    · have hA' := stretch q (by omega) a (a + τ) ha (by linarith [hτ.1]) (by linarith [hτ.2])
        ρ hρ hA
      rw [show a + τ - a = τ by ring] at hA'
      exact hhand q hq _ hA' (by
        rw [mergeLR_R]; rw [hτs, hL0])
  -- FLAT
  have s2 : ∀ a, 0 ≤ a → a ≤ r → ∀ ρ, (∀ i, ρ (Lv i) = x₀ (Lv i)) → Formula.sat domR ρ →
      ladBand 2 ρ → Formula.sat (A 2) (mergeLR ω₀ (ΦL a) ρ) → RResp G 2 post ρ := by
    intro a ha har ρ hρL hρ hband hA
    have hs := (LR.s_low 2 (by norm_num) ρ hρ (r - a) (by linarith)).2
    have h14 := hband.2.2 rfl
    exact toEnd 2 (by norm_num) e22 m22 t22 a ha har ρ hρL hρ hA (leg22 _ (by linarith))
      ⟨fun h => absurd h (by norm_num), fun h => absurd h (by norm_num), fun _ => by linarith⟩
  -- MODER
  have s1 : ∀ a, 0 ≤ a → a ≤ r → ∀ ρ, (∀ i, ρ (Lv i) = x₀ (Lv i)) → Formula.sat domR ρ →
      ladBand 1 ρ → Formula.sat (A 1) (mergeLR ω₀ (ΦL a) ρ) → RResp G 1 post ρ := by
    intro a ha har ρ hρL hρ hband hA
    have hs := (LR.s_low 1 (by norm_num) ρ hρ (r - a) (by linarith)).2
    obtain ⟨hlo, hhi⟩ := hband.2.1 rfl
    by_cases hend : LR.run 1 ρ (r - a) (Rv 1) < 7/5
    · exact toEnd 1 (by norm_num) e11 m11 t11 a ha har ρ hρL hρ hA
        (leg11 _ (by linarith) hend)
        ⟨fun h => absurd h (by norm_num), fun _ => ⟨by linarith, hend⟩,
          fun h => absurd h (by norm_num)⟩
    · exact hit 1 (by norm_num) e12 m12 t12 (7/5) (by norm_num) leg12 s2 a ha har ρ hρL hρ
        (le_of_lt hhi) (not_lt.mp hend) hA
  intro q hq
  interval_cases q
  · intro a ha har ρ hρL hρ hband hA
    have hs := (LR.s_low 0 (by norm_num) ρ hρ (r - a) (by linarith)).2
    obtain ⟨hlo, hhi⟩ := hband.1 rfl
    by_cases hend : LR.run 0 ρ (r - a) (Rv 1) < 3/5
    · exact toEnd 0 (by norm_num) e00 m00 t00 a ha har ρ hρL hρ hA
        (leg00 _ (by linarith) hend)
        ⟨fun _ => ⟨by linarith, hend⟩, fun h => absurd h (by norm_num),
          fun h => absurd h (by norm_num)⟩
    · exact hit 0 (by norm_num) e01 m01 t01 (3/5) (by norm_num) leg01 s1 a ha har ρ hρL hρ
        (le_of_lt hhi) (not_lt.mp hend) hA
  · exact s1
  · exact s2

end RelCertifier
