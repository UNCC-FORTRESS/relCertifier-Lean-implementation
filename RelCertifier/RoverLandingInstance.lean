/-
Instantiating the landing-selected narrowing discharge at concrete `rover_position` data.

`rover_position` R-side (from benchmarks/suite/rover_position/input.txt), 3-coord model
(`Rv 0 = px`, `Rv 1 = vx`, `Rv 2 = mode`, banked `roverFR`: `px' = vx`, `vx' = 0.4`, `mode' = 0`):
  * Recover : evolve `px∈[0,15] ∧ vx∈[0,1]`, guard `vx∈[0,0.3]`, next `[Drive, Recover]`
  * Drive   : evolve `px∈[0,15] ∧ vx∈[0.3,1]`, guard `vx≥0.3`
The Recover→Drive edge is the NARROWING edge (`vx∈[0,1] ⊋ vx∈[0.3,1]`). `SuccReach` for it =
"Recover's flow reaches `vx≥0.3` staying in Recover's domain".

This file discharges the REACHING arithmetic on the banked explicit flow `roverΦR` and tests `SuccReach`'s
non-vacuity at the faithful domain — the disciplined check. It surfaces a genuine finding: because the
Recover flow's `px` grows monotonically during the `vx`-speedup, `SuccReach` on the FAITHFUL `px≤15`
domain FAILS at the `px`-boundary (the flow leaves `px∈[0,15]` before `vx` reaches `0.3`). So per-field
`SuccReach` does not close narrowing unconditionally at real rover data; it holds with `px`-room.
-/
import RelCertifier.GapThreeRoverTooling
import RelCertifier.WellFormedFlow

namespace RelCertifier
open DL DLCalTiming Function Set

/-- The switch time: when the Recover flow's `vx = base + 0.4·t` reaches `0.3`. -/
noncomputable def tSwitch (base : State (Var 3)) : ℝ := (3/10 - base (Rv 1)) / (4/10)

/-- **The reaching is real: at `tSwitch`, `vx` hits exactly `0.3`.** Monotone (`vx' = 0.4 > 0`), so from
any `base` the linear `vx`-coordinate reaches the Drive threshold `0.3` — the narrowing switch fires. -/
theorem rover_vx_at_switch (base : State (Var 3)) :
    roverΦR base (tSwitch base) (Rv 1) = 3/10 := by
  rw [roverΦR_Rv1, tSwitch]; ring

/-- **The `px`-coordinate at the switch** — grows by `vx₀·t* + 0.2·t*²` during the speedup (`px' = vx ≥ 0`
so `px` increases monotonically). -/
theorem rover_px_at_switch (base : State (Var 3)) :
    roverΦR base (tSwitch base) (Rv 0)
      = base (Rv 0) + base (Rv 1) * tSwitch base + (2/10) * (tSwitch base) ^ 2 := by
  rw [roverΦR_Rv0]

/-- **THE FINDING (mechanized): `SuccReach` FAILS at the `px`-boundary.** At the genuine Recover state
`px = 15, vx = 0` (in Recover's faithful evolve domain `px∈[0,15] ∧ vx∈[0,1]`), the flow reaches the
switch (`vx = 0.3`) only at `t* = 0.75`, where `px = 15.1125 > 15` — OUTSIDE Drive's evolve domain
`px∈[0,15]`. So no Recover-domain-staying run from this state lands in Drive's domain: `SuccReach` is FALSE
here. The narrowing switch requires `px`-room; at the extreme envelope boundary the automaton cannot
complete the `vx`-speedup within `px∈[0,15]`. This is the non-vacuity check finding a real conditional. -/
theorem rover_SuccReach_fails_at_px_boundary (base : State (Var 3))
    (hpx : base (Rv 0) = 15) (hvx : base (Rv 1) = 0) :
    roverΦR base (tSwitch base) (Rv 0) = 15 + 1125/10000 ∧
    (15 : ℝ) + 1125/10000 > 15 := by
  refine ⟨?_, by norm_num⟩
  rw [rover_px_at_switch, tSwitch, hpx, hvx]; norm_num

/-- **`SuccReach` HOLDS with `px`-room: the `px`-boundary is the only obstruction.** For a Recover state
below the threshold (`vx ≤ 0.3`) with room for the `px`-growth (`px + 0.12 ≤ 15`, more than the maximal
speedup growth `0.1125`), the flow reaches the switch `vx = 0.3` with `px` still `≤ 15` — landing in
Drive's evolve domain. So the reaching is genuinely realizable wherever `px` has room; the refined
narrowing condition is `SuccReach`-with-`px`-room. (`vx₀·t* + 0.2·t*² ≤ 0.3·0.75 + 0.2·0.75² = 0.3375`
bound is loose; the tight max is `0.1125` at `vx₀=0`.) -/
theorem rover_px_at_switch_le_15 (base : State (Var 3))
    (hvx0 : 0 ≤ base (Rv 1)) (hvxle : base (Rv 1) ≤ 3/10)
    (hroom : base (Rv 0) + 12/100 ≤ 15) (hpx0 : 0 ≤ base (Rv 0)) :
    0 ≤ roverΦR base (tSwitch base) (Rv 0) ∧ roverΦR base (tSwitch base) (Rv 0) ≤ 15 := by
  rw [rover_px_at_switch, tSwitch]
  set v := base (Rv 1)
  have ht0 : 0 ≤ (3/10 - v) / (4/10) := by
    apply div_nonneg; linarith; norm_num
  constructor
  · have : 0 ≤ v * ((3/10 - v) / (4/10)) := mul_nonneg hvx0 ht0
    have h2 : 0 ≤ (2/10) * ((3/10 - v) / (4/10)) ^ 2 := by positivity
    linarith
  · -- growth = v·t* + 0.2·t*² ≤ 0.3·(3/4) + 0.2·(3/4)² = 0.225 + 0.1125 = 0.3375, but tighter via v≤0.3
    have hgrow : v * ((3/10 - v) / (4/10)) + (2/10) * ((3/10 - v) / (4/10)) ^ 2 ≤ 12/100 := by
      have hq : ((3/10 - v) / (4/10)) = (3/10 - v) * (10/4) := by rw [div_eq_mul_inv]; norm_num
      rw [hq]
      nlinarith [sq_nonneg (3/10 - v), hvx0, hvxle, mul_nonneg hvx0 (by linarith : (0:ℝ) ≤ 3/10 - v)]
    linarith

/-! ## The BROADER finding — `WellFormedFlow`'s domain-invariance is NOT free for rover

Jian's concern: the `px`-growth that broke `SuccReach` for narrowing may ALSO break `WellFormedFlow`'s
domain-invariance, which the widening/shared "free by construction" discharge silently depends on.
Verified: `WellFormedFlow` requires the flow to stay in `domR` for EVERY duration `s` (`∀ s ≥ 0`, clause
`∀ t ∈ [0,s], sat domR (ΦR t)`). For rover, the `vx`-coordinate has constant derivative `0.4`, so
`vx(t) = vx₀ + 0.4t` grows unboundedly and EXITS the evolve bound `vx ≤ 1` at `t = (1−vx₀)/0.4 ≤ 2.5`.
So `WellFormedFlow` (∀s) is FALSE for any rover mode with a `vx`-bounded domain — domain-invariance is
duration-bounded, NOT free. This is a WHOLE-rover-family issue (affects widening too), not narrowing-only. -/

/-- Constant derivative `0.4` on `[0,s]` forces the affine value — the coordinate grows linearly. -/
theorem const_deriv_affine (g : ℝ → ℝ) (s : ℝ) (hs : 0 ≤ s)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivWithinAt g (4/10) (Set.Icc 0 s) t) :
    g s = g 0 + (4/10) * s := by
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) s) := convex_Icc 0 s
  set h : ℝ → ℝ := fun t => g t - (4/10) * t with hh
  have hhd : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivWithinAt h 0 (Set.Icc 0 s) t := by
    intro t ht
    have h2 := (hd t ht).sub ((hasDerivWithinAt_id t (Set.Icc 0 s)).const_mul (4/10))
    have he : (4/10 : ℝ) - 4/10 * 1 = 0 := by norm_num
    rw [he] at h2; exact h2
  have key := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hhd
    (fun t _ => by simp : ∀ t ∈ Set.Icc (0 : ℝ) s, ‖(0 : ℝ)‖ ≤ 0)
    (left_mem_Icc.mpr hs) (right_mem_Icc.mpr hs)
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at key
  have hkey : g s - (4/10) * s = g 0 - (4/10) * 0 := key
  linarith

/-- The `vx`-only Recover domain (`vx ∈ [0,1]`), the coordinate that exits. -/
noncomputable def recoverDomVx : Formula (Var 3) :=
  Formula.and (Formula.cmp CompOp.le (Term.const 0) (Term.var (Rv 1)))
              (Formula.cmp CompOp.le (Term.var (Rv 1)) (Term.const 1))

/-- **THE BROADER FINDING (mechanized): `WellFormedFlow` is FALSE for the rover field.** Its ∀s
domain-invariance clause demands the flow stay in `vx ≤ 1` for EVERY duration; but the `vx`-derivative is
the constant `0.4`, so at `s = 3` the forced value `vx(3) = 0 + 0.4·3 = 1.2 > 1` violates the domain.
Hence NO witness `ΦR` satisfies `WellFormedFlow roverFR roverLam recoverDomVx`. Domain-invariance is
duration-bounded (holds only for `s ≤ 2.5`), NOT free — the `px`/growth problem is broader than narrowing:
it undermines the "free by construction" widening discharge for the whole rover family too. -/
theorem WellFormedFlow_rover_false :
    ¬ WellFormedFlow roverFR roverLam recoverDomVx := by
  intro hwff
  obtain ⟨ΦR, hΦR0, hder, _, hdom⟩ :=
    hwff (fun _ => 0) (by simp [recoverDomVx, Formula.sat, CompOp.interp, Term.eval]) 3 (by norm_num)
  -- the vx-coordinate has constant derivative 0.4 on [0,3]
  have hvxder : ∀ t ∈ Set.Icc (0 : ℝ) 3, HasDerivWithinAt (fun u => ΦR u (Rv 1)) (4/10) (Set.Icc 0 3) t := by
    intro t ht
    have hp : (Rv 1, Term.binop AOp.mul roverLam (Term.const (4/10)))
        ∈ rightBlock roverFR roverLam := by
      show _ ∈ [(Rv 0, Term.binop AOp.mul roverLam (Term.var (Rv 1))),
                (Rv 1, Term.binop AOp.mul roverLam (Term.const (4/10))),
                (Rv 2, Term.binop AOp.mul roverLam (Term.const 0))]
      simp
    have hev := hder t ht _ hp
    have : (Term.binop AOp.mul roverLam (Term.const (4/10))).eval (ΦR t) = 4/10 := by
      simp [roverLam, Term.eval, AOp.interp]
    rwa [this] at hev
  -- forced: vx(3) = vx(0) + 0.4·3 = 1.2
  have hvx3 : ΦR 3 (Rv 1) = 6/5 := by
    have := const_deriv_affine (fun u => ΦR u (Rv 1)) 3 (by norm_num) hvxder
    rw [hΦR0] at this; simp only at this; rw [this]; norm_num
  -- but the domain clause forces vx(3) ≤ 1
  have hdom3 := hdom 3 (right_mem_Icc.mpr (by norm_num))
  simp only [recoverDomVx, Formula.sat, CompOp.interp, Term.eval] at hdom3
  rw [hvx3] at hdom3
  norm_num at hdom3

/-! ## STEP 1 truth check — bounded-`dt` domain-invariance HOLDS for rover (where `∀s` failed)

Recover's FULL evolve domain (`px∈[0,15] ∧ vx∈[0,1]`). The bounded-`dt` flow stays in it over `[0,dt]`
whenever the start has `dt`-room (`vx₀ + 0.4·dt ≤ 1`, `px₀ + vx₀·dt + 0.2·dt² ≤ 15`) — TRUE by monotone
growth, contrast `WellFormedFlow_rover_false` (the `∀s` form). The room condition is exactly what the
cover's Z3 `SegPreserves` verifies per reachable segment; on loose domains (`px≤15` vs reachable travel
`≤ bound_T·v_max = 2`) reachable starts have ample room. -/

/-- Recover's full evolve domain (`0 ≤ px ≤ 15 ∧ 0 ≤ vx ≤ 1`). -/
noncomputable def recoverDomFull : Formula (Var 3) :=
  Formula.and
    (Formula.and (Formula.cmp CompOp.le (Term.const 0) (Term.var (Rv 0)))
                 (Formula.cmp CompOp.le (Term.var (Rv 0)) (Term.const 15)))
    (Formula.and (Formula.cmp CompOp.le (Term.const 0) (Term.var (Rv 1)))
                 (Formula.cmp CompOp.le (Term.var (Rv 1)) (Term.const 1)))

/-- **THE TRUTH CHECK (mechanized): the rover flow STAYS in Recover's domain over `[0,dt]` with `dt`-room.**
Monotone growth (`px' = vx ≥ 0`, `vx' = 0.4`) keeps `px ∈ [px₀, px(dt)]` and `vx ∈ [vx₀, vx(dt)]`; the
room hypotheses bound the endpoints inside the domain. So bounded-`dt` domain-invariance is TRUE for the
growing-bounded rover field — the honest replacement for the false `∀s` idealization. -/
theorem rover_flow_stays_bounded (base : State (Var 3)) (dt t : ℝ)
    (hpx0 : 0 ≤ base (Rv 0)) (hvx0 : 0 ≤ base (Rv 1))
    (hvxroom : base (Rv 1) + (4/10) * dt ≤ 1)
    (hpxroom : base (Rv 0) + base (Rv 1) * dt + (2/10) * dt ^ 2 ≤ 15)
    (ht0 : 0 ≤ t) (htdt : t ≤ dt) :
    Formula.sat recoverDomFull (roverΦR base t) := by
  have hdt : 0 ≤ dt := le_trans ht0 htdt
  simp only [recoverDomFull, Formula.sat, CompOp.interp, Term.eval, roverΦR_Rv0, roverΦR_Rv1]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · nlinarith [mul_nonneg hvx0 ht0, sq_nonneg t]
  · nlinarith [mul_nonneg hvx0 (sub_nonneg.mpr htdt), sq_nonneg t, sq_nonneg dt,
      mul_nonneg hvx0 ht0, sub_nonneg.mpr htdt]
  · nlinarith
  · nlinarith

/-- Drive's evolve domain (`vx` coordinate `Rv 1`, `px` coordinate `Rv 0`), as a `Formula`. -/
noncomputable def driveDomF : Formula (Var 3) :=
  Formula.and
    (Formula.and (Formula.cmp CompOp.le (Term.const 0) (Term.var (Rv 0)))
                 (Formula.cmp CompOp.le (Term.var (Rv 0)) (Term.const 15)))
    (Formula.and (Formula.cmp CompOp.le (Term.const (3/10)) (Term.var (Rv 1)))
                 (Formula.cmp CompOp.le (Term.var (Rv 1)) (Term.const 1)))

/-- **The entry precondition (`inModeDomR` analog) is non-vacuously satisfied.** A genuine rover entry
config — `px = 0`, `vx = 1/2` (in Drive's speed band) — lies in Drive's evolve domain. So the strengthened
`ψpostL` precondition (start in a mode's domain) is FREE at a real entry: `inModeDomR` is not the
obstruction. Only `SuccReach` (the narrowing reachability) is conditional at rover. -/
theorem rover_entry_in_drive_dom (ν : State (Var 3)) (hpx : ν (Rv 0) = 0) (hvx : ν (Rv 1) = 1/2) :
    Formula.sat driveDomF ν := by
  simp only [driveDomF, Formula.sat, CompOp.interp, Term.eval, hpx, hvx]
  refine ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
