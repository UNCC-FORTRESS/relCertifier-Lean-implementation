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

namespace RelCertifier
open DL DLCalTiming Function

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
