/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Assumption 1 for the terrain ladders (`STEEP → MODER → FLAT`), proved once

Eighteen suite_v2 benchmarks share one right model shape: three bands of the odometer `s`
(`STEEP` `0 ≤ s < 0.6`, `MODER` `0.6 ≤ s < 1.4`, `FLAT` `s ≥ 1.4`, optionally with the speed
caps `v ≤ 0.3 / 0.5 / 0.65`), the speed a contraction `v' = 3 (c_q − v)` toward the band's
set point `c_q = ladC q` (0.3, 0.5, 0.65), the odometer rate `s'` between 0 and 0.8 on the
evolve domain (`s' = v`, or `v` weighted by an attitude factor in `[0, 1]`), the other
coordinates whatever the file declares, the declared successors `STEEP → {MODER, STEEP}`,
`MODER → {FLAT, MODER}`, `FLAT → {FLAT}`, and `ε_r = 1`.

`wellFormedR_ladder`: from the band facts and the existence of runs (each instance's
`LadderRun.sol`), `WellFormedR`. Clause (ii) per band: the speed stays between its start
and the set point (so a speed cap of the band is kept and implies the next band's cap), the
odometer does not decrease, and over one interval it grows by at most `0.8`, so a `STEEP`
run ends below `0.6 + 0.8 = 1.4` (inside `STEEP` or `MODER`), a `MODER` run ends in `MODER`
or `FLAT`, and `FLAT` is forward invariant. Style (b) for `STEEP`, `MODER`; (a) for `FLAT`.
Z3-free.

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Encoding.LadderClimb

namespace RelCertifier
open DL DLCalTiming Set

variable {n : ℕ}

/-- The band facts of a terrain ladder (indices: `Rv 0` the speed, `Rv 1` the odometer). -/
structure LadderWF (G : SearchGraph (Var n)) (guard : ℕ → Formula (Var n))
    (dom : Formula (Var n)) where
  m : ℕ → RMode (Var n)
  fR : ℕ → Fin n → Term (Var n)
  /-- whether the guards carry the speed caps `v ≤ c_q` -/
  vcap : Prop
  i0 : Fin n
  i1 : Fin n
  modeAt : ∀ q < 3, G.modeAt q = some (m q)
  len : G.modes.length = 3
  sys_eq : ∀ q < 3, (m q).sys = rightBlock (fR q) (Term.const 1)
  dom_eq : ∀ q < 3, (m q).dom = dom
  fv : ∀ q < 3, ∀ s, Term.eval (fR q i0) s = 3 * (ladC q - s (Rv i0))
  fs : ∀ q < 3, ∀ s, Formula.sat dom s → 0 ≤ Term.eval (fR q i1) s ∧ Term.eval (fR q i1) s ≤ 4/5
  g0 : ∀ x, Formula.sat (guard 0) x ↔
    (0 ≤ x (Rv i1) ∧ x (Rv i1) < 3/5) ∧ (vcap → x (Rv i0) ≤ 3/10)
  g1 : ∀ x, Formula.sat (guard 1) x ↔
    (3/5 ≤ x (Rv i1) ∧ x (Rv i1) < 7/5) ∧ (vcap → x (Rv i0) ≤ 1/2)
  g2 : ∀ x, Formula.sat (guard 2) x ↔ 7/5 ≤ x (Rv i1) ∧ (vcap → x (Rv i0) ≤ 13/20)
  e00 : REdge (Var n)
  e01 : REdge (Var n)
  e11 : REdge (Var n)
  e12 : REdge (Var n)
  e22 : REdge (Var n)
  e00_mem : e00 ∈ G.edgesFrom 0
  e01_mem : e01 ∈ G.edgesFrom 0
  e11_mem : e11 ∈ G.edgesFrom 1
  e12_mem : e12 ∈ G.edgesFrom 1
  e22_mem : e22 ∈ G.edgesFrom 2
  e00_tgt : e00.tgt = 0
  e01_tgt : e01.tgt = 1
  e11_tgt : e11.tgt = 1
  e12_tgt : e12.tgt = 2
  e22_tgt : e22.tgt = 2
  exists_run : ∀ q < 3, ∀ x, Formula.sat dom x → ∃ Φ, ODESol (m q).sys (m q).dom x 1 Φ

/-- **Assumption 1 for a terrain ladder**, from its band facts (Z3-free). -/
theorem wellFormedR_ladder {G : SearchGraph (Var n)} {guard : ℕ → Formula (Var n)}
    {dom : Formula (Var n)} (W : LadderWF G guard dom) : WellFormedR G guard 1 := by
  intro q hq m hm x hg hd _
  rw [W.len] at hq
  have hmq : m = W.m q := by
    have := W.modeAt q hq; rw [hm] at this; exact Option.some.inj this
  subst hmq
  refine ⟨W.exists_run q hq x (by rw [← W.dom_eq q hq]; exact hd), ?_⟩
  intro t Φ ht H
  rw [W.sys_eq q hq, W.dom_eq q hq] at H
  have hmemv := rightBlock_mem' (W.fR q) (Term.const 1) W.i0
  have hmems := rightBlock_mem' (W.fR q) (Term.const 1) W.i1
  have hv := H.linear_between hmemv 3 (ladC q) (by norm_num)
    (fun s _ => by rw [eval_unit_mul, W.fv q hq])
  have hsup := H.rate_le hmems (4/5) (fun s hs => by rw [eval_unit_mul]; exact (W.fs q hq s hs).2)
  have hslo := H.mono hmems (fun s hs => by rw [eval_unit_mul]; exact (W.fs q hq s hs).1)
  have hr := H.hr
  have hcap : ∀ c, ladC q ≤ c → x (Rv W.i0) ≤ c → Φ t (Rv W.i0) ≤ c :=
    fun c h1 h2 => le_trans hv.2 (max_le h2 h1)
  interval_cases q
  · -- STEEP: ends below 0.6 + 0.8 = 1.4, inside STEEP or MODER
    obtain ⟨⟨hs0, hs1⟩, hvc⟩ := (W.g0 x).mp hg
    have hc : ladC 0 = 3/10 := by simp [ladC]
    by_cases h06 : Φ t (Rv W.i1) < 3/5
    · refine ⟨W.e00, W.e00_mem, ?_⟩
      rw [W.e00_tgt, W.g0]
      exact ⟨⟨by linarith, h06⟩, fun h => hcap _ hc.le (hvc h)⟩
    · refine ⟨W.e01, W.e01_mem, ?_⟩
      rw [W.e01_tgt, W.g1]
      exact ⟨⟨by linarith, by nlinarith⟩,
        fun h => hcap _ (by rw [hc]; norm_num) (by linarith [hvc h])⟩
  · -- MODER: inside MODER or FLAT
    obtain ⟨⟨hs0, hs1⟩, hvc⟩ := (W.g1 x).mp hg
    have hc : ladC 1 = 1/2 := by simp [ladC]
    by_cases h14 : Φ t (Rv W.i1) < 7/5
    · refine ⟨W.e11, W.e11_mem, ?_⟩
      rw [W.e11_tgt, W.g1]
      exact ⟨⟨by linarith, h14⟩, fun h => hcap _ hc.le (hvc h)⟩
    · refine ⟨W.e12, W.e12_mem, ?_⟩
      rw [W.e12_tgt, W.g2]
      exact ⟨by linarith, fun h => hcap _ (by rw [hc]; norm_num) (by linarith [hvc h])⟩
  · -- FLAT: forward invariant
    obtain ⟨hs0, hvc⟩ := (W.g2 x).mp hg
    have hc : ladC 2 = 13/20 := by simp [ladC]
    refine ⟨W.e22, W.e22_mem, ?_⟩
    rw [W.e22_tgt, W.g2]
    exact ⟨by linarith, fun h => hcap _ hc.le (hvc h)⟩

end RelCertifier
