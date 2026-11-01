/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Assumption 1 for the stop-line ladders (`CRUISE → BRAKE → STOP`), proved once

The four rungs of the stop-line rover ladder share one right model shape: three modes on the
odometer `p` and the speed `v`, `CRUISE` (`p < 100`, `v ≥ 0.35`: the speed is held, `v' = 0`),
`BRAKE` (`p ≥ 100`, `v ≥ 0.35`: the brake decelerates, `v' ≤ 0`) and `STOP` (`p ≥ 100`,
`v ≤ 0.35`: every coordinate frozen), with `p' = v ≥ 0` in the moving modes, the other
coordinates whatever the level declares, the declared successors `CRUISE → {CRUISE, BRAKE}`,
`BRAKE → {BRAKE, STOP}`, `STOP → {STOP}`, and `ε_r = 1/10`.
`wellFormedR_stopline`: from these mode facts and the existence of runs (each instance's
explicit runs), `WellFormedR`. Clause (ii) per mode: a `CRUISE` run keeps its speed and does
not move the odometer backwards, so it ends in `CRUISE` (`p < 100`) or `BRAKE` (`p ≥ 100`); a
`BRAKE` run keeps `p ≥ 100` and ends with `v ≥ 0.35` (`BRAKE`) or `v ≤ 0.35` (`STOP`); a `STOP`
run is constant. Z3-free. New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.WellFormedR

namespace RelCertifier

open DL DLCalTiming Set

variable {n : ℕ}

/-- The mode facts of a stop-line ladder (indices: `Rv ip` the odometer, `Rv iv` the speed). -/
structure StopWF (G : SearchGraph (Var n)) (guard : ℕ → Formula (Var n))
    (dom : Formula (Var n)) where
  m : ℕ → RMode (Var n)
  fR : ℕ → Fin n → Term (Var n)
  ip : Fin n
  iv : Fin n
  modeAt : ∀ q < 3, G.modeAt q = some (m q)
  len : G.modes.length = 3
  sys_eq : ∀ q < 3, (m q).sys = rightBlock (fR q) (Term.const 1)
  dom_eq : ∀ q < 3, (m q).dom = dom
  /-- the odometer rate is the speed while moving, 0 at standstill -/
  fp0 : ∀ s, Term.eval (fR 0 ip) s = s (Rv iv)
  fp1 : ∀ s, Term.eval (fR 1 ip) s = s (Rv iv)
  fp2 : ∀ s, Term.eval (fR 2 ip) s = 0
  /-- the speed is held while cruising and frozen at standstill -/
  fv0 : ∀ s, Term.eval (fR 0 iv) s = 0
  fv2 : ∀ s, Term.eval (fR 2 iv) s = 0
  /-- the speed is nonnegative on the domain -/
  vdom : ∀ s, Formula.sat dom s → 0 ≤ s (Rv iv)
  g0 : ∀ x, Formula.sat (guard 0) x ↔ x (Rv ip) < 100 ∧ 7/20 ≤ x (Rv iv)
  g1 : ∀ x, Formula.sat (guard 1) x ↔ 100 ≤ x (Rv ip) ∧ 7/20 ≤ x (Rv iv)
  g2 : ∀ x, Formula.sat (guard 2) x ↔ 100 ≤ x (Rv ip) ∧ x (Rv iv) ≤ 7/20
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
  /-- existence of a full control interval of flow from every guard state of the domain -/
  exists_run : ∀ q < 3, ∀ x, Formula.sat (guard q) x → Formula.sat dom x →
    ∃ Φ, ODESol (m q).sys (m q).dom x (1/10) Φ

/-- **Assumption 1 for a stop-line ladder**, from its mode facts (Z3-free). -/
theorem wellFormedR_stopline {G : SearchGraph (Var n)} {guard : ℕ → Formula (Var n)}
    {dom : Formula (Var n)} (W : StopWF G guard dom) : WellFormedR G guard (1/10) := by
  intro q hq m hm x hg hd _
  rw [W.len] at hq
  have hmq : m = W.m q := by
    have := W.modeAt q hq; rw [hm] at this; exact Option.some.inj this
  subst hmq
  refine ⟨W.exists_run q hq x hg (by rw [← W.dom_eq q hq]; exact hd), ?_⟩
  intro t Φ _ H
  rw [W.sys_eq q hq, W.dom_eq q hq] at H
  have hmemp := rightBlock_mem' (W.fR q) (Term.const 1) W.ip
  have hmemv := rightBlock_mem' (W.fR q) (Term.const 1) W.iv
  interval_cases q
  · -- CRUISE: the speed is held, the odometer does not decrease
    obtain ⟨hp, hv⟩ := (W.g0 x).mp hg
    have hpm : x (Rv W.ip) ≤ Φ t (Rv W.ip) :=
      H.mono hmemp (fun s hs => by rw [eval_unit_mul, W.fp0]; exact W.vdom s hs)
    have hvc : Φ t (Rv W.iv) = x (Rv W.iv) :=
      H.const hmemv (fun s _ => by rw [eval_unit_mul, W.fv0])
    by_cases h100 : Φ t (Rv W.ip) < 100
    · refine ⟨W.e00, W.e00_mem, ?_⟩
      rw [W.e00_tgt, W.g0]; exact ⟨h100, by rw [hvc]; exact hv⟩
    · refine ⟨W.e01, W.e01_mem, ?_⟩
      rw [W.e01_tgt, W.g1]; exact ⟨by linarith, by rw [hvc]; exact hv⟩
  · -- BRAKE: the odometer stays past the brake point; the speed ends above or below the threshold
    obtain ⟨hp, hv⟩ := (W.g1 x).mp hg
    have hpm : x (Rv W.ip) ≤ Φ t (Rv W.ip) :=
      H.mono hmemp (fun s hs => by rw [eval_unit_mul, W.fp1]; exact W.vdom s hs)
    by_cases hth : 7/20 ≤ Φ t (Rv W.iv)
    · refine ⟨W.e11, W.e11_mem, ?_⟩
      rw [W.e11_tgt, W.g1]; exact ⟨by linarith, hth⟩
    · refine ⟨W.e12, W.e12_mem, ?_⟩
      rw [W.e12_tgt, W.g2]; exact ⟨by linarith, by linarith⟩
  · -- STOP: constant
    obtain ⟨hp, hv⟩ := (W.g2 x).mp hg
    have hpc : Φ t (Rv W.ip) = x (Rv W.ip) :=
      H.const hmemp (fun s _ => by rw [eval_unit_mul, W.fp2])
    have hvc : Φ t (Rv W.iv) = x (Rv W.iv) :=
      H.const hmemv (fun s _ => by rw [eval_unit_mul, W.fv2])
    refine ⟨W.e22, W.e22_mem, ?_⟩
    rw [W.e22_tgt, W.g2, hpc, hvc]; exact ⟨hp, hv⟩

end RelCertifier
