/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The clock reduction — the clock is a transient proof device, eliminable

The B>1 clock rework introduces a clock `tg` to *state* the duration-bounded segment and enable
`plantT_split`, then **eliminates** it: a clocked run projects to the ordinary (unclocked) run.
So `jointSys`/the invariant/the encoding stay over `Var n` — no permanent `ExtVar` threading.

`clockReduce`: a run of `ode (clk tg sys) ϕ` (physical `sys` + clock `tg'=1`) projects, by resetting
`tg`, to a run of `ode sys ϕ` — provided `tg` is fresh (`∉ sys.bound`, `∉ sys.readVars`, `∉ ϕ.fv`).
The physical variables evolve identically (the clock is inert for them); the domain `ϕ` is
clock-free, so it survives the projection (coincidence). Generic over `V`.
-/
import DLCalTiming.ODEClock
import RelCertifier.Checker.Cover

namespace RelCertifier

open DL DLCalTiming Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Clock reduction.** A clocked ODE run projects (resetting the clock `tg`) to an unclocked run
of the physical system, when `tg` is fresh. The clock's only trace is the duration `ν tg − ω tg`. -/
theorem clockReduce (sys : ODESystem V) (ϕ : Formula V) (tg : V)
    (htgb : tg ∉ sys.bound) (htgr : tg ∉ sys.readVars) (htgϕ : tg ∉ ϕ.fv)
    {ω ν : State V}
    (h : Program.sem (Program.ode (clk tg sys) ϕ) ω ν) :
    Program.sem (Program.ode sys ϕ) ω (Function.update ν tg (ω tg)) := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := h
  -- projected curve: physical vars from Φ, clock held at its initial value
  refine ⟨r, fun t => Function.update (Φ t) tg (ω tg), hr, ?_, ?_, ?_, ?_, ?_⟩
  · -- start: update (Φ 0) tg (ω tg) = ω
    funext x
    by_cases hx : x = tg
    · subst hx; simp only [Function.update_self, ← hΦ0]
    · simp only [Function.update_of_ne hx]; rw [hΦ0]
  · -- end: update (Φ r) tg (ω tg) = update ν tg (ω tg)
    funext x
    show Function.update (Φ r) tg (ω tg) x = Function.update ν tg (ω tg) x
    by_cases hx : x = tg
    · subst hx; simp only [Function.update_self]
    · rw [Function.update_of_ne hx, Function.update_of_ne hx, hΦr]
  · -- derivatives for p ∈ sys (a subset of clk tg sys); clock reset doesn't affect p.1 or p.2.eval
    intro t ht p hp
    have hp1 : p.1 ≠ tg := fun hc => htgb (by rw [← hc]; exact List.mem_map.mpr ⟨p, hp, rfl⟩)
    have hpc : p ∈ clk tg sys := by simp only [clk]; exact List.mem_append_left _ hp
    have hd := hder t ht p hpc
    have hfun : (fun u => Function.update (Φ u) tg (ω tg) p.1) = fun u => Φ u p.1 := by
      funext u; exact Function.update_of_ne hp1 _ _
    rw [hfun]
    have hev : p.2.eval (Function.update (Φ t) tg (ω tg)) = p.2.eval (Φ t) :=
      Term.coincidence p.2 (fun y hy => Function.update_of_ne
        (fun hc => htgr (by rw [← hc]; exact ⟨p, hp, hy⟩)) _ _)
    rw [hev]; exact hd
  · -- mask: x ∉ sys.bound → projected t x = ω x
    intro t ht x hx
    show Function.update (Φ t) tg (ω tg) x = ω x
    by_cases hxtg : x = tg
    · subst hxtg; simp only [Function.update_self]
    · rw [Function.update_of_ne hxtg]
      refine hmask t ht x ?_
      simp only [clk, ODESystem.bound, List.map_append, List.map_cons, List.map_nil,
        List.mem_append, List.mem_singleton, not_or]
      exact ⟨hx, hxtg⟩
  · -- domain ϕ (clock-free) survives the projection
    intro t ht
    exact (Formula.coincidence ϕ (fun y hy => (Function.update_of_ne
      (fun hc => htgϕ (by rw [← hc]; exact hy)) _ _))).mpr (hdom t ht)

end RelCertifier
