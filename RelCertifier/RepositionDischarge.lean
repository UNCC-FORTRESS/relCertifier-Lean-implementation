/-
GAP 1 — the `Hmulti` discharge: derive the genuine-multi-flow emit from `cert.segPres`, making the
reposition-inclusive multi Theorem 3 **checker-entailed** (`decideCovered`/`cert ⟹ Theorem 3`)
rather than emit-conditional. Mirror of `hpair_from_cover` (single-flow), multi-flow version.

The new plumbing vs single-flow: the bounded per-segment coupling (`faModal_ODE_G'_bounded`) runs the
left under a fresh clock (`clk tg leftBlock`), but `cert.segPres` is an **unclocked** joint `BoxLe`.
This file lifts the certificate across the clock — `sem_ode_perm` (semantics is permutation-invariant),
`box_ode_perm`, and `boxLe_clock_lift` (reuse `clockReduce`) — so the segment certs come from `cert`,
not re-assumed.
-/
import RelCertifier.BridgeReposition
import RelCertifier.ClockReduce

namespace RelCertifier
open DL DLCalTiming Function Set

variable {n : ℕ}

/-! ## Clock plumbing — lift an unclocked certificate box across a fresh clock -/

/-- **ODE semantics is permutation-invariant.** All the run conditions (per-equation derivatives,
non-bound masking, throughout-domain) are membership- and ∀-based, so reordering the equation list
leaves the reachability relation unchanged. -/
theorem sem_ode_perm {sys1 sys2 : ODESystem (Var n)} (hperm : List.Perm sys1 sys2)
    (dom : Formula (Var n)) {ω ν : State (Var n)}
    (h : Program.sem (Program.ode sys1 dom) ω ν) :
    Program.sem (Program.ode sys2 dom) ω ν := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := h
  refine ⟨r, Φ, hr, hΦ0, hΦr, ?_, ?_, hdom⟩
  · intro t ht p hp; exact hder t ht p (hperm.mem_iff.mpr hp)
  · intro t ht x hx
    exact hmask t ht x (fun hc => hx ((hperm.map Prod.fst).mem_iff.mp hc))

/-- Box transfers across a permutation of the ODE equation list. -/
theorem box_ode_perm {sys1 sys2 : ODESystem (Var n)} (hperm : List.Perm sys1 sys2)
    (dom : Formula (Var n)) (φ : Formula (Var n)) {ω : State (Var n)}
    (h : Formula.sat (Formula.box (Program.ode sys1 dom) φ) ω) :
    Formula.sat (Formula.box (Program.ode sys2 dom) φ) ω := by
  rw [sat_box] at h ⊢
  intro ν hν
  exact h ν (sem_ode_perm hperm.symm dom hν)

/-- **Certificate clock-lift.** An unclocked `invLe g` box lifts to the clock-augmented system
(`clk tg sys = sys ++ [(tg,1)]`), for `tg` fresh. A clocked run drops (`clockReduce`) to an unclocked
run reaching the same state up to `tg`; `invLe g` is `tg`-invisible (`tg ∉ g.fv`), so it transfers. -/
theorem boxLe_clock_lift (sys : ODESystem (Var n)) (dom : Formula (Var n)) (g : Term (Var n))
    (tg : Var n) (htgb : tg ∉ sys.bound) (htgr : tg ∉ sys.readVars) (htgd : tg ∉ dom.fv)
    (htgg : tg ∉ g.fv) {ω : State (Var n)}
    (h : Formula.sat (Formula.box (Program.ode sys dom) (invLe g)) ω) :
    Formula.sat (Formula.box (Program.ode (clk tg sys) dom) (invLe g)) ω := by
  rw [sat_box] at h ⊢
  intro ν hν
  have hdrop := clockReduce sys dom tg htgb htgr htgd hν
  have hinv := h _ hdrop
  rw [sat_invLe] at hinv ⊢
  rwa [Term.coincidence g (fun y hy =>
    Function.update_of_ne (fun hc => htgg (by rw [← hc]; exact hy)) _ _)] at hinv

/-- The permutation moving the fresh clock from mid-position (`clk tg A ++ B`) to the tail
(`clk tg (A ++ B)`), so `boxLe_clock_lift` (clock-at-tail) applies to the joint system
`faModal_ODE_G'_bounded` forms. -/
theorem clk_mid_perm (A B : ODESystem (Var n)) (tg : Var n) :
    List.Perm ((clk tg A) ++ B) (clk tg (A ++ B)) := by
  simp only [clk]
  rw [List.append_assoc, List.append_assoc]
  exact (List.perm_append_comm.append_left A)

end RelCertifier
