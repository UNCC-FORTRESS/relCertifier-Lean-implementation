/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Generic kernel pins — runtime-built queries ARE the hypothesized queries

The cut-instance hypotheses quote `getD`-lowered components (`hostDyn`, `hostEvolve`,
`hostGuard`, `hostComps`, `hostAtomF/G`). The verdict runner rebuilds the same queries
at runtime from the emitted IR (`benchIRTable`) and cut certificates
(`EvolStrengthenings`) — the pins below prove, ONCE and generically, that whenever the
lowerings succeed (`some`-facts, observable at runtime and kernel-established per
instance), the printed IR query denotes exactly the hypothesized host query. No
per-benchmark literals; every benchmark rides the same five lemmas.
-/
import RelCertifier.Verdicts.Combinators
import RelCertifier.Proofs.Soundness.CutCoverDischarge

namespace RelCertifier

open DL Parse RelCertifier.Oracle

variable {n : ℕ}

/-- Componentwise `some`-facts collapse the `getD` wrappers (field vector). -/
theorem hostDyn_pin {vars : List String} {side : Side} {m : PMode}
    {fI : Fin n → ITerm n} (h : Run.dynOf vars n side m = some fI) :
    hostDyn vars n side m = fun i => (fI i).toHost := by
  funext i
  unfold hostDyn
  rw [h]
  rfl

theorem hostEvolve_pin {vars : List String} {side : Side} {m : PMode}
    {evI : IForm n} (h : Run.lowerF vars n side m.evolve = some evI) :
    hostEvolve vars n side m = evI.toHost := by
  unfold hostEvolve
  rw [h]
  rfl

theorem hostGuard_pin {vars : List String} {side : Side} {m : PMode}
    {gI : IForm n} (h : Run.lowerF vars n side m.guard = some gI) :
    hostGuard vars n side m = gI.toHost := by
  unfold hostGuard
  rw [h]
  rfl

theorem hostComps_pin {vars : List String} {f : PForm}
    {gsI : List (ITerm n)} (h : Oracle.invComponents vars n f = some gsI) :
    hostComps vars n f = gsI.map ITerm.toHost := by
  unfold hostComps
  rw [h]
  rfl

theorem hostAtomG_pin {vars : List String} {side : Side} {a : PForm}
    {gI : ITerm n} (h : cutAtomG vars n side a = some gI) :
    hostAtomG vars n side a = gI.toHost := by
  unfold hostAtomG
  rw [h]
  rfl

theorem hostAtomF_pin {vars : List String} {side : Side} {a : PForm}
    {aI : IForm n} (h : Run.lowerF vars n side a = some aI) :
    hostAtomF vars n side a = aI.toHost := by
  unfold hostAtomF
  rw [h]
  rfl

/-! ## Query-shape pins

Each mirrors one hypothesis shape of the cut instances (and the O2 probes), assembled
from the component pins, the fold mirrors, and the route-query mirrors. -/

/-- The O2 probe (any of the three routes, selected by the caller's builder). -/
theorem o2_probe_pin {vars : List String} {side : Side} {m : PMode} {a : PForm}
    {fI : Fin n → ITerm n} {evI : IForm n} {gI : ITerm n}
    (hdyn : Run.dynOf vars n side m = some fI)
    (hev : Run.lowerF vars n side m.evolve = some evI)
    (hg : cutAtomG vars n side a = some gI) :
    ((iflowQuery gI (fun _ => .rat 0) fI (.rat 1) evI).toHost
        = flowQuery ⟨hostAtomG vars n side a, (fun _ => Term.const 0),
            hostDyn vars n side m, Term.const 1, hostEvolve vars n side m⟩)
    ∧ ((iflowQueryStrict gI (fun _ => .rat 0) fI (.rat 1) evI).toHost
        = flowQueryStrict ⟨hostAtomG vars n side a, (fun _ => Term.const 0),
            hostDyn vars n side m, Term.const 1, hostEvolve vars n side m⟩)
    ∧ ((iflowQuerySuperlevel gI (fun _ => .rat 0) fI (.rat 1) evI).toHost
        = flowQuerySuperlevel ⟨hostAtomG vars n side a, (fun _ => Term.const 0),
            hostDyn vars n side m, Term.const 1, hostEvolve vars n side m⟩) := by
  rw [hostAtomG_pin hg, hostDyn_pin hdyn, hostEvolve_pin hev]
  refine ⟨?_, ?_, ?_⟩
  · rw [iflowQuery_toHost, zeroField_toHost, oneConst_toHost]
  · rw [iflowQueryStrict_toHost, zeroField_toHost, oneConst_toHost]
  · rw [iflowQuerySuperlevel_toHost, zeroField_toHost, oneConst_toHost]

/-- The mirrored L-side O2 probe (left atoms: own field left, right frozen). -/
theorem o2_probeL_pin {vars : List String} {m : PMode} {a : PForm}
    {fI : Fin n → ITerm n} {evI : IForm n} {gI : ITerm n}
    (hdyn : Run.dynOf vars n Side.L m = some fI)
    (hev : Run.lowerF vars n Side.L m.evolve = some evI)
    (hg : cutAtomG vars n Side.L a = some gI) :
    ((iflowQuery gI fI (fun _ => .rat 0) (.rat 1) evI).toHost
        = flowQuery ⟨hostAtomG vars n Side.L a, hostDyn vars n Side.L m,
            (fun _ => Term.const 0), Term.const 1, hostEvolve vars n Side.L m⟩)
    ∧ ((iflowQuerySuperlevel gI fI (fun _ => .rat 0) (.rat 1) evI).toHost
        = flowQuerySuperlevel ⟨hostAtomG vars n Side.L a, hostDyn vars n Side.L m,
            (fun _ => Term.const 0), Term.const 1, hostEvolve vars n Side.L m⟩) := by
  rw [hostAtomG_pin hg, hostDyn_pin hdyn, hostEvolve_pin hev]
  constructor
  · rw [iflowQuery_toHost, zeroField_toHost, oneConst_toHost]
  · rw [iflowQuerySuperlevel_toHost, zeroField_toHost, oneConst_toHost]

/-- The instance-side cut fold, pinned: the IR fold over the atoms' lowered forms
denotes `cutF` of the instance's `CutAtomP` pairs (whose `.1` are the `hostAtomF`s). -/
theorem cutFold_pin {vars : List String} {side : Side} (atoms : List PForm)
    (aIs : List (IForm n))
    (hall : atoms.mapM (Run.lowerF vars n side) = some aIs) :
    (icutF aIs).toHost
      = cutF (atoms.map (fun a =>
          ((hostAtomF vars n side a : Formula (Var n)),
           (hostAtomG vars n side a : Term (Var n))))) := by
  refine icutF_toHost' aIs _ ?_
  induction atoms generalizing aIs with
  | nil =>
      cases aIs with
      | nil => rfl
      | cons b t => simp [List.mapM, List.mapM.loop] at hall
  | cons a atoms ih =>
      rw [List.mapM_cons] at hall
      rcases ha : (Run.lowerF vars n side a : Option (IForm n)) with _ | aI <;> rw [ha] at hall
      · simp at hall
      rcases ht : atoms.mapM (Run.lowerF vars n side) with _ | tIs <;> rw [ht] at hall
      · simp at hall
      simp only [Option.bind_eq_bind, Option.bind] at hall
      injection hall with h
      subst h
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨(hostAtomF_pin ha).symm ▸ rfl, ih tIs ht⟩

end RelCertifier
