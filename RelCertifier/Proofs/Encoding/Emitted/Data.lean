/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The generic bridge, part 1: a benchmark's data, read off its records

Everything the general Theorem 3 (`theorem3_of_coverX`, and its mode-keyed assembly) needs
of a benchmark, as functions of the records the tool emits: the parsed problem `p` (the IR),
the extended cut certificate `cX`, the cover record `cov`. No per-benchmark definition is
written by hand; a generated instance supplies only the literals, the kernel-decided
structural facts (`structOK`) and the verdict hypotheses.

* the lowered fields, evolve domains, guards and invariant rows of both sides (the same
  pipelines the verdict runners rebuild their queries from: `hostDyn`, `hostEvolve`,
  `hostGuard`, `hostComps`);
* the right automaton `grOf`: one mode per declared right mode (its field at stretch 1, the
  uniform right evolve domain, unit weight), one edge per name in each mode's `next` list,
  resolved by `findIdx` exactly as the tool's `succOf`, carrying the entered mode's lowered
  guard, pruned iff the cover record prunes it;
* the left automaton `leftAutOf`: one guard-gated window per left mode, the declared `next`
  lists resolved by `Handoff.leftModeIndex`;
* the kept cut atoms of each mode and the anchor `AG` of a window and right mode: the
  window's row, the kept atoms of both modes, the barrier terms of the pruned exits of the
  right mode, and the evolve envelope;
* the time model of a window: the window's stretch `lamQ`, the per-pairing stretches, the
  common span `εR / lamQ`, the budget.

The dimension `n` is a parameter: the state variables plus the auxiliary coordinates (the
window form needs two, the keyed form three); the generated instances take the pack table's
dimension (`bridgeDimV2`).
-/
import RelCertifier.Proofs.Encoding.Theorem3General
import RelCertifier.Proofs.Encoding.ModeHandoff
import RelCertifier.Proofs.Encoding.NonConnBridge
import RelCertifier.Checker.CoverEmit
import RelCertifier.Trusted.Handoff
import RelCertifier.Trusted.ProgressEmit

set_option autoImplicit false

namespace RelCertifier
namespace Emitted

open DL DLRel Parse Run Set Oracle

/-- The default mode every runner uses for an out-of-range index. -/
def dm : PMode := ⟨"", [], .tt, .tt, []⟩

section Data

variable (p : PProblem) (n : ℕ)

def vars : List String := p.L.stateVars
def nL : ℕ := p.L.modes.length
def nR : ℕ := p.R.modes.length
def mLof (l : ℕ) : PMode := p.L.modes.getD l dm
def mRof (q : ℕ) : PMode := p.R.modes.getD q dm

/-- The invariant row of left mode `l`: its own when rows are per mode, else row 0
(the runners' `VerdictsV2.invRowOf`). -/
def rowIdx (l : ℕ) : ℕ := if p.invariants.length > l then l else 0
def rowOf (l : ℕ) : PForm := (p.invariants.getD (rowIdx p l) ("", PForm.tt)).2

noncomputable def fL (l : ℕ) : Fin n → Term (Var n) := hostDyn (vars p) n Side.L (mLof p l)
noncomputable def fR (q : ℕ) : Fin n → Term (Var n) := hostDyn (vars p) n Side.R (mRof p q)
noncomputable def domL : Formula (Var n) := hostEvolve (vars p) n Side.L (mLof p 0)
noncomputable def domR : Formula (Var n) := hostEvolve (vars p) n Side.R (mRof p 0)
noncomputable def env : Formula (Var n) := Formula.and (domL p n) (domR p n)
noncomputable def guardL (l : ℕ) : Formula (Var n) := hostGuard (vars p) n Side.L (mLof p l)
noncomputable def guardR (q : ℕ) : Formula (Var n) := hostGuard (vars p) n Side.R (mRof p q)

/-- The lowered components of window `l`'s row, and the row as `g :: gs`. -/
noncomputable def comps (l : ℕ) : List (Term (Var n)) := hostComps (vars p) n (rowOf p l)
noncomputable def g (l : ℕ) : Term (Var n) := (comps p n l).headD (Term.const 0)
noncomputable def gs (l : ℕ) : List (Term (Var n)) := (comps p n l).tail
noncomputable def FRow (l : ℕ) : Formula (Var n) := FM (g p n l) (gs p n l)
noncomputable def ϕRow (l : ℕ) : RFormula (Var n) := canonInvM (g p n l) (gs p n l)

theorem encode_ϕRow (l : ℕ) : encode (Equiv.refl (Var n)) (ϕRow p n l) = FRow p n l :=
  encode_canonInvM _ _

/-- The number of components of a row, computably (the lowering's success is part of
`structOK`). -/
def compsLen (l : ℕ) : ℕ :=
  ((Oracle.invComponents (vars p) n (rowOf p l)).map List.length).getD 0

theorem comps_length (l : ℕ) : (comps p n l).length = compsLen p n l := by
  unfold comps compsLen hostComps
  rcases Oracle.invComponents (vars p) n (rowOf p l) with _ | cs <;> simp

theorem cons_g_gs (l : ℕ) (h : 0 < compsLen p n l) : g p n l :: gs p n l = comps p n l := by
  unfold g gs
  rw [← comps_length] at h
  rcases hc : comps p n l with _ | ⟨c, cs⟩
  · rw [hc] at h; simp at h
  · rfl

/-! ## The right automaton -/

/-- Index of a right mode by name (the tool's `findIdx`; the mode count if absent). -/
def tgtIdx (nm : String) : ℕ := p.R.modes.findIdx (·.name == nm)

noncomputable def modeOf (q : ℕ) : RMode (Var n) :=
  { sys := rightBlock (fR p n q) (Term.const 1), dom := domR p n, weight := 1 }

/-- The declared edge `q → nm`, carrying the entered mode's lowered guard. -/
noncomputable def edgeOf (pruned : String → String → Bool) (q : ℕ) (nm : String) :
    REdge (Var n) :=
  { src := q, tgt := tgtIdx p nm, guard := guardR p n (tgtIdx p nm),
    pruned := pruned (mRof p q).name nm }

noncomputable def grOf (pruned : String → String → Bool) : SearchGraph (Var n) :=
  { modes := (List.range (nR p)).map (modeOf p n),
    edges := (List.range (nR p)).flatMap (fun q => (mRof p q).next.map (edgeOf p n pruned q)) }

variable {p n}
variable {pruned : String → String → Bool}

theorem grOf_len : (grOf p n pruned).modes.length = nR p := by simp [grOf]

theorem grOf_modeAt {q : ℕ} (hq : q < nR p) :
    (grOf p n pruned).modeAt q = some (modeOf p n q) := by
  simp [grOf, SearchGraph.modeAt, hq]

theorem grOf_modeAt_inv {q : ℕ} {m : RMode (Var n)} (hm : (grOf p n pruned).modeAt q = some m) :
    q < nR p ∧ m = modeOf p n q := by
  by_cases hq : q < nR p
  · rw [grOf_modeAt hq] at hm
    exact ⟨hq, (Option.some.injEq _ _).mp hm.symm⟩
  · exfalso
    simp [grOf, SearchGraph.modeAt, hq] at hm

theorem grOf_sys {q : ℕ} {m : RMode (Var n)} (hm : (grOf p n pruned).modeAt q = some m) :
    m.sys = rightBlock (fR p n q) (Term.const 1) := by
  obtain ⟨-, rfl⟩ := grOf_modeAt_inv hm; rfl
theorem grOf_dom {q : ℕ} {m : RMode (Var n)} (hm : (grOf p n pruned).modeAt q = some m) :
    m.dom = domR p n := by
  obtain ⟨-, rfl⟩ := grOf_modeAt_inv hm; rfl
theorem grOf_weight {q : ℕ} {m : RMode (Var n)} (hm : (grOf p n pruned).modeAt q = some m) :
    m.weight = 1 := by
  obtain ⟨-, rfl⟩ := grOf_modeAt_inv hm; rfl

theorem edgesFrom_grOf {q : ℕ} {e : REdge (Var n)} (he : e ∈ (grOf p n pruned).edgesFrom q) :
    q < nR p ∧ ∃ nm ∈ (mRof p q).next, e = edgeOf p n pruned q nm := by
  have hmem : e ∈ (grOf p n pruned).edges := List.mem_of_mem_filter he
  have hsrc : e.src = q := by
    unfold SearchGraph.edgesFrom at he
    rw [List.mem_filter] at he
    exact decide_eq_true_eq.mp he.2
  simp only [grOf, List.mem_flatMap, List.mem_range, List.mem_map] at hmem
  obtain ⟨q', hq', nm, hnm, rfl⟩ := hmem
  simp only [edgeOf] at hsrc
  subst hsrc
  exact ⟨hq', nm, hnm, rfl⟩

theorem edge_mem_grOf {q : ℕ} (hq : q < nR p) {nm : String} (hnm : nm ∈ (mRof p q).next) :
    edgeOf p n pruned q nm ∈ (grOf p n pruned).edgesFrom q :=
  List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq,
    List.mem_map.mpr ⟨nm, hnm, rfl⟩⟩, by simp [edgeOf]⟩

theorem grOf_guards : ∀ q, ∀ e ∈ (grOf p n pruned).edgesFrom q, e.guard = guardR p n e.tgt := by
  intro q e he
  obtain ⟨-, nm, -, rfl⟩ := edgesFrom_grOf he
  rfl

theorem grOf_pruned {q : ℕ} {e : REdge (Var n)} (he : e ∈ (grOf p n pruned).edgesFrom q) :
    ∃ nm ∈ (mRof p q).next, e.tgt = tgtIdx p nm ∧ e.pruned = pruned (mRof p q).name nm := by
  obtain ⟨-, nm, hnm, rfl⟩ := edgesFrom_grOf he
  exact ⟨nm, hnm, rfl, rfl⟩

/-! ## The left automaton -/

variable (p n)

/-- The window of left mode `l`: `?guard_l ; clock := 0 ; flow_l` (one interval of duration
at most `dt`), the clock on `tg`. -/
noncomputable def windowOf (tg : Var n) (dt : ℝ) (l : ℕ) : Program (Var n) :=
  gwindowSeg (guardL p n l) (leftBlock (fL p n l)) (domL p n) tg dt 1

/-- The declared left transitions, by index. -/
def nextL : List (List ℕ) :=
  (List.range (nL p)).map (fun l => (mLof p l).next.filterMap (Handoff.leftModeIndex p))

noncomputable def leftAutOf (tg : Var n) (dt : ℝ) : LeftAut n :=
  { windows := (List.range (nL p)).map (windowOf p n tg dt),
    guards := (List.range (nL p)).map (guardL p n),
    next := nextL p }

variable {p n}

theorem leftAutOf_numModes (tg : Var n) (dt : ℝ) : (leftAutOf p n tg dt).numModes = nL p := by
  simp [leftAutOf, LeftAut.numModes]

theorem leftAutOf_window (tg : Var n) (dt : ℝ) {t : ℕ} (ht : t < nL p) :
    (leftAutOf p n tg dt).window t = windowOf p n tg dt t := by
  simp [leftAutOf, LeftAut.window, ht]

theorem leftAutOf_guard (tg : Var n) (dt : ℝ) {t : ℕ} (ht : t < nL p) :
    (leftAutOf p n tg dt).guard t = guardL p n t := by
  simp [leftAutOf, LeftAut.guard, ht]

theorem leftAutOf_succ (tg : Var n) (dt : ℝ) (m' : ℕ) :
    (leftAutOf p n tg dt).succ m' = (nextL p).getD m' [] := rfl

theorem leftModeIndex_lt {nm : String} {t : ℕ} (h : Handoff.leftModeIndex p nm = some t) :
    t < nL p := by
  unfold Handoff.leftModeIndex at h
  exact (List.findIdx?_eq_some_iff_findIdx_eq.mp h).1

theorem nextL_lt : ∀ m' < nL p, ∀ t ∈ (nextL p).getD m' [], t < nL p := by
  intro m' hm' t ht
  simp only [nextL] at ht
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm'] at ht
  simp only [Option.map_some, Option.getD_some, List.mem_filterMap] at ht
  obtain ⟨nm, -, hnm⟩ := ht
  exact leftModeIndex_lt hnm

/-! ## The kept atoms, the barrier terms, the anchor -/

variable (p n) (cX : Oracle.EvolStrengtheningX) (cov : CoverEmitE)

noncomputable def cL (l : ℕ) : List (CutAtomP n) :=
  cutPairsX (vars p) n Side.L (cutAtomsOfX cX.L (mLof p l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP n) :=
  cutPairsX (vars p) n Side.R (cutAtomsOfX cX.R (mRof p q).name)
noncomputable def cuts (q : ℕ) : Formula (Var n) := cutF (cR p n cX q)

/-- The cover record's pruned-edge predicate, by names. -/
def prunedOf (a b : String) : Bool := cov.pruned.contains (a, b)

/-- The pruned exits of right mode `q`, by index. -/
def prunedTgts (q : ℕ) : List ℕ :=
  ((mRof p q).next.filter (fun nm => prunedOf cov (mRof p q).name nm)).map (tgtIdx p)

/-- The barrier term of a pruned exit into `t`: the tool's `guardTerm` of `t`'s guard, so that
`t`'s guard implies `barrier > 0`; `≤ 0` is kept by the right flow (Theorem 2). -/
noncomputable def barrierOf (t : ℕ) : Term (Var n) :=
  ((NonConn.guardTerm (vars p) n (mRof p t).guard).map ITerm.toHost).getD (Term.const 0)

noncomputable def barriers (q : ℕ) : List (Term (Var n)) :=
  (prunedTgts p cov q).map (barrierOf p n)

/-- **The anchor** of window `l` at right mode `q`: the row, the kept atoms of both modes, the
barrier terms of `q`'s pruned exits, the evolve envelope. -/
noncomputable def AG (l q : ℕ) : Formula (Var n) :=
  Formula.and (FM (g p n l) (gs p n l ++ atomTerms (cL p n cX l) (cR p n cX q) ++
    barriers p n cov q)) (env p n)

/-! ## The time model of a window -/

/-- The cover of left mode `l` in the record (by name; an absent one is the empty cover). -/
def coverOf (l : ℕ) : LeftCoverE :=
  (cov.covers.find? (·.mL == (mLof p l).name)).getD ⟨"", 1, 0, [], [], []⟩

def strataOf (l q : ℕ) : PairStrataE :=
  ((coverOf p cov l).strata.find? (·.mR == (mRof p q).name)).getD ⟨"", [], [], [], 1, 1⟩

def flagsOf (l q : ℕ) : ModeFlagsE :=
  ((coverOf p cov l).flags.find? (·.name == (mRof p q).name)).getD ⟨"", false, false, false⟩

/-- The stretch of pairing `(l, q)` as the record states it. -/
def lamQ (l q : ℕ) : ℚ := ((strataOf p cov l q).lamN : ℚ) / ((strataOf p cov l q).lamD : ℚ)

noncomputable def lam (l q : ℕ) : ℝ := ((lamQ p cov l q : ℚ) : ℝ)

noncomputable def epsL : ℝ := (((Run.parseRat p.L.epsilon).getD 1 : ℚ) : ℝ)

/-- The common segment span of window `l`: `εR / lamQ`. -/
noncomputable def δ (l : ℕ) : ℝ := epsR p / (((coverOf p cov l).lamQ : ℚ) : ℝ)

def B (l : ℕ) : ℕ := (coverOf p cov l).bBudget

/-- The cover's per-window choice data (no chosen sets: the all-successors rules). -/
def chOf (l : ℕ) : ChoiceData :=
  { jointOK := fun q => (flagsOf p cov l q).jointOK,
    repoPre := fun q => (flagsOf p cov l q).dynPre,
    repoPost := fun q => (flagsOf p cov l q).dynPost,
    jointS := fun _ => [], repoS := fun _ _ => [], hopS := fun _ _ => [] }

/-- The admissible starts of window `l`, by index. -/
def admissibleOf (l : ℕ) : List ℕ := (coverOf p cov l).admissible.map (tgtIdx p)

end Data

/-! ## The atom-level checks a certificate side must pass -/

/-- A kept atom is a closed threshold `a ≤ b` / `a ≥ b` whose sides mention no `bad` name, it
lowers on its side, and its entry condition is not a Z3 one. -/
def atomOK (vars : List String) (n : ℕ) (side : Side) (bad : String) (x : CutAtomX) : Bool :=
  (match x.atom with
   | .cmp op a b => (op == "<=" || op == ">=") && PExpr.namesFree bad a && PExpr.namesFree bad b
   | _ => false) &&
  (lowerF vars n side x.atom).isSome && x.entry != CutEntry.z3

/-- Every atom passes `atomOK` and its `given` forms are earlier atoms of the list. -/
def atomsWF (vars : List String) (n : ℕ) (side : Side) (bad : String) (atoms : List CutAtomX) :
    Bool :=
  (List.range atoms.length).all (fun i =>
    match atoms[i]? with
    | some x => atomOK vars n side bad x && x.given.all (fun f => (atoms.take i).any (·.atom == f))
    | none => false)

/-! ## Structural facts decided in the kernel -/

section Struct

variable (p : PProblem) (n : ℕ) (cov : CoverEmitE)

/-- Every mode of a side shares the side's first mode's evolve domain. -/
def uniformEvolve : Bool :=
  p.L.modes.all (·.evolve == (mLof p 0).evolve) && p.R.modes.all (·.evolve == (mRof p 0).evolve)

/-- No cross-side names: a right mode's guard, evolve and fields mention no `L_` name, a left
mode's none `R_`. -/
def namesOK : Bool :=
  p.R.modes.all (fun m => PForm.namesFree "L_" m.guard && PForm.namesFree "L_" m.evolve &&
    m.odes.all (fun o => PExpr.namesFree "L_" o.2)) &&
  p.L.modes.all (fun m => PForm.namesFree "R_" m.guard && PForm.namesFree "R_" m.evolve &&
    m.odes.all (fun o => PExpr.namesFree "R_" o.2))

/-- Mode names are distinct and every declared successor name is a declared mode. -/
def namesResolve : Bool :=
  (p.R.modes.map (·.name)).Nodup && (p.L.modes.map (·.name)).Nodup &&
  p.R.modes.all (fun m => m.next.all (fun nm => p.R.modes.any (·.name == nm)))

/-- Every window's row lowers to at least one component. -/
def rowsOK : Bool := (List.range (nL p)).all (fun l => 0 < compsLen p n l)

/-- The record's time model: positive stretches, each pairing's stretch at most its window's,
and the budget covers one left interval (`bBudget · εR ≥ εL · lamQ`). -/
def timeOK : Bool :=
  let eL : ℚ := (Run.parseRat p.L.epsilon).getD 1
  let eR : ℚ := (Run.parseRat p.R.epsilon).getD 1
  0 < eR && 0 < eL &&
  (List.range (nL p)).all (fun l =>
    let lc := coverOf p cov l
    0 < lc.lamQ && (lc.bBudget : ℚ) * eR ≥ eL * lc.lamQ &&
    (List.range (nR p)).all (fun q =>
      let s := strataOf p cov l q
      0 < s.lamN && 0 < s.lamD && lamQ p cov l q ≤ lc.lamQ))

/-- Every mode's guard, evolve domain and field lower on its side. -/
def lowersOK : Bool :=
  p.L.modes.all (fun m => (lowerF (vars p) n Side.L m.guard).isSome &&
    (lowerF (vars p) n Side.L m.evolve).isSome && (dynOf (vars p) n Side.L m).isSome) &&
  p.R.modes.all (fun m => (lowerF (vars p) n Side.R m.guard).isSome &&
    (lowerF (vars p) n Side.R m.evolve).isSome && (dynOf (vars p) n Side.R m).isSome)

/-- The handoff runner's by-name row of each left mode is the by-index row. -/
def rowsByName : Bool :=
  (List.range (nL p)).all (fun l => Handoff.invRowOf p (mLof p l) == some (rowOf p l))

/-- The strata orders of the certified pairings (joint, pre- and post-joint reposition) are
permutations of the row's component indices. -/
def permOK : Bool :=
  (List.range (nL p)).all (fun l => (List.range (nR p)).all (fun q =>
    let fl := flagsOf p cov l q
    let s := strataOf p cov l q
    let k := compsLen p n l
    (!fl.jointOK || decide (s.order.Perm (List.range k))) &&
    (!fl.dynPre || decide (s.dynPreOrder.Perm (List.range k))) &&
    (!fl.dynPost || decide (s.dynPostOrder.Perm (List.range k)))))

/-- The kept-atom lists of every mode pass `atomsWF`, and the extended certificate is
well-formed (`evolStrengtheningWFX`). -/
def cutsOK (cX : Oracle.EvolStrengtheningX) : Bool :=
  Oracle.evolStrengtheningWFX p cX &&
  p.L.modes.all (fun m => atomsWF (vars p) n Side.L "R_" (cutAtomsOfX cX.L m.name)) &&
  p.R.modes.all (fun m => atomsWF (vars p) n Side.R "L_" (cutAtomsOfX cX.R m.name)) &&
  cX.L.all (fun e => p.L.modes.any (·.name == e.1)) &&
  cX.R.all (fun e => p.R.modes.any (·.name == e.1))

def structOK (cX : Oracle.EvolStrengtheningX) : Bool :=
  uniformEvolve p && namesOK p && namesResolve p && rowsOK p n && timeOK p cov &&
  lowersOK p n && rowsByName p && permOK p n cov && cutsOK p n cX && 0 < nR p &&
  (vars p).length ≤ n

variable {p n cov}

theorem structOK_iff {cX : Oracle.EvolStrengtheningX} : structOK p n cov cX = true ↔
    uniformEvolve p = true ∧ namesOK p = true ∧ namesResolve p = true ∧ rowsOK p n = true ∧
    timeOK p cov = true ∧ lowersOK p n = true ∧ rowsByName p = true ∧ permOK p n cov = true ∧
    cutsOK p n cX = true ∧ 0 < nR p ∧ (vars p).length ≤ n := by
  simp only [structOK, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-! ### Modes in range, by index -/

theorem mLof_mem {l : ℕ} (hl : l < nL p) : mLof p l ∈ p.L.modes := by
  unfold mLof; rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl
theorem mRof_mem {q : ℕ} (hq : q < nR p) : mRof p q ∈ p.R.modes := by
  unfold mRof; rw [List.getD_eq_getElem _ _ hq]; exact List.getElem_mem hq
theorem mLof_dm {l : ℕ} (hl : ¬ l < nL p) : mLof p l = dm := by
  unfold mLof; exact List.getD_eq_default _ _ (Nat.le_of_not_lt hl)
theorem mRof_dm {q : ℕ} (hq : ¬ q < nR p) : mRof p q = dm := by
  unfold mRof; exact List.getD_eq_default _ _ (Nat.le_of_not_lt hq)

/-! ### Uniform evolve domains -/

theorem evolve_L_eq (h : uniformEvolve p = true) {l : ℕ} (hl : l < nL p) :
    (mLof p l).evolve = (mLof p 0).evolve := by
  simp only [uniformEvolve, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact h.1 _ (mLof_mem hl)
theorem evolve_R_eq (h : uniformEvolve p = true) {q : ℕ} (hq : q < nR p) :
    (mRof p q).evolve = (mRof p 0).evolve := by
  simp only [uniformEvolve, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact h.2 _ (mRof_mem hq)

theorem hostEvolve_L (h : uniformEvolve p = true) {l : ℕ} (hl : l < nL p) :
    hostEvolve (vars p) n Side.L (mLof p l) = domL p n := by
  unfold domL hostEvolve; rw [evolve_L_eq h hl]
theorem hostEvolve_R (h : uniformEvolve p = true) {q : ℕ} (hq : q < nR p) :
    hostEvolve (vars p) n Side.R (mRof p q) = domR p n := by
  unfold domR hostEvolve; rw [evolve_R_eq h hq]

/-! ### Sides -/

theorem names_R (h : namesOK p = true) (q : ℕ) :
    PForm.namesFree "L_" (mRof p q).guard = true ∧ PForm.namesFree "L_" (mRof p q).evolve = true ∧
    (mRof p q).odes.all (fun o => PExpr.namesFree "L_" o.2) = true := by
  by_cases hq : q < nR p
  · simp only [namesOK, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h.1 _ (mRof_mem hq)
    exact ⟨h1, h2, List.all_eq_true.mpr h3⟩
  · rw [mRof_dm hq]; decide
theorem names_L (h : namesOK p = true) (l : ℕ) :
    PForm.namesFree "R_" (mLof p l).guard = true ∧ PForm.namesFree "R_" (mLof p l).evolve = true ∧
    (mLof p l).odes.all (fun o => PExpr.namesFree "R_" o.2) = true := by
  by_cases hl : l < nL p
  · simp only [namesOK, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h.2 _ (mLof_mem hl)
    exact ⟨h1, h2, List.all_eq_true.mpr h3⟩
  · rw [mLof_dm hl]; decide

theorem guardR_fv (h : namesOK p = true) (q : ℕ) : (guardR p n q).fv ⊆ range Rv :=
  hostGuard_fv_R (vars p) (mRof p q) (names_R h q).1
theorem guardL_fv (h : namesOK p = true) (l : ℕ) : (guardL p n l).fv ⊆ range Lv :=
  hostGuard_fv_L (vars p) (mLof p l) (names_L h l).1

theorem domR_fv (h : namesOK p = true) : (domR p n).fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R (vars p)) (some (mRof p 0))
    (by simpa using (names_R h 0).2.1) x hx)
theorem domL_fv (h : namesOK p = true) : (domL p n).fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L (vars p)) (some (mLof p 0))
    (by simpa using (names_L h 0).2.1) x hx)

theorem fR_fv (h : namesOK p = true) (q : ℕ) : ∀ i, (fR p n q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R (vars p)) (some (mRof p q))
    (by simpa using (names_R h q).2.2) i x hx)
theorem fL_fv (h : namesOK p = true) (l : ℕ) : ∀ i, (fL p n l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L (vars p)) (some (mLof p l))
    (by simpa using (names_L h l).2.2) i x hx)

theorem grOf_guardsRight (h : namesOK p = true) {pruned : String → String → Bool} :
    GuardsRight (grOf p n pruned) := by
  intro q e he
  rw [grOf_guards q e he]
  exact guardR_fv h _

/-! ### Edge targets in range -/

theorem tgtIdx_lt (h : namesResolve p = true) {q : ℕ} (hq : q < nR p) {nm : String}
    (hnm : nm ∈ (mRof p q).next) : tgtIdx p nm < nR p := by
  simp only [namesResolve, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at h
  obtain ⟨m, hm, hname⟩ := h.2 _ (mRof_mem hq) nm hnm
  exact List.findIdx_lt_length.mpr ⟨m, hm, hname⟩

theorem grOf_lt (h : namesResolve p = true) {pruned : String → String → Bool} :
    ∀ q, ∀ e ∈ (grOf p n pruned).edgesFrom q, e.tgt < (grOf p n pruned).modes.length := by
  intro q e he
  obtain ⟨hq, nm, hnm, rfl⟩ := edgesFrom_grOf he
  rw [grOf_len]
  exact tgtIdx_lt h hq hnm

/-- A resolved successor name is the name of the mode at its index. -/
theorem name_tgtIdx (h : namesResolve p = true) {q : ℕ} (hq : q < nR p) {nm : String}
    (hnm : nm ∈ (mRof p q).next) : (mRof p (tgtIdx p nm)).name = nm := by
  have hlt := tgtIdx_lt h hq hnm
  unfold mRof tgtIdx at hlt ⊢
  rw [List.getD_eq_getElem _ _ hlt]
  have := List.findIdx_getElem (p := fun m : PMode => m.name == nm) (xs := p.R.modes) (w := hlt)
  simpa using this

end Struct

end Emitted
end RelCertifier
