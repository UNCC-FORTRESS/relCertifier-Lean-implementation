/-
# `decideWellFormed` — the decidable well-formedness checker (statements + checker, phase A)

The reduction this file mechanizes: for the SETTLING model class, per-benchmark soundness
reduces to (a) this decidable checker passing on the model data, plus (b) the per-run Z3
certificates — tied together by ONE theorem (`WellFormedSound`, stated below; proof is the
phased build described at the bottom). This is the `decideCovered`/`check_sound` pattern
applied to the settling hypothesis: untrusted construction, verified checkable acceptance.

WHAT THE CHECKER DECIDES (all rational arithmetic / structural — no ODE solving, no Z3):

* the shared envelope's bands are well-ordered, and every mode's guard band sits inside the
  envelope band of its guarded coordinate;
* every mode SETTLES, by shape:
  - `contract k c` (`x' = k(c − x)`, `k ≥ 0`) with the equilibrium INSIDE the mode's own guard
    band (`a ≤ c ≤ cap`) — stays and self-lands (tangent case `c = cap` included);
  - `constRate c` (`x' = c`, `0 ≤ c`) with MARGIN (`cap + c·dt ≤ envelope-hi`) and a
    self-or-declared-successor guard band covering the one-step image
    (`[a + c·dt, cap + c·dt]`);
  - `frozen` (`x' = 0`) — holds anywhere it starts;
* (phase-A fragment) every NON-guarded coordinate of a mode is `frozen` — the single-active-
  coordinate class; driven coordinates (`x' = y`) are phase B/C (see the plan);
* declared successors are valid mode indices.

THE BASE-SET CORRECTION (found while stating this): `GuardSettlingB` quantifies over the guard
region, so for multi-coordinate models the guard map must be `GdOf M q := envelope ∧ guard-band`
— the mode's operating region WITHIN PHYSICS. A bare guard band would admit bases whose
unguarded coordinates violate the envelope at `t = 0`, making the hypothesis vacuously false.
The threaded invariant then carries "in the current guard band AND in the envelope", which is
exactly what entry (landing in a successor's `GdOf`) re-establishes: envelope membership from
the staying clause, band membership from the landing clause.

TRUST/AXIOMS: this file is definitions plus decidable functions (no `native_decide` anywhere —
evaluation is `decide`/`#eval`-class ℚ arithmetic, per project discipline).
-/
import RelCertifier.GuardThreaded

namespace RelCertifier
open DL Function Set

variable {n : ℕ}

/-! ## The settling model (rational data) -/

/-- Per-coordinate field shape of a mode (phase-A shapes; `driven` is phase B/C). -/
inductive CoordShape where
  | frozen                          -- x' = 0
  | constRate (c : ℚ)               -- x' = c
  | contract (k c : ℚ)              -- x' = k (c − x)
  deriving Repr, DecidableEq

/-- An optional band `[lo, hi]` (either side may be absent = unbounded). -/
structure Band where
  lo : Option ℚ := none
  hi : Option ℚ := none
  deriving Repr, DecidableEq

/-- One right mode of a settling model: its per-coordinate shapes, the single guarded
coordinate and its band, and the declared successor indices. -/
structure SettlingMode (n : ℕ) where
  shapes : Fin n → CoordShape
  gcoord : Fin n
  glo    : ℚ
  ghi    : ℚ
  succs  : List ℕ

/-- A settling model: the right modes, the shared envelope (per-coordinate bands), and the
budget data (`dt = epsR / lamMin`). -/
structure SettlingModel (n : ℕ) where
  modes  : List (SettlingMode n)
  env    : Fin n → Band
  epsR   : ℚ
  lamMin : ℚ

/-- The control-step budget. -/
def SettlingModel.dt (M : SettlingModel n) : ℚ := M.epsR / M.lamMin

/-! ## The checker (computable, ℚ arithmetic) -/

def bandOrdered (b : Band) : Bool :=
  match b.lo, b.hi with
  | some l, some h => decide (l ≤ h)
  | _, _ => true

/-- `[lo₁, hi₁] ⊆ b` (absent outer side = no constraint). -/
def bandInside (lo hi : ℚ) (b : Band) : Bool :=
  (b.lo.all fun bl => decide (bl ≤ lo)) && (b.hi.all fun bh => decide (hi ≤ bh))

/-- One mode's settling check (see the header). `q` is the mode's own index (for the
self-landing option). -/
def checkMode (M : SettlingModel n) (q : ℕ) (m : SettlingMode n) : Bool :=
  let dt := M.dt
  decide (m.glo ≤ m.ghi) &&
  bandInside m.glo m.ghi (M.env m.gcoord) &&
  -- phase-A fragment: every non-guarded coordinate frozen
  ((List.finRange n).all fun i => i == m.gcoord || m.shapes i == CoordShape.frozen) &&
  m.succs.all (fun q' => decide (q' < M.modes.length)) &&
  (match m.shapes m.gcoord with
   | .frozen => true                                       -- holds; self-lands
   | .contract k c =>
       decide (0 ≤ k) && decide (m.glo ≤ c) && decide (c ≤ m.ghi)   -- eq inside own band
   | .constRate c =>
       decide (0 ≤ c) &&
       -- margin: one step cannot cross the envelope
       ((M.env m.gcoord).hi.all fun hi => decide (m.ghi + c * dt ≤ hi)) &&
       -- landing: some self-or-successor band covers the one-step image
       ((q :: m.succs).any fun q' =>
         match M.modes[q']? with
         | some m' =>
             m'.gcoord == m.gcoord &&
             decide (m'.glo ≤ m.glo + c * dt) && decide (m.ghi + c * dt ≤ m'.ghi)
         | none => false))

/-- **The well-formedness checker.** Decidable; no Z3, no ODE reasoning. -/
def decideWellFormed (M : SettlingModel n) : Bool :=
  decide (0 < M.lamMin) && decide (0 ≤ M.epsR) &&
  ((List.finRange n).all fun i => bandOrdered (M.env i)) &&
  (List.range M.modes.length).all (fun q =>
    match M.modes[q]? with
    | some m => checkMode M q m
    | none => false)

/-! ## The transcription: settling model → the proof objects -/

/-- The field term of one coordinate shape. -/
noncomputable def CoordShape.field (i : Fin n) : CoordShape → Term (Var n)
  | .frozen => Term.const 0
  | .constRate c => Term.const (c : ℝ)
  | .contract k c =>
      Term.binop AOp.mul (Term.const (k : ℝ))
        (Term.binop AOp.sub (Term.const (c : ℝ)) (Term.var (Rv i)))

/-- The mode's right field. -/
noncomputable def SettlingMode.fieldOf (m : SettlingMode n) : Fin n → Term (Var n) :=
  fun i => (m.shapes i).field i

/-- One coordinate's envelope conjunct(s). -/
noncomputable def Band.formula (i : Fin n) (b : Band) : Formula (Var n) :=
  Formula.and
    (match b.lo with
     | some l => Formula.cmp CompOp.le (Term.const (l : ℝ)) (Term.var (Rv i))
     | none => Formula.tt)
    (match b.hi with
     | some h => Formula.cmp CompOp.le (Term.var (Rv i)) (Term.const (h : ℝ))
     | none => Formula.tt)

/-- The shared envelope as a Formula (the uniform evolution domain). -/
noncomputable def SettlingModel.envF (M : SettlingModel n) : Formula (Var n) :=
  (List.finRange n).foldr (fun i acc => Formula.and (Band.formula i (M.env i)) acc) Formula.tt

/-- The guard map: the mode's guard band INTERSECTED WITH THE ENVELOPE (the base-set
correction — see the header). Out-of-range indices get the unsatisfiable-by-convention `ff`
shape (here: an empty band statement is fine since the H only reads declared indices). -/
noncomputable def SettlingModel.GdOf (M : SettlingModel n) : ℕ → Formula (Var n) :=
  fun q => match M.modes[q]? with
    | some m => Formula.and M.envF (bandDom m.gcoord (m.glo : ℝ) (m.ghi : ℝ))
    | none => Formula.tt

/-- The search graph of a settling model: each mode's system is its right block over the
shared envelope; edges are the ⊤-guarded self-loop plus the declared successors. -/
noncomputable def SettlingModel.graph (M : SettlingModel n) : SearchGraph (Var n) :=
  { modes := M.modes.map (fun m =>
      { sys := rightBlock m.fieldOf (Term.const 1), dom := M.envF, weight := 1 })
    edges := (List.range M.modes.length).flatMap (fun q =>
      match M.modes[q]? with
      | some m =>
          ({ src := q, tgt := q, guard := Formula.tt, pruned := false } :: m.succs.map
            (fun q' => { src := q, tgt := q', guard := Formula.tt, pruned := false }))
      | none => []) }

/-! ## The soundness statement (`wellformed_sound`) — statement-first

The theorem this file exists for, as a `Prop` (the phased proof plan is below; the statement
is fixed now so the phases target it):

`WellFormedSound M mv tg g fL` says — given
* the checker passed (`decideWellFormed M = true`),
* the freshness side-conditions for the auxiliary coordinates `mv`, `tg` (all provable
  generically for `Aux`-side choices, since every formula this file builds mentions only
  `Rv`-coordinates — the helper lemmas are part of phase A'),
* the per-run Z3 certificates (`BoxLe` for each mode over the envelope from `GdOf`-bases —
  the ONLY semantic input, `z3_unsat_sound` at its construction),

then the settling hypothesis `GuardSettlingH` holds for the transcribed model — and hence
`theorem3_faithful_settling` applies, yielding `rvalid` for the benchmark. -/
def WellFormedSound (M : SettlingModel n) (mv tg : Var n) (g : Term (Var n))
    (fL : Fin n → Term (Var n)) : Prop :=
  decideWellFormed M = true →
  (0 : ℝ) ≤ (M.dt : ℝ) →
  mv ∉ g.fv → mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound → mv ≠ tg →
  (∀ q', mv ∉ (M.GdOf q').fv) → (∀ q', tg ∉ (M.GdOf q').fv) →
  (∀ q', ∀ x ∈ (M.GdOf q').fv, x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound) →
  (∀ q m, M.graph.modeAt q = some m → ∀ ν, Formula.sat (M.GdOf q) ν →
      BoxLe (Program.ode m.sys M.envF) (fun ω => Term.eval g ω) ν) →
  GuardSettlingH M.graph M.GdOf mv g (Term.const 1) tg (M.dt : ℝ) fL M.envF

/-! ## The phased proof plan (targets the statement above; each phase lands sorry-free)

* **Phase A' (bookkeeping + single-active-coordinate discharge).** Prove `WellFormedSound`
  for the phase-A fragment the checker currently accepts (single guarded coordinate, others
  frozen). Ingredients: `sat`-reflection for `envF`/`GdOf` (fold ↔ per-coordinate bands);
  `fv ⊆ Rv`-image lemmas discharging the freshness hypotheses for `Aux`-side `mv`/`tg`;
  env-aware variants of the two discharge lemmas (`GuardSettlingB_of_contract` /
  `_of_margin_const` with `Gd = envF ∧ band` and `domR = envF` — same witnesses, which
  already freeze the non-active coordinates; the new content is per-conjunct envelope
  preservation for frozen coordinates, from the base's envelope membership). Expected pass
  set: watertank, robot_braking, the arm/plant family (single-θ right sides) — ~10–12.
* **Phase B (driven-by-const: `x' = y`, `y' = c`).** The integrator shape with the banked
  quadratic witness (`GapThreeRoverTooling.roverΦR` pattern); one-sided envelope bounds
  with signed drift (the rover family's `px ≥ lo` with `vx > 0`) or two-sided with margin
  against the driving coordinate's band (via `staying_from_margin`, which is already
  deriv-bound-generic). Adds the rover family (+3–4).
* **Phase C (driven-by-contract: `x' = y`, `y' = k(c − y)`).** The exp-integral witness
  (`s(t) = s₀ + c·t + (y₀ − c)(1 − e^{−kt})/k`); adds the terrain/endurance/story families
  (~20).
* **Phase D (checker-side Z3 route for coupled shapes).** For fields outside closed-form
  shapes (attitude_rate), let the checker delegate the per-conjunct invariance to the same
  trusted route-B query the cut channel uses — the `GuardSettlingB` obligation then rests on
  the Z3 leaf like everything else. Turns the remaining case-1 holdouts checkable.
-/

end RelCertifier
