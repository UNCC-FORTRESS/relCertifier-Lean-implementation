/-
# `decideWellFormed` — the decidable well-formedness checker (phases A′/B/C + EXT 1/2/4 PROVEN)

The reduction this file mechanizes: for the SETTLING model class, per-benchmark soundness
reduces to (a) this decidable checker passing on the model data, plus (b) the per-run Z3
certificates — tied together by ONE theorem (`WellFormedSound`, stated below; proof is the
phased build described at the bottom). This is the `decideCovered`/`check_sound` pattern
applied to the settling hypothesis: untrusted construction, verified checkable acceptance.

WHAT THE CHECKER DECIDES (all integer arithmetic / structural — no ODE solving, no Z3):

* the shared envelope's bands are well-ordered, and every mode's guard band sits inside the
  envelope band of its guarded coordinate;
* every mode SETTLES, by shape:
  - `contract k c` (`x' = k(c − x)`, `k ≥ 0`) with the equilibrium INSIDE the mode's own guard
    band (`a ≤ c ≤ cap`) — stays and self-lands (tangent case `c = cap` included) — or (EXT 4)
    ABOVE it (`cap < c ≤ envelope-hi`, a transit-up mode: the flow stays in the hull
    `[a, c]` and the endpoint lands in the own band or a declared successor band that touches
    it, `glo' ≤ cap ∧ c ≤ ghi'`) or BELOW it (`envelope-lo ≤ c < a`, `0 ≤ c`, the mirror);
  - `constRate c` (`x' = c`, `0 ≤ c`) with MARGIN (`cap + c·dt ≤ envelope-hi`) and the one-step
    image `[a + c·dt, cap + c·dt]` covered by a single self-or-successor band OR (EXT 4) by
    the UNION of the own band with one touching successor band (`glo' ≤ cap ∧
    cap + c·dt ≤ ghi'`; landing discharged by an endpoint case-split at `cap`);
  - `frozen` (`x' = 0`) — holds anywhere it starts;
* non-guarded coordinates are `frozen`, DRIVEN by the active coordinate (`x' = x_active`,
  phases B/C: quadratic / exp-integral witnesses), or driven by a non-active frozen
  coordinate when envelope-free (EXT 2); const rates may be NEGATIVE (EXT 1, lower-side
  margin and lower-edge union — the Return modes);
* declared successors are valid mode indices.

STATUS: `wellformed_sound` is PROVEN for this whole grammar (EXT 4's union covers included —
`settling_contract_above`/`settling_contract_below` and the `hland` disjunctions of the const
lemmas). The known completeness gaps, in build order: the RATIONAL-GAIN (exp-bound) class — a
transit contract whose equilibrium lies beyond the adjacent successor band needs the sharper
finite-dt cap `cap + (c − cap)(1 − e^{−k·dt})`, which the integer model cannot express (both
factors of `k·dt < 1` would have to be integers; needs `contract kNum kDen c` + a
`1 − e^{−x} ≤ x` lemma); EXT 3 — multi-band guards + driven-active coordinates (the s-guarded
terrain family); phase D — coupled fields (flow existence via `PicardBridge`).

THE BASE-SET CORRECTION (found while stating this): `GuardSettlingB` quantifies over the guard
region, so for multi-coordinate models the guard map must be `GdOf M q := envelope ∧ guard-band`
— the mode's operating region WITHIN PHYSICS. A bare guard band would admit bases whose
unguarded coordinates violate the envelope at `t = 0`, making the hypothesis vacuously false.
The threaded invariant then carries "in the current guard band AND in the envelope", which is
exactly what entry (landing in a successor's `GdOf`) re-establishes: envelope membership from
the staying clause, band membership from the landing clause.

TRUST/AXIOMS: this file is definitions plus decidable functions (no `native_decide` anywhere —
evaluation is `decide`/`#eval`-class ℤ arithmetic, per project discipline).
-/
import RelCertifier.Proofs.Soundness.GuardThreaded

namespace RelCertifier
open DL Function Set

variable {n : ℕ}

/-! ## The settling model (integer data) -/

/-- Per-coordinate field shape of a mode (phase-A shapes; `driven` is phase B/C). -/
inductive CoordShape (n : ℕ) where
  | frozen                          -- x' = 0
  | constRate (c : ℤ)               -- x' = c
  | contract (k c : ℤ)              -- x' = k (c − x)
  | contractQ (kn kd c : ℤ)         -- x' = (kn/kd) (c − x): rational gain (the exp-bound ext)
  | driven (j : Fin n)              -- x' = x_j (integrator; phase B)
  | drivenDamp (j : Fin n) (dampers : List (Fin n × ℤ × ℤ))
      -- x' = x_j · (1 − Σ_d (aₙ/a_d)·x_{p_d}²): a damped integrator (the nonlinear-s'
      -- terrain family); each damper p_d is a contract-to-0 coordinate
  | riccati (b a : ℤ)               -- x' = b − (a/10⁶)·x²: quadratic drag toward √(10⁶b/a)
                                    -- (b, a both = real coefficient ×1000 under the value
                                    -- scaling; the 10⁶ divisor absorbs the squared scale)
  | pairSym (j : Fin n) (c h : ℤ)   -- x' = c − x + (h/1000)·x_j: one member of a weakly
                                    -- coupled symmetric pair (the partner j mirrors it);
                                    -- diagonalizes by x ± x_j to rates 1 ∓ h/1000
  | chase (j : Fin n) (k : ℤ)       -- x' = x_j − k·x: the angle member of a critically
                                    -- damped cascade, chasing its resonant driver
                                    -- (x_j' = −k·x_j); value (x₀ + x_j₀·t)e^{−kt}
  deriving Repr, DecidableEq

/-- An optional band `[lo, hi]` (either side may be absent = unbounded). -/
structure Band where
  lo : Option ℤ := none
  hi : Option ℤ := none
  deriving Repr, DecidableEq

/-- One right mode of a settling model: its per-coordinate shapes, the single guarded
coordinate and its band, and the declared successor indices. -/
structure SettlingMode (n : ℕ) where
  shapes : Fin n → CoordShape n
  gcoord : Fin n
  glo    : ℤ
  ghi    : ℤ
  succs  : List ℕ

/-- A settling model: the right modes, the shared envelope (per-coordinate bands), and the
budget data (`dt = epsR / lamMin`). -/
structure SettlingModel (n : ℕ) where
  modes  : List (SettlingMode n)
  env    : Fin n → Band
  /-- The control-step budget `εR / λmin` — stored pre-divided so the checker kernel-reduces
  (`Rat` division does not). -/
  dtQ    : ℤ

/-- The control-step budget. -/
def SettlingModel.dt (M : SettlingModel n) : ℤ := M.dtQ

/-! ## The checker (computable, ℤ arithmetic) -/

def bandOrdered (b : Band) : Bool :=
  match b.lo, b.hi with
  | some l, some h => decide (l ≤ h)
  | _, _ => true

/-- `[lo₁, hi₁] ⊆ b` (absent outer side = no constraint). -/
def bandInside (lo hi : ℤ) (b : Band) : Bool :=
  (b.lo.all fun bl => decide (bl ≤ lo)) && (b.hi.all fun bh => decide (hi ≤ bh))

/-- The eleven rational conditions of the coupled-pair discharge (EXT P), against the
landing target `TT`: band-in-cover, cover-in-envelope, equilibrium position, and the
vertex-capped amplitude bounds for both members (see `twoExp_le`). -/
def pairCondsB (glo ghi plo phi qlo qhi c h TT : ℤ) : Bool :=
  decide (ghi ≤ TT) && decide (TT ≤ phi) && decide (plo ≤ glo) &&
  decide (1000 * c ≤ TT * (1000 - h)) && decide (glo * (1000 - h) ≤ 1000 * c) &&
  decide ((ghi + qhi) * (1000 - h) + 2 * (1000 * c) ≤ 4 * TT * (1000 - h)) &&
  decide (4 * glo * (1000 - h) ≤ (glo + qlo) * (1000 - h) + 2 * (1000 * c)) &&
  decide (1000 * c ≤ qhi * (1000 - h)) && decide (qlo * (1000 - h) ≤ 1000 * c) &&
  decide ((ghi + qhi) * (1000 - h) + 2 * (1000 * c) ≤ 4 * qhi * (1000 - h)) &&
  decide (4 * qlo * (1000 - h) ≤ (glo + qlo) * (1000 - h) + 2 * (1000 * c))

/-- Its Prop form. -/
def PairConds (glo ghi plo phi qlo qhi c h TT : ℤ) : Prop :=
  ghi ≤ TT ∧ TT ≤ phi ∧ plo ≤ glo ∧
  1000 * c ≤ TT * (1000 - h) ∧ glo * (1000 - h) ≤ 1000 * c ∧
  (ghi + qhi) * (1000 - h) + 2 * (1000 * c) ≤ 4 * TT * (1000 - h) ∧
  4 * glo * (1000 - h) ≤ (glo + qlo) * (1000 - h) + 2 * (1000 * c) ∧
  1000 * c ≤ qhi * (1000 - h) ∧ qlo * (1000 - h) ≤ 1000 * c ∧
  (ghi + qhi) * (1000 - h) + 2 * (1000 * c) ≤ 4 * qhi * (1000 - h) ∧
  4 * qlo * (1000 - h) ≤ (glo + qlo) * (1000 - h) + 2 * (1000 * c)

theorem pairCondsB_true {glo ghi plo phi qlo qhi c h TT : ℤ}
    (hb : pairCondsB glo ghi plo phi qlo qhi c h TT = true) :
    PairConds glo ghi plo phi qlo qhi c h TT := by
  unfold pairCondsB at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  unfold PairConds
  tauto

/-- One mode's settling check (see the header). `q` is the mode's own index (for the
self-landing option). -/
def checkMode (M : SettlingModel n) (q : ℕ) (m : SettlingMode n) : Bool :=
  let dt := M.dt
  let othersFrozen :=
    (List.finRange n).all fun i =>
      decide (i = m.gcoord) || decide (m.shapes i = CoordShape.frozen)
  -- phase B: with a const-rate active coordinate, a non-guarded coordinate may also be
  -- DRIVEN BY the active one (x' = x_gcoord) — provided the driving rate is nonneg
  -- (0 ≤ glo, so the driven coordinate only grows) and its envelope has no upper wall.
  let othersFlex :=
    decide (0 ≤ m.glo) &&
    ((List.finRange n).all fun i =>
      decide (i = m.gcoord) || decide (m.shapes i = CoordShape.frozen) ||
      (decide (m.shapes i = CoordShape.driven m.gcoord) &&
        decide ((M.env i).hi = none)) ||
      -- EXT 2: driven by a non-active FROZEN coordinate, itself envelope-free
      (match m.shapes i with
       | CoordShape.driven j =>
           !decide (j = m.gcoord) && decide (m.shapes j = CoordShape.frozen) &&
           decide ((M.env i).lo = none) && decide ((M.env i).hi = none)
       | _ => false))
  -- EXT 4b: the extended flex condition (contract others with interior equilibria; and
  -- envelope-free integrators driven by them) — used by the contract-below branch
  let othersFlexC :=
    decide (0 ≤ m.glo) &&
    ((List.finRange n).all fun i =>
      decide (i = m.gcoord) || decide (m.shapes i = CoordShape.frozen) ||
      (decide (m.shapes i = CoordShape.driven m.gcoord) &&
        decide ((M.env i).hi = none)) ||
      (match m.shapes i with
       | CoordShape.driven j =>
           !decide (j = m.gcoord) && decide (m.shapes j = CoordShape.frozen) &&
           decide ((M.env i).lo = none) && decide ((M.env i).hi = none)
       | _ => false) ||
      (match m.shapes i with
       | CoordShape.contract k' c' =>
           decide (0 ≤ k') &&
           ((M.env i).lo.all fun lo => decide (lo ≤ c')) &&
           ((M.env i).hi.all fun hi => decide (c' ≤ hi))
       | _ => false) ||
      (match m.shapes i with
       | CoordShape.driven j =>
           !decide (j = m.gcoord) &&
           (match m.shapes j with
            | CoordShape.contract _ _ => true
            | _ => false) &&
           decide ((M.env i).lo = none) && decide ((M.env i).hi = none)
       | _ => false))
  decide (m.glo ≤ m.ghi) &&
  bandInside m.glo m.ghi (M.env m.gcoord) &&
  m.succs.all (fun q' => decide (q' < M.modes.length)) &&
  (match m.shapes m.gcoord with
   | .frozen => othersFrozen                               -- holds; self-lands
   | .contract k c =>
       decide (0 ≤ k) &&
       ((othersFlex &&
         (-- equilibrium inside the own band: self-landing (phases A'/C)
          (decide (m.glo ≤ c) && decide (c ≤ m.ghi)) ||
          -- EXT 4: equilibrium ABOVE the band — transit up; the flow stays in the hull [glo, c]
          (decide (m.ghi < c) &&
           ((M.env m.gcoord).hi.all fun hi => decide (c ≤ hi)) &&
           (m.succs.any fun q' =>
            match M.modes[q']? with
            | some m' => decide (m'.gcoord = m.gcoord) &&
                decide (m'.glo ≤ m.ghi) && decide (c ≤ m'.ghi)
            | none => false)))) ||
        -- EXT 4/4b: equilibrium BELOW the band — transit down, over the EXTENDED flex grammar
        (othersFlexC &&
         (decide (c < m.glo) && decide (0 ≤ c) &&
          ((M.env m.gcoord).lo.all fun lo => decide (lo ≤ c)) &&
          (m.succs.any fun q' =>
           match M.modes[q']? with
           | some m' => decide (m'.gcoord = m.gcoord) &&
               decide (m.glo ≤ m'.ghi) && decide (m'.glo ≤ c)
           | none => false))))
   | .contractQ kn kd c =>
       -- rational gain: same 3-way landing as `contract`, but the transit cover uses the
       -- sharper finite-dt cap `ghi + (c − ghi)·(kn/kd)·dt` (sound by `1 − e^{−x} ≤ x`),
       -- stated cross-multiplied by `kd > 0` so it kernel-reduces in ℤ
       othersFlex && decide (0 ≤ kn) && decide (0 < kd) &&
       ((decide (m.glo ≤ c) && decide (c ≤ m.ghi)) ||
        (decide (m.ghi < c) &&
         ((M.env m.gcoord).hi.all fun hi => decide (c ≤ hi)) &&
         (m.succs.any fun q' =>
          match M.modes[q']? with
          | some m' => decide (m'.gcoord = m.gcoord) &&
              decide (m'.glo ≤ m.ghi) &&
              decide (m.ghi * kd + (c - m.ghi) * (kn * dt) ≤ m'.ghi * kd)
          | none => false)) ||
        (decide (c < m.glo) && decide (0 ≤ c) &&
         ((M.env m.gcoord).lo.all fun lo => decide (lo ≤ c)) &&
         (m.succs.any fun q' =>
          match M.modes[q']? with
          | some m' => decide (m'.gcoord = m.gcoord) &&
              decide (m.glo ≤ m'.ghi) &&
              decide (m'.glo * kd ≤ m.glo * kd - (m.glo - c) * (kn * dt))
          | none => false)))
   | .constRate c =>
       -- EXT 1: signed rates — nonneg rates take the flex path with an upper margin;
       -- negative rates (a Return mode) take the frozen path with a LOWER margin
       ((decide (0 ≤ c) && othersFlex &&
         ((M.env m.gcoord).hi.all fun hi => decide (m.ghi + c * dt ≤ hi))) ||
        (decide (c < 0) && othersFrozen &&
         ((M.env m.gcoord).lo.all fun lo => decide (lo ≤ m.glo + c * dt)))) &&
       -- landing: a single self-or-successor band covers the one-step image, OR (EXT 4)
       -- the UNION of the own band with one contiguous successor band covers it
       (((q :: m.succs).any fun q' =>
         match M.modes[q']? with
         | some m' =>
             decide (m'.gcoord = m.gcoord) &&
             decide (m'.glo ≤ m.glo + c * dt) && decide (m.ghi + c * dt ≤ m'.ghi)
         | none => false) ||
        (m.succs.any fun q' =>
         match M.modes[q']? with
         | some m' =>
             decide (m'.gcoord = m.gcoord) &&
             (if 0 ≤ c then
               decide (m'.glo ≤ m.ghi) && decide (m.ghi + c * dt ≤ m'.ghi)
              else
               decide (m.glo ≤ m'.ghi) && decide (m'.glo ≤ m.glo + c * dt))
         | none => false))
   | .driven _ => false
   | .drivenDamp _ _ => false
   | .chase j k =>
       -- EXT G: chase GUARD coordinate — the driver contracts to `c` at the same rate;
       -- staying by `polyExp_le` (single-corner discriminants), landing through the pair
       -- covers (a far band per side holding the staying bound, a near band bridging it
       -- to the own band; self-pairing degenerates to the single-band case)
       !decide (j = m.gcoord) && decide (0 < k) && othersFlexC &&
       (match m.shapes j, (M.env j).lo, (M.env j).hi with
        | CoordShape.contract k2 c, some ulo, some uhi =>
            decide (k2 = k) &&
            ((q :: m.succs).any fun q1 =>
              match M.modes[q1]? with
              | some m1 =>
                  decide (m1.gcoord = m.gcoord) && decide (m1.glo ≤ m.glo) &&
                  decide (0 ≤ m1.glo) && decide (k * m1.glo ≤ c) &&
                  ((M.env m.gcoord).lo.all fun lo => decide (lo ≤ m1.glo)) &&
                  (decide (k * m1.glo ≤ ulo) ||
                   decide ((ulo - k * m1.glo)^2
                     ≤ 2 * (c - k * m1.glo) * (k * m.glo - k * m1.glo))) &&
                  ((q :: m.succs).any fun q2 =>
                    match M.modes[q2]? with
                    | some m2 => decide (m2.gcoord = m.gcoord) &&
                        decide (m2.glo ≤ m1.ghi) && decide (m.glo ≤ m2.ghi)
                    | none => false)
              | none => false) &&
            ((q :: m.succs).any fun q3 =>
              match M.modes[q3]? with
              | some m3 =>
                  decide (m3.gcoord = m.gcoord) && decide (m.ghi ≤ m3.ghi) &&
                  decide (c ≤ k * m3.ghi) &&
                  ((M.env m.gcoord).hi.all fun hi => decide (m3.ghi ≤ hi)) &&
                  (decide (uhi ≤ k * m3.ghi) ||
                   decide ((k * m3.ghi - uhi)^2
                     ≤ 2 * (k * m3.ghi - c) * (k * m3.ghi - k * m.ghi))) &&
                  ((q :: m.succs).any fun q4 =>
                    match M.modes[q4]? with
                    | some m4 => decide (m4.gcoord = m.gcoord) &&
                        decide (m4.glo ≤ m.ghi) && decide (m3.glo ≤ m4.ghi)
                    | none => false)
              | none => false)
        | _, _, _ => false)
   | .pairSym j c h =>
       -- weakly coupled symmetric pair (EXT P): the partner mirrors the shape; the eleven
       -- rational conditions of `PairConds` bound both members' two-exponentials against
       -- the landing target TT (own band top, or a covering successor's) and the envelopes
       !decide (j = m.gcoord) &&
       decide (m.shapes j = CoordShape.pairSym m.gcoord c h) &&
       decide (0 < h) && decide (3 * h ≤ 1000) && decide (0 ≤ m.glo) &&
       (match (M.env m.gcoord).lo, (M.env m.gcoord).hi,
              (M.env j).lo, (M.env j).hi with
        | some plo, some phi, some qlo, some qhi =>
            decide (0 ≤ qlo) &&
            ((List.finRange n).all fun i =>
              decide (i = m.gcoord) || decide (i = j) ||
              decide (m.shapes i = CoordShape.frozen) ||
              ((decide (m.shapes i = CoordShape.driven m.gcoord) ||
                decide (m.shapes i = CoordShape.driven j)) &&
                decide ((M.env i).lo = none) && decide ((M.env i).hi = none)) ||
              (match m.shapes i with
               | CoordShape.contractQ kn kd cc =>
                   decide (0 ≤ kn) && decide (0 < kd) &&
                   ((M.env i).lo.all fun lo => decide (lo ≤ cc)) &&
                   ((M.env i).hi.all fun hi => decide (cc ≤ hi))
               | CoordShape.driven j2 =>
                   !decide (j2 = m.gcoord) && !decide (j2 = j) &&
                   (match m.shapes j2 with
                    | CoordShape.contractQ _ kd _ => decide (0 < kd)
                    | _ => false) &&
                   decide ((M.env i).lo = none) && decide ((M.env i).hi = none)
               | _ => false)) &&
            m.succs.all (fun q' => decide (q' < M.modes.length)) &&
            (pairCondsB m.glo m.ghi plo phi qlo qhi c h m.ghi ||
             (m.succs.any fun q' =>
               match M.modes[q']? with
               | some m' => decide (m'.gcoord = m.gcoord) && decide (m'.glo ≤ m.ghi) &&
                   pairCondsB m.glo m.ghi plo phi qlo qhi c h m'.ghi
               | none => false))
        | _, _, _, _ => false)
   | .riccati b a =>
       -- quadratic drag: equilibrium √(10⁶b/a) inside the band ⟹ the hull of base and
       -- equilibrium self-lands; only frozen others (the class is one-coordinate)
       othersFrozen &&
       decide (0 < b) && decide (0 < a) && decide (0 ≤ m.glo) &&
       decide (m.glo^2 * a ≤ 1000000 * b) && decide (1000000 * b ≤ m.ghi^2 * a))

/-- **The well-formedness checker.** Decidable; no Z3, no ODE reasoning. -/
def decideWellFormed (M : SettlingModel n) : Bool :=
  decide (0 ≤ M.dtQ) &&
  ((List.finRange n).all fun i => bandOrdered (M.env i)) &&
  (List.range M.modes.length).all (fun q =>
    match M.modes[q]? with
    | some m => checkMode M q m
    | none => false)

/-! ## The transcription: settling model → the proof objects -/

/-- The field term of one coordinate shape. -/
noncomputable def CoordShape.field (i : Fin n) : CoordShape n → Term (Var n)
  | .frozen => Term.const 0
  | .constRate c => Term.const (c : ℝ)
  | .contract k c =>
      Term.binop AOp.mul (Term.const (k : ℝ))
        (Term.binop AOp.sub (Term.const (c : ℝ)) (Term.var (Rv i)))
  | .contractQ kn kd c =>
      Term.binop AOp.mul (Term.const ((kn : ℝ) / (kd : ℝ)))
        (Term.binop AOp.sub (Term.const (c : ℝ)) (Term.var (Rv i)))
  | .driven j => Term.var (Rv j)
  | .drivenDamp j dampers =>
      Term.binop AOp.mul (Term.var (Rv j))
        (dampers.foldr (fun d acc =>
          Term.binop AOp.sub acc
            (Term.binop AOp.mul (Term.const ((d.2.1 : ℝ) / (d.2.2 : ℝ)))
              (Term.binop AOp.mul (Term.var (Rv d.1)) (Term.var (Rv d.1)))))
          (Term.const 1))
  | .riccati b a =>
      Term.binop AOp.sub (Term.const (b : ℝ))
        (Term.binop AOp.mul (Term.const ((a : ℝ) / 1000000))
          (Term.binop AOp.mul (Term.var (Rv i)) (Term.var (Rv i))))
  | .pairSym j c h =>
      Term.binop AOp.add
        (Term.binop AOp.sub (Term.const (c : ℝ)) (Term.var (Rv i)))
        (Term.binop AOp.mul (Term.const ((h : ℝ) / 1000)) (Term.var (Rv j)))
  | .chase j k =>
      Term.binop AOp.sub (Term.var (Rv j))
        (Term.binop AOp.mul (Term.const (k : ℝ)) (Term.var (Rv i)))

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
  GuardSettlingH M.graph M.GdOf mv g (Term.const 1) tg (M.dt : ℝ) fL M.envF

/-! ## The phased proof plan — phases A′/B/C PROVEN below; D scoped

STATUS: `wellformed_sound` is PROVEN for shapes {frozen, constRate, contract, driven-by-active}
— i.e. phases A′ (single-active-coordinate), B (driven-by-const integrators, the rover class)
and C (driven-by-contract integrators, the terrain/endurance class) are complete, with the
watertank-shaped instance checker-accepted by kernel `rfl` at the bottom. Phase D (coupled
fields, e.g. attitude_rate's `p' = 1 − p + 0.05q`) is scoped but NOT built: its invariance half
can ride the cut channel's Z3 route, but `GuardSettlingB` also demands flow EXISTENCE, which for
coupled shapes has no closed-form witness — it needs the `PicardBridge` machinery generalized,
a genuinely separate build. Until then coupled modes fail the checker and their hypothesis is
carried (honest classification, not a gap).

Original plan (kept for the record):

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

/-! ## Phase A′ — the proof: `wellformed_sound` for the phase-A fragment -/

/-- Real-side band membership. -/
def Band.memR (b : Band) (x : ℝ) : Prop :=
  (match b.lo with | some l => ((l : ℝ) ≤ x) | none => True) ∧
  (match b.hi with | some h => (x ≤ (h : ℝ)) | none => True)

theorem sat_band_formula {i : Fin n} {b : Band} {μ : State (Var n)} :
    Formula.sat (Band.formula i b) μ ↔ b.memR (μ (Rv i)) := by
  unfold Band.formula Band.memR
  cases b.lo <;> cases b.hi <;>
    simp [Formula.sat, CompOp.interp, Term.eval]

theorem sat_bandFold {env : Fin n → Band} {μ : State (Var n)} (l : List (Fin n)) :
    Formula.sat (l.foldr (fun i acc => Formula.and (Band.formula i (env i)) acc) Formula.tt) μ
      ↔ ∀ i ∈ l, (env i).memR (μ (Rv i)) := by
  induction l with
  | nil => simp [Formula.sat]
  | cons a t ih =>
      simp only [List.foldr_cons, Formula.sat, List.mem_cons]
      rw [sat_band_formula, ih]
      constructor
      · rintro ⟨h1, h2⟩ i (rfl | hi)
        · exact h1
        · exact h2 i hi
      · intro h
        exact ⟨h a (Or.inl rfl), fun i hi => h i (Or.inr hi)⟩

/-- **Reflection**: envelope satisfaction is per-coordinate band membership. -/
theorem sat_envF {M : SettlingModel n} {μ : State (Var n)} :
    Formula.sat M.envF μ ↔ ∀ i, (M.env i).memR (μ (Rv i)) := by
  unfold SettlingModel.envF
  rw [sat_bandFold]
  exact ⟨fun h i => h i (List.mem_finRange i), fun h i _ => h i⟩

theorem sat_GdOf {M : SettlingModel n} {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m) {μ : State (Var n)} :
    Formula.sat (M.GdOf q) μ ↔
      Formula.sat M.envF μ ∧ (m.glo : ℝ) ≤ μ (Rv m.gcoord) ∧ μ (Rv m.gcoord) ≤ (m.ghi : ℝ) := by
  unfold SettlingModel.GdOf
  rw [hq]
  simp [bandDom, Formula.sat, CompOp.interp, Term.eval]

/-- The transcription of one settling mode into the graph's `RMode`. -/
noncomputable def SettlingMode.toRMode (M : SettlingModel n) (m : SettlingMode n) : RMode (Var n) :=
  { sys := rightBlock m.fieldOf (Term.const 1), dom := M.envF, weight := 1 }

theorem graph_modeAt (M : SettlingModel n) (q : ℕ) :
    M.graph.modeAt q = (M.modes[q]?).map (SettlingMode.toRMode M) := by
  unfold SettlingModel.graph SearchGraph.modeAt SettlingMode.toRMode
  simp [List.getElem?_map]

/-- Every edge of a settling graph is unpruned, ⊤-guarded, and its source names its block. -/
theorem graph_edges_shape (M : SettlingModel n) {e : REdge (Var n)}
    (he : e ∈ M.graph.edges) :
    e.guard = Formula.tt ∧ e.pruned = false ∧
      ∃ m, M.modes[e.src]? = some m ∧ (e.tgt = e.src ∨ e.tgt ∈ m.succs) := by
  unfold SettlingModel.graph at he
  simp only [List.mem_flatMap, List.mem_range] at he
  obtain ⟨q, -, he⟩ := he
  rcases hq : M.modes[q]? with _ | m
  · rw [hq] at he; simp at he
  · rw [hq] at he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨rfl, rfl, m, hq, Or.inl rfl⟩
    · obtain ⟨q', hq', rfl⟩ := List.mem_map.mp he
      exact ⟨rfl, rfl, m, hq, Or.inr hq'⟩

/-- The self edge is declared. -/
theorem self_edge_mem (M : SettlingModel n) {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m) :
    ({ src := q, tgt := q, guard := Formula.tt, pruned := false } : REdge (Var n))
      ∈ M.graph.edgesFrom q := by
  unfold SearchGraph.edgesFrom SettlingModel.graph
  rw [List.mem_filter]
  refine ⟨?_, by simp⟩
  simp only [List.mem_flatMap, List.mem_range]
  refine ⟨q, ?_, ?_⟩
  · exact (List.getElem?_eq_some_iff.mp hq).1
  · rw [hq]; exact List.mem_cons_self ..

/-- Each declared successor's edge is declared. -/
theorem succ_edge_mem (M : SettlingModel n) {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m) {q' : ℕ} (hq' : q' ∈ m.succs) :
    ({ src := q, tgt := q', guard := Formula.tt, pruned := false } : REdge (Var n))
      ∈ M.graph.edgesFrom q := by
  unfold SearchGraph.edgesFrom SettlingModel.graph
  rw [List.mem_filter]
  refine ⟨?_, by simp⟩
  simp only [List.mem_flatMap, List.mem_range]
  refine ⟨q, ?_, ?_⟩
  · exact (List.getElem?_eq_some_iff.mp hq).1
  · rw [hq]
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem hq')

/-- Retained successors of a settling graph node are the self index plus edge targets, each
with a declared ⊤-guarded edge. -/
theorem retainedSucc_edges (M : SettlingModel n) {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m)
    (hsucclen : ∀ q' ∈ m.succs, q' < M.modes.length) :
    ∀ q' ∈ M.graph.retainedSucc q,
      ∃ e ∈ M.graph.edgesFrom q, e.tgt = q' ∧ e.guard = Formula.tt ∧
        e.tgt < M.graph.modes.length := by
  have hlen : M.graph.modes.length = M.modes.length := by
    unfold SettlingModel.graph; simp
  intro q' hq'
  unfold SearchGraph.retainedSucc at hq'
  rcases List.mem_cons.mp hq' with rfl | hq'
  · refine ⟨_, self_edge_mem M hq, rfl, rfl, ?_⟩
    rw [hlen]; exact (List.getElem?_eq_some_iff.mp hq).1
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq'
    rw [List.mem_filter] at he
    obtain ⟨he, hsrc⟩ := he
    have hsrcq : e.src = q := by
      have := Bool.and_eq_true .. |>.mp hsrc
      exact of_decide_eq_true this.1
    obtain ⟨htt, -, m2, hm2, htgt⟩ := graph_edges_shape M he
    rw [hsrcq] at hm2
    have hm2' : m2 = m := by rw [hq] at hm2; exact (Option.some.injEq ..).mp hm2.symm
    refine ⟨e, ?_, rfl, htt, ?_⟩
    · unfold SearchGraph.edgesFrom
      rw [List.mem_filter]
      exact ⟨he, by simp [hsrcq]⟩
    · rw [hlen]
      rcases htgt with h | h
      · rw [h, hsrcq]; exact (List.getElem?_eq_some_iff.mp hq).1
      · exact hsucclen e.tgt (hm2' ▸ h)

/-- Every valid index of a settling graph has a mode. -/
theorem graph_modeAll (M : SettlingModel n) :
    ∀ q', q' < M.graph.modes.length → ∃ m', M.graph.modeAt q' = some m' := by
  intro q' hq'
  unfold SearchGraph.modeAt
  exact ⟨_, List.getElem?_eq_getElem hq'⟩

/-! ### The per-mode discharge: `checkMode = true → GuardSettlingB` -/

/-- Non-active coordinates are frozen ⟹ their field terms are `const 0`. -/
theorem frozen_field {m : SettlingMode n} {i : Fin n} (h : m.shapes i = CoordShape.frozen) :
    m.fieldOf i = Term.const 0 := by
  unfold SettlingMode.fieldOf
  rw [h]; rfl

/-- Envelope preservation for a single-active-coordinate update: if the base satisfies the
envelope and only coordinate `j`'s value changes — to a value still inside `j`'s band — the
result satisfies the envelope. -/
theorem envF_update {M : SettlingModel n} {base ν : State (Var n)} {j : Fin n}
    (hbase : Formula.sat M.envF base)
    (hoth : ∀ x, x ≠ Rv j → ν x = base x)
    (hj : (M.env j).memR (ν (Rv j))) :
    Formula.sat M.envF ν := by
  rw [sat_envF] at hbase ⊢
  intro i
  by_cases hij : i = j
  · subst hij; exact hj
  · rw [hoth (Rv i) (by simpa [Rv, Prod.ext_iff] using hij)]
    exact hbase i

/-- A declared successor index is a retained successor in the settling graph. -/
theorem succ_mem_retained (M : SettlingModel n) {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m) {q' : ℕ} (hq' : q' ∈ m.succs) :
    q' ∈ M.graph.retainedSucc q := by
  unfold SearchGraph.retainedSucc
  refine List.mem_cons_of_mem _ ?_
  refine List.mem_map.mpr ⟨{ src := q, tgt := q', guard := Formula.tt, pruned := false }, ?_, rfl⟩
  rw [List.mem_filter]
  have := succ_edge_mem M hq hq'
  unfold SearchGraph.edgesFrom at this
  rw [List.mem_filter] at this
  exact ⟨this.1, by simp⟩

/-! ### Per-shape discharges (real-parameter mirrors of `GuardThreaded`'s, envelope-aware) -/

/-- FROZEN active coordinate: the constant witness — holds, self-lands. -/
theorem settling_frozen (M : SettlingModel n) {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m)
    (hsh : m.shapes m.gcoord = CoordShape.frozen)
    (hfr : ∀ i, i ≠ m.gcoord → m.shapes i = CoordShape.frozen)
    (_hdt : (0 : ℝ) ≤ (M.dt : ℝ)) :
    GuardSettlingB M.graph M.GdOf m.fieldOf (Term.const 1) M.envF ((M.dt : ℝ)) q := by
  intro base hb
  refine ⟨fun _ => base, rfl, ?_, ?_, ?_, q, List.mem_cons_self .., hb⟩
  · -- all fields are const 0 (every coordinate frozen)
    intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    have hfz : m.shapes i = CoordShape.frozen := by
      by_cases hij : i = m.gcoord
      · rw [hij]; exact hsh
      · exact hfr i hij
    have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i)) base = 0 := by
      simp [SettlingMode.fieldOf, hfz, CoordShape.field, Term.eval, AOp.interp]
    rw [heval]
    exact hasDerivWithinAt_const t _ _
  · intro t ht x hx; rfl
  · intro t ht
    exact ((sat_GdOf hq).mp hb).1

/-- CONTRACT active coordinate with the equilibrium inside the mode's own band: the
exponential witness — stays between base and equilibrium, self-lands (tangent included). -/
theorem settling_contract (M : SettlingModel n) {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m) {k c : ℤ}
    (hsh : m.shapes m.gcoord = CoordShape.contract k c)
    (hfr : ∀ i, i ≠ m.gcoord → m.shapes i = CoordShape.frozen)
    (hk : 0 ≤ k) (hcl : m.glo ≤ c) (hch : c ≤ m.ghi)
    (hloIn : ∀ l', (M.env m.gcoord).lo = some l' → l' ≤ m.glo)
    (hhiIn : ∀ h', (M.env m.gcoord).hi = some h' → m.ghi ≤ h')
    (hdt : (0 : ℝ) ≤ (M.dt : ℝ)) :
    GuardSettlingB M.graph M.GdOf m.fieldOf (Term.const 1) M.envF ((M.dt : ℝ)) q := by
  intro base hb
  obtain ⟨henv, hblo, hbhi⟩ := (sat_GdOf hq).mp hb
  have hkR0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hclR : (m.glo : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcl
  have hchR : (c : ℝ) ≤ (m.ghi : ℝ) := by exact_mod_cast hch
  -- the flow stays in the guard band for all t ≥ 0
  have hband : ∀ t, 0 ≤ t → (m.glo : ℝ) ≤ contractΦ m.gcoord (k : ℝ) (c : ℝ) base t (Rv m.gcoord)
      ∧ contractΦ m.gcoord (k : ℝ) (c : ℝ) base t (Rv m.gcoord) ≤ (m.ghi : ℝ) := by
    intro t ht
    have hθpos : 0 < Real.exp (-((k : ℝ) * t)) := Real.exp_pos _
    have hθle : Real.exp (-((k : ℝ) * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    rw [contractΦ_Rvj]
    constructor
    · rcases le_or_gt (c : ℝ) (base (Rv m.gcoord)) with hbc | hbc
      · nlinarith
      · nlinarith
    · rcases le_or_gt (c : ℝ) (base (Rv m.gcoord)) with hbc | hbc
      · nlinarith
      · nlinarith
  have hstayGd : ∀ t, 0 ≤ t →
      Formula.sat (M.GdOf q) (contractΦ m.gcoord (k : ℝ) (c : ℝ) base t) := by
    intro t ht
    rw [sat_GdOf hq]
    obtain ⟨h1, h2⟩ := hband t ht
    refine ⟨?_, h1, h2⟩
    refine envF_update henv
      (fun x hx => contractΦ_other m.gcoord (k : ℝ) (c : ℝ) base t hx) ?_
    unfold Band.memR
    constructor
    · cases hcase : (M.env m.gcoord).lo with
      | none => trivial
      | some l =>
          have hlG : (l : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hloIn l hcase
          linarith
    · cases hcase : (M.env m.gcoord).hi with
      | none => trivial
      | some h =>
          have hhG : (m.ghi : ℝ) ≤ (h : ℝ) := by exact_mod_cast hhiIn h hcase
          linarith
  refine ⟨contractΦ m.gcoord (k : ℝ) (c : ℝ) base, ?_, ?_, ?_, ?_, q,
    List.mem_cons_self .., hstayGd _ hdt⟩
  · funext x
    by_cases hx : x = Rv m.gcoord
    · subst hx; simp [contractΦ]
    · exact contractΦ_other m.gcoord (k : ℝ) (c : ℝ) base 0 hx
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hij : i = m.gcoord
    · subst hij
      have hd := (contractΦ_hasDeriv m.gcoord (k : ℝ) (c : ℝ) base t).hasDerivWithinAt
        (s := Icc 0 (M.dt : ℝ))
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf m.gcoord))
          (contractΦ m.gcoord (k : ℝ) (c : ℝ) base t)
          = (k : ℝ) * ((c : ℝ) - contractΦ m.gcoord (k : ℝ) (c : ℝ) base t (Rv m.gcoord)) := by
        simp [SettlingMode.fieldOf, hsh, CoordShape.field, Term.eval, AOp.interp]
      rw [heval]
      exact hd
    · have hfz : m.shapes i = CoordShape.frozen := hfr i hij
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
          (contractΦ m.gcoord (k : ℝ) (c : ℝ) base t) = 0 := by
        simp [SettlingMode.fieldOf, hfz, CoordShape.field, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => contractΦ m.gcoord (k : ℝ) (c : ℝ) base u (Rv i))
          = fun _ => base (Rv i) := by
        funext u
        exact contractΦ_other m.gcoord (k : ℝ) (c : ℝ) base u
          (fun hc' => hij (by simpa [Rv, Prod.ext_iff] using hc'))
      rw [hcurve]
      exact hasDerivWithinAt_const t _ _
  · intro t ht x hx
    have hxj : x ≠ Rv m.gcoord := by
      intro hcx; subst hcx
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map]
        exact List.mem_map.mpr ⟨m.gcoord, List.mem_finRange m.gcoord, rfl⟩)
    exact contractΦ_other m.gcoord (k : ℝ) (c : ℝ) base t hxj
  · intro t ht
    exact ((sat_GdOf hq).mp (hstayGd t ht.1)).1

/-- CONST-RATE active coordinate with margin and a covering self-or-successor band: the
affine witness — stays by the margin, lands in the covering band. -/
theorem settling_const (M : SettlingModel n) {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m) {c : ℤ}
    (hsh : m.shapes m.gcoord = CoordShape.constRate c)
    (hfr : ∀ i, i ≠ m.gcoord → m.shapes i = CoordShape.frozen)
    (hc : 0 ≤ c)
    (hloIn : ∀ l', (M.env m.gcoord).lo = some l' → l' ≤ m.glo)
    (hmargin : ∀ h', (M.env m.gcoord).hi = some h' → m.ghi + c * M.dt ≤ h')
    (hland : (∃ q' ∈ q :: m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
        m'.glo ≤ m.glo + c * M.dt ∧ m.ghi + c * M.dt ≤ m'.ghi) ∨
      (∃ q' ∈ m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
        m'.glo ≤ m.ghi ∧ m.ghi + c * M.dt ≤ m'.ghi))
    (hdt : (0 : ℝ) ≤ (M.dt : ℝ)) :
    GuardSettlingB M.graph M.GdOf m.fieldOf (Term.const 1) M.envF ((M.dt : ℝ)) q := by
  intro base hb
  obtain ⟨henv, hblo, hbhi⟩ := (sat_GdOf hq).mp hb
  have hcR0 : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hstayEnv : ∀ t, 0 ≤ t → t ≤ (M.dt : ℝ) →
      Formula.sat M.envF (affineΦ m.gcoord (c : ℝ) base t) := by
    intro t ht htd
    have hct0 : 0 ≤ (c : ℝ) * t := mul_nonneg hcR0 ht
    have hctd : (c : ℝ) * t ≤ (c : ℝ) * (M.dt : ℝ) := mul_le_mul_of_nonneg_left htd hcR0
    refine envF_update henv (fun x hx => affineΦ_other m.gcoord (c : ℝ) base t hx) ?_
    unfold Band.memR
    constructor
    · cases hcase : (M.env m.gcoord).lo with
      | none => trivial
      | some l =>
          have hlG : (l : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hloIn l hcase
          show (l : ℝ) ≤ affineΦ m.gcoord (c : ℝ) base t (Rv m.gcoord)
          simp [affineΦ]
          linarith
    · cases hcase : (M.env m.gcoord).hi with
      | none => trivial
      | some h =>
          have hmR : (m.ghi : ℝ) + (c : ℝ) * (M.dt : ℝ) ≤ (h : ℝ) := by
            exact_mod_cast hmargin h hcase
          show affineΦ m.gcoord (c : ℝ) base t (Rv m.gcoord) ≤ (h : ℝ)
          simp [affineΦ]
          linarith
  have hpick : ∃ q' ∈ q :: M.graph.retainedSucc q, ∃ m', M.modes[q']? = some m' ∧
      m'.gcoord = m.gcoord ∧
      (m'.glo : ℝ) ≤ base (Rv m.gcoord) + (c : ℝ) * (M.dt : ℝ) ∧
      base (Rv m.gcoord) + (c : ℝ) * (M.dt : ℝ) ≤ (m'.ghi : ℝ) := by
    have hcd0 : 0 ≤ (c : ℝ) * (M.dt : ℝ) := mul_nonneg hcR0 hdt
    rcases hland with ⟨q', hq'mem, m', hm', hgc', hcov1, hcov2⟩ | ⟨q', hq'mem, m', hm', hgc', hcv1, hcv2⟩
    · have h1 : (m'.glo : ℝ) ≤ (m.glo : ℝ) + (c : ℝ) * (M.dt : ℝ) := by exact_mod_cast hcov1
      have h2 : (m.ghi : ℝ) + (c : ℝ) * (M.dt : ℝ) ≤ (m'.ghi : ℝ) := by exact_mod_cast hcov2
      refine ⟨q', ?_, m', hm', hgc', by linarith, by linarith⟩
      rcases List.mem_cons.mp hq'mem with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (succ_mem_retained M hq h)
    · have h1 : (m'.glo : ℝ) ≤ (m.ghi : ℝ) := by exact_mod_cast hcv1
      have h2 : (m.ghi : ℝ) + (c : ℝ) * (M.dt : ℝ) ≤ (m'.ghi : ℝ) := by exact_mod_cast hcv2
      rcases le_or_gt (base (Rv m.gcoord) + (c : ℝ) * (M.dt : ℝ)) (m.ghi : ℝ) with he | he
      · exact ⟨q, List.mem_cons_self .., m, hq, rfl, by linarith, he⟩
      · exact ⟨q', List.mem_cons_of_mem _ (succ_mem_retained M hq hq'mem), m', hm', hgc',
          by linarith, by linarith⟩
  obtain ⟨q', hq'ret, m', hm', hgc', hcov1R, hcov2R⟩ := hpick
  refine ⟨affineΦ m.gcoord (c : ℝ) base, ?_, ?_, ?_,
    fun t ht => hstayEnv t ht.1 ht.2, q', hq'ret, ?_⟩
  · funext x
    by_cases hx : x = Rv m.gcoord
    · subst hx; simp [affineΦ]
    · exact affineΦ_other m.gcoord (c : ℝ) base 0 hx
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hij : i = m.gcoord
    · subst hij
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf m.gcoord))
          (affineΦ m.gcoord (c : ℝ) base t) = (c : ℝ) := by
        simp [SettlingMode.fieldOf, hsh, CoordShape.field, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => affineΦ m.gcoord (c : ℝ) base u (Rv m.gcoord))
          = fun u => base (Rv m.gcoord) + (c : ℝ) * u := by
        funext u; simp [affineΦ]
      rw [hcurve]
      have h := ((hasDerivAt_id t).const_mul (c : ℝ)).const_add (base (Rv m.gcoord))
      simp only [id, mul_one] at h
      exact h.hasDerivWithinAt
    · have hfz : m.shapes i = CoordShape.frozen := hfr i hij
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
          (affineΦ m.gcoord (c : ℝ) base t) = 0 := by
        simp [SettlingMode.fieldOf, hfz, CoordShape.field, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => affineΦ m.gcoord (c : ℝ) base u (Rv i))
          = fun _ => base (Rv i) := by
        funext u
        exact affineΦ_other m.gcoord (c : ℝ) base u
          (fun hc' => hij (by simpa [Rv, Prod.ext_iff] using hc'))
      rw [hcurve]
      exact hasDerivWithinAt_const t _ _
  · intro t ht x hx
    have hxj : x ≠ Rv m.gcoord := by
      intro hcx; subst hcx
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map]
        exact List.mem_map.mpr ⟨m.gcoord, List.mem_finRange m.gcoord, rfl⟩)
    exact affineΦ_other m.gcoord (c : ℝ) base t hxj
  · rw [sat_GdOf hm']
    refine ⟨hstayEnv _ hdt le_rfl, ?_, ?_⟩
    · rw [hgc']
      show (m'.glo : ℝ) ≤ affineΦ m.gcoord (c : ℝ) base (M.dt : ℝ) (Rv m.gcoord)
      simp [affineΦ]
      have : 0 ≤ (c : ℝ) * (M.dt : ℝ) := mul_nonneg hcR0 hdt
      linarith
    · rw [hgc']
      show affineΦ m.gcoord (c : ℝ) base (M.dt : ℝ) (Rv m.gcoord) ≤ (m'.ghi : ℝ)
      simp [affineΦ]
      linarith

/-! ### Phase B — the driven-by-const integrator witness -/

/-- Per-coordinate value of the phase-B witness: the active coordinate moves affinely, a
driven coordinate quadratically (integrating the active one), everything else frozen. -/
noncomputable def drivenVal (m : SettlingMode n) (cR : ℝ) (base : State (Var n)) (t : ℝ)
    (i : Fin n) : ℝ :=
  if i = m.gcoord then base (Rv i) + cR * t
  else match m.shapes i with
    | CoordShape.driven j =>
        if j = m.gcoord then base (Rv i) + base (Rv m.gcoord) * t + cR / 2 * t ^ 2
        else base (Rv i) + base (Rv j) * t
    | _ => base (Rv i)

/-- The phase-B witness flow. -/
noncomputable def drivenΦ (m : SettlingMode n) (cR : ℝ) (base : State (Var n)) (t : ℝ) :
    State (Var n) :=
  fun x => match x with
    | (Side.R, i) => drivenVal m cR base t i
    | _ => base x

@[simp] theorem drivenΦ_Rv (m : SettlingMode n) (cR : ℝ) (base : State (Var n)) (t : ℝ)
    (i : Fin n) : drivenΦ m cR base t (Rv i) = drivenVal m cR base t i := rfl

theorem drivenΦ_nonR (m : SettlingMode n) (cR : ℝ) (base : State (Var n)) (t : ℝ)
    {x : Var n} (hx : ∀ i : Fin n, x ≠ Rv i) : drivenΦ m cR base t x = base x := by
  obtain ⟨sd, ix⟩ := x
  cases sd with
  | R => exact absurd rfl (hx ix)
  | L => rfl
  | Aux => rfl

theorem drivenVal_frozen {m : SettlingMode n} {cR : ℝ} {base : State (Var n)} {t : ℝ}
    {i : Fin n} (hig : i ≠ m.gcoord) (hfz : m.shapes i = CoordShape.frozen) :
    drivenVal m cR base t i = base (Rv i) := by
  simp [drivenVal, hig, hfz]

theorem drivenVal_dactive {m : SettlingMode n} {cR : ℝ} {base : State (Var n)} {t : ℝ}
    {i : Fin n} (hig : i ≠ m.gcoord) (hdr : m.shapes i = CoordShape.driven m.gcoord) :
    drivenVal m cR base t i = base (Rv i) + base (Rv m.gcoord) * t + cR / 2 * t ^ 2 := by
  simp [drivenVal, hig, hdr]

theorem drivenVal_dfrozen {m : SettlingMode n} {cR : ℝ} {base : State (Var n)} {t : ℝ}
    {i j : Fin n} (hig : i ≠ m.gcoord) (hdr : m.shapes i = CoordShape.driven j)
    (hjne : j ≠ m.gcoord) :
    drivenVal m cR base t i = base (Rv i) + base (Rv j) * t := by
  simp [drivenVal, hig, hdr, hjne]

/-- The flexible non-active-coordinate condition (EXT 2 included): frozen, driven by the
active coordinate (no upper wall), or driven by a non-active FROZEN coordinate (envelope-free). -/
def FlexOthers (M : SettlingModel n) (m : SettlingMode n) : Prop :=
  ∀ i, i ≠ m.gcoord → m.shapes i = CoordShape.frozen ∨
    (m.shapes i = CoordShape.driven m.gcoord ∧ (M.env i).hi = none) ∨
    (∃ j, m.shapes i = CoordShape.driven j ∧ j ≠ m.gcoord ∧
      m.shapes j = CoordShape.frozen ∧ (M.env i).lo = none ∧ (M.env i).hi = none)

/-- CONST-RATE active coordinate, others frozen OR driven by it (integrators with no upper
envelope wall and a nonneg driving band): the affine/quadratic product witness. -/
theorem settling_const_driven (M : SettlingModel n) {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m) {c : ℤ}
    (hsh : m.shapes m.gcoord = CoordShape.constRate c)
    (hflex : FlexOthers M m)
    (hglo0 : 0 ≤ m.glo) (hc : 0 ≤ c)
    (hloIn : ∀ l', (M.env m.gcoord).lo = some l' → l' ≤ m.glo)
    (hmargin : ∀ h', (M.env m.gcoord).hi = some h' → m.ghi + c * M.dt ≤ h')
    (hland : (∃ q' ∈ q :: m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
        m'.glo ≤ m.glo + c * M.dt ∧ m.ghi + c * M.dt ≤ m'.ghi) ∨
      (∃ q' ∈ m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
        m'.glo ≤ m.ghi ∧ m.ghi + c * M.dt ≤ m'.ghi))
    (hdt : (0 : ℝ) ≤ (M.dt : ℝ)) :
    GuardSettlingB M.graph M.GdOf m.fieldOf (Term.const 1) M.envF ((M.dt : ℝ)) q := by
  intro base hb
  obtain ⟨henv, hblo, hbhi⟩ := (sat_GdOf hq).mp hb
  have hcR0 : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hglo0R : (0 : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hglo0
  have hbg0 : (0 : ℝ) ≤ base (Rv m.gcoord) := le_trans hglo0R hblo
  -- the active coordinate's value along the witness
  have hval_g : ∀ t, drivenVal m (c : ℝ) base t m.gcoord = base (Rv m.gcoord) + (c : ℝ) * t := by
    intro t; unfold drivenVal; rw [if_pos rfl]
  -- staying in the envelope
  have hstayEnv : ∀ t, 0 ≤ t → t ≤ (M.dt : ℝ) →
      Formula.sat M.envF (drivenΦ m (c : ℝ) base t) := by
    intro t ht htd
    have hct0 : 0 ≤ (c : ℝ) * t := mul_nonneg hcR0 ht
    have hctd : (c : ℝ) * t ≤ (c : ℝ) * (M.dt : ℝ) := mul_le_mul_of_nonneg_left htd hcR0
    rw [sat_envF]
    intro i
    rw [drivenΦ_Rv]
    by_cases hig : i = m.gcoord
    · rw [hig, hval_g]
      have hbe := (sat_envF.mp henv) m.gcoord
      unfold Band.memR at hbe ⊢
      rcases hbe with ⟨hbl, hbh⟩
      constructor
      · cases hcase : (M.env m.gcoord).lo with
        | none => trivial
        | some l =>
            have hlG : (l : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hloIn l hcase
            linarith
      · cases hcase : (M.env m.gcoord).hi with
        | none => trivial
        | some h =>
            have hmR : (m.ghi : ℝ) + (c : ℝ) * (M.dt : ℝ) ≤ (h : ℝ) := by
              exact_mod_cast hmargin h hcase
            linarith
    · rcases hflex i hig with hfz | ⟨hdr, hhi⟩ | ⟨j, hdr, hjne, -, hlo, hhi⟩
      · rw [drivenVal_frozen hig hfz]
        exact (sat_envF.mp henv) i
      · rw [drivenVal_dactive hig hdr]
        have hbe := (sat_envF.mp henv) i
        unfold Band.memR at hbe ⊢
        rcases hbe with ⟨hbl, hbh⟩
        have hq2 : 0 ≤ (c : ℝ) / 2 * t ^ 2 := by positivity
        have hbgt : 0 ≤ base (Rv m.gcoord) * t := mul_nonneg hbg0 ht
        constructor
        · cases hcase : (M.env i).lo with
          | none => trivial
          | some l =>
              rw [hcase] at hbl
              show (l : ℝ) ≤ base (Rv i) + base (Rv m.gcoord) * t + (c : ℝ) / 2 * t ^ 2
              linarith
        · rw [hhi]; trivial
      · -- EXT 2: envelope-free coordinate — membership trivial
        unfold Band.memR
        rw [hlo, hhi]
        exact ⟨trivial, trivial⟩
  have hpick : ∃ q' ∈ q :: M.graph.retainedSucc q, ∃ m', M.modes[q']? = some m' ∧
      m'.gcoord = m.gcoord ∧
      (m'.glo : ℝ) ≤ base (Rv m.gcoord) + (c : ℝ) * (M.dt : ℝ) ∧
      base (Rv m.gcoord) + (c : ℝ) * (M.dt : ℝ) ≤ (m'.ghi : ℝ) := by
    have hcd0 : 0 ≤ (c : ℝ) * (M.dt : ℝ) := mul_nonneg hcR0 hdt
    rcases hland with ⟨q', hq'mem, m', hm', hgc', hcov1, hcov2⟩ | ⟨q', hq'mem, m', hm', hgc', hcv1, hcv2⟩
    · have h1 : (m'.glo : ℝ) ≤ (m.glo : ℝ) + (c : ℝ) * (M.dt : ℝ) := by exact_mod_cast hcov1
      have h2 : (m.ghi : ℝ) + (c : ℝ) * (M.dt : ℝ) ≤ (m'.ghi : ℝ) := by exact_mod_cast hcov2
      refine ⟨q', ?_, m', hm', hgc', by linarith, by linarith⟩
      rcases List.mem_cons.mp hq'mem with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (succ_mem_retained M hq h)
    · have h1 : (m'.glo : ℝ) ≤ (m.ghi : ℝ) := by exact_mod_cast hcv1
      have h2 : (m.ghi : ℝ) + (c : ℝ) * (M.dt : ℝ) ≤ (m'.ghi : ℝ) := by exact_mod_cast hcv2
      rcases le_or_gt (base (Rv m.gcoord) + (c : ℝ) * (M.dt : ℝ)) (m.ghi : ℝ) with he | he
      · exact ⟨q, List.mem_cons_self .., m, hq, rfl, by linarith, he⟩
      · exact ⟨q', List.mem_cons_of_mem _ (succ_mem_retained M hq hq'mem), m', hm', hgc',
          by linarith, by linarith⟩
  obtain ⟨q', hq'ret, m', hm', hgc', hcov1R, hcov2R⟩ := hpick
  refine ⟨drivenΦ m (c : ℝ) base, ?_, ?_, ?_,
    fun t ht => hstayEnv t ht.1 ht.2, q', hq'ret, ?_⟩
  · -- t = 0 recovers the base
    funext x
    obtain ⟨sd, ix⟩ := x
    cases sd with
    | R =>
        show drivenVal m (c : ℝ) base 0 ix = base (Rv ix)
        unfold drivenVal
        by_cases hig : ix = m.gcoord
        · rw [if_pos hig]; ring
        · rw [if_neg hig]
          rcases hshx : m.shapes ix with _ | _ | _ | _ <;> simp
    | L => rfl
    | Aux => rfl
  · -- derivatives
    intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hig : i = m.gcoord
    · rw [hig]
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf m.gcoord))
          (drivenΦ m (c : ℝ) base t) = (c : ℝ) := by
        simp [SettlingMode.fieldOf, hsh, CoordShape.field, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => drivenΦ m (c : ℝ) base u (Rv m.gcoord))
          = fun u => base (Rv m.gcoord) + (c : ℝ) * u := by
        funext u; rw [drivenΦ_Rv, hval_g]
      rw [hcurve]
      have h := ((hasDerivAt_id t).const_mul (c : ℝ)).const_add (base (Rv m.gcoord))
      simp only [id, mul_one] at h
      exact h.hasDerivWithinAt
    · rcases hflex i hig with hfz | ⟨hdr, -⟩ | ⟨j, hdr, hjne, hjfz, -, -⟩
      · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦ m (c : ℝ) base t) = 0 := by
          simp [SettlingMode.fieldOf, hfz, CoordShape.field, Term.eval, AOp.interp]
        rw [heval]
        have hcurve : (fun u => drivenΦ m (c : ℝ) base u (Rv i))
            = fun _ => base (Rv i) := by
          funext u; rw [drivenΦ_Rv, drivenVal_frozen hig hfz]
        rw [hcurve]
        exact hasDerivWithinAt_const t _ _
      · -- driven by the ACTIVE coordinate: quadratic curve
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦ m (c : ℝ) base t)
            = base (Rv m.gcoord) + (c : ℝ) * t := by
          simp [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp,
            drivenΦ_Rv, hval_g]
        rw [heval]
        have hcurve : (fun u => drivenΦ m (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + base (Rv m.gcoord) * u + (c : ℝ) / 2 * u ^ 2 := by
          funext u; rw [drivenΦ_Rv, drivenVal_dactive hig hdr]
        rw [hcurve]
        have h1 : HasDerivAt (fun u : ℝ => base (Rv i) + base (Rv m.gcoord) * u)
            (base (Rv m.gcoord)) t := by
          have h := ((hasDerivAt_id t).const_mul (base (Rv m.gcoord))).const_add (base (Rv i))
          simpa using h
        have h2 : HasDerivAt (fun u : ℝ => (c : ℝ) / 2 * u ^ 2) ((c : ℝ) * t) t := by
          have h := (hasDerivAt_pow 2 t).const_mul ((c : ℝ) / 2)
          have he : (c : ℝ) / 2 * ((2 : ℕ) * t ^ (2 - 1)) = (c : ℝ) * t := by
            push_cast; ring
          rwa [he] at h
        have h := h1.add h2
        exact h.hasDerivWithinAt
      · -- EXT 2: driven by a frozen non-active coordinate — linear curve, constant driver
        have hvalj : drivenΦ m (c : ℝ) base t (Rv j) = base (Rv j) := by
          rw [drivenΦ_Rv, drivenVal_frozen hjne hjfz]
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦ m (c : ℝ) base t) = base (Rv j) := by
          simp only [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp]
          rw [hvalj]; ring
        rw [heval]
        have hcurve : (fun u => drivenΦ m (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + base (Rv j) * u := by
          funext u; rw [drivenΦ_Rv, drivenVal_dfrozen hig hdr hjne]
        rw [hcurve]
        have h := ((hasDerivAt_id t).const_mul (base (Rv j))).const_add (base (Rv i))
        simp only [id, mul_one] at h
        exact h.hasDerivWithinAt
  · -- mask
    intro t ht x hx
    refine drivenΦ_nonR m (c : ℝ) base t ?_
    intro i hxi
    exact hx (by
      rw [hxi]
      simp only [rightBlock, ODESystem.bound, List.map_map]
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  · -- landing
    rw [sat_GdOf hm']
    refine ⟨hstayEnv _ hdt le_rfl, ?_, ?_⟩
    · rw [hgc', drivenΦ_Rv, hval_g]
      have : 0 ≤ (c : ℝ) * (M.dt : ℝ) := mul_nonneg hcR0 hdt
      linarith
    · rw [hgc', drivenΦ_Rv, hval_g]
      linarith

/-! ### Phase C — the driven-by-contract integrator witness -/

/-- The integrated exponential `∫₀ᵗ e^{−ku} du` — `(1 − e^{−kt})/k`, degenerating to `t`. -/
noncomputable def expInt (k t : ℝ) : ℝ :=
  if k = 0 then t else (1 - Real.exp (-(k * t))) / k

theorem expInt_hasDeriv (k t : ℝ) :
    HasDerivAt (fun u => expInt k u) (Real.exp (-(k * t))) t := by
  unfold expInt
  by_cases hk : k = 0
  · simp only [hk, if_true, zero_mul, neg_zero, Real.exp_zero]
    exact hasDerivAt_id t
  · simp only [hk, if_false]
    have hinner : HasDerivAt (fun u : ℝ => -(k * u)) (-k) t := by
      have h := (hasDerivAt_id t).const_mul (-k)
      simp only [id, mul_one, neg_mul] at h
      exact h
    have hexp : HasDerivAt (fun u : ℝ => Real.exp (-(k * u))) (-k * Real.exp (-(k * t))) t := by
      have h := (Real.hasDerivAt_exp (-(k * t))).comp t hinner
      simp only [Function.comp_def] at h
      rw [mul_comm (Real.exp (-(k * t))) (-k)] at h
      exact h
    have hsub : HasDerivAt (fun u : ℝ => 1 - Real.exp (-(k * u)))
        (k * Real.exp (-(k * t))) t := by
      have h := hexp.const_sub 1
      simpa using h
    have h := hsub.div_const k
    rwa [mul_comm k (Real.exp (-(k * t))), mul_div_assoc, div_self hk, mul_one] at h

theorem expInt_nonneg {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t) : 0 ≤ expInt k t := by
  unfold expInt
  by_cases hk0 : k = 0
  · simpa [hk0]
  · rw [if_neg hk0]
    have hkpos : 0 < k := lt_of_le_of_ne hk (Ne.symm hk0)
    have : Real.exp (-(k * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    positivity

theorem expInt_le {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t) : expInt k t ≤ t := by
  unfold expInt
  by_cases hk0 : k = 0
  · simp [hk0]
  · rw [if_neg hk0]
    have hkpos : 0 < k := lt_of_le_of_ne hk (Ne.symm hk0)
    rw [div_le_iff₀ hkpos]
    have h := Real.add_one_le_exp (-(k * t))
    have hle : 1 - k * t ≤ Real.exp (-(k * t)) := by linarith
    nlinarith [hle]

/-- Per-coordinate value of the phase-C witness: the active coordinate contracts, a driven
coordinate integrates it, everything else frozen. -/
noncomputable def drivenValC (m : SettlingMode n) (kR cR : ℝ) (base : State (Var n)) (t : ℝ)
    (i : Fin n) : ℝ :=
  if i = m.gcoord then cR + (base (Rv i) - cR) * Real.exp (-(kR * t))
  else match m.shapes i with
    | CoordShape.driven j =>
        if j = m.gcoord then base (Rv i) + cR * t + (base (Rv m.gcoord) - cR) * expInt kR t
        else base (Rv i) + base (Rv j) * t
    | _ => base (Rv i)

/-- The phase-C witness flow. -/
noncomputable def drivenΦC (m : SettlingMode n) (kR cR : ℝ) (base : State (Var n)) (t : ℝ) :
    State (Var n) :=
  fun x => match x with
    | (Side.R, i) => drivenValC m kR cR base t i
    | _ => base x

@[simp] theorem drivenΦC_Rv (m : SettlingMode n) (kR cR : ℝ) (base : State (Var n)) (t : ℝ)
    (i : Fin n) : drivenΦC m kR cR base t (Rv i) = drivenValC m kR cR base t i := rfl

theorem drivenΦC_nonR (m : SettlingMode n) (kR cR : ℝ) (base : State (Var n)) (t : ℝ)
    {x : Var n} (hx : ∀ i : Fin n, x ≠ Rv i) : drivenΦC m kR cR base t x = base x := by
  obtain ⟨sd, ix⟩ := x
  cases sd with
  | R => exact absurd rfl (hx ix)
  | L => rfl
  | Aux => rfl

theorem drivenValC_frozen {m : SettlingMode n} {kR cR : ℝ} {base : State (Var n)} {t : ℝ}
    {i : Fin n} (hig : i ≠ m.gcoord) (hfz : m.shapes i = CoordShape.frozen) :
    drivenValC m kR cR base t i = base (Rv i) := by
  simp [drivenValC, hig, hfz]

theorem drivenValC_dactive {m : SettlingMode n} {kR cR : ℝ} {base : State (Var n)} {t : ℝ}
    {i : Fin n} (hig : i ≠ m.gcoord) (hdr : m.shapes i = CoordShape.driven m.gcoord) :
    drivenValC m kR cR base t i
      = base (Rv i) + cR * t + (base (Rv m.gcoord) - cR) * expInt kR t := by
  simp [drivenValC, hig, hdr]

theorem drivenValC_dfrozen {m : SettlingMode n} {kR cR : ℝ} {base : State (Var n)} {t : ℝ}
    {i j : Fin n} (hig : i ≠ m.gcoord) (hdr : m.shapes i = CoordShape.driven j)
    (hjne : j ≠ m.gcoord) :
    drivenValC m kR cR base t i = base (Rv i) + base (Rv j) * t := by
  simp [drivenValC, hig, hdr, hjne]

/-- CONTRACT active coordinate (equilibrium in its own band), others frozen OR driven by it
(integrators with no upper envelope wall, nonneg band): the exponential/exp-integral witness. -/
theorem settling_contract_driven (M : SettlingModel n) {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m) {k c : ℤ}
    (hsh : m.shapes m.gcoord = CoordShape.contract k c)
    (hflex : FlexOthers M m)
    (hglo0 : 0 ≤ m.glo)
    (hk : 0 ≤ k) (hcl : m.glo ≤ c) (hch : c ≤ m.ghi)
    (hloIn : ∀ l', (M.env m.gcoord).lo = some l' → l' ≤ m.glo)
    (hhiIn : ∀ h', (M.env m.gcoord).hi = some h' → m.ghi ≤ h')
    (hdt : (0 : ℝ) ≤ (M.dt : ℝ)) :
    GuardSettlingB M.graph M.GdOf m.fieldOf (Term.const 1) M.envF ((M.dt : ℝ)) q := by
  intro base hb
  obtain ⟨henv, hblo, hbhi⟩ := (sat_GdOf hq).mp hb
  have hkR0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hclR : (m.glo : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcl
  have hchR : (c : ℝ) ≤ (m.ghi : ℝ) := by exact_mod_cast hch
  have hglo0R : (0 : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hglo0
  -- the active coordinate's value and its band, for all t ≥ 0
  have hval_g : ∀ t, drivenValC m (k : ℝ) (c : ℝ) base t m.gcoord
      = (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * t)) := by
    intro t; unfold drivenValC; rw [if_pos rfl]
  have hband : ∀ t, 0 ≤ t →
      (m.glo : ℝ) ≤ drivenValC m (k : ℝ) (c : ℝ) base t m.gcoord
      ∧ drivenValC m (k : ℝ) (c : ℝ) base t m.gcoord ≤ (m.ghi : ℝ) := by
    intro t ht
    have hθpos : 0 < Real.exp (-((k : ℝ) * t)) := Real.exp_pos _
    have hθle : Real.exp (-((k : ℝ) * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    rw [hval_g]
    constructor
    · rcases le_or_gt (c : ℝ) (base (Rv m.gcoord)) with hbc | hbc
      · nlinarith
      · nlinarith
    · rcases le_or_gt (c : ℝ) (base (Rv m.gcoord)) with hbc | hbc
      · nlinarith
      · nlinarith
  -- staying in the envelope
  have hstayEnv : ∀ t, 0 ≤ t → Formula.sat M.envF (drivenΦC m (k : ℝ) (c : ℝ) base t) := by
    intro t ht
    rw [sat_envF]
    intro i
    rw [drivenΦC_Rv]
    by_cases hig : i = m.gcoord
    · rw [hig]
      obtain ⟨h1, h2⟩ := hband t ht
      unfold Band.memR
      constructor
      · cases hcase : (M.env m.gcoord).lo with
        | none => trivial
        | some l =>
            have hlG : (l : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hloIn l hcase
            linarith
      · cases hcase : (M.env m.gcoord).hi with
        | none => trivial
        | some h =>
            have hhG : (m.ghi : ℝ) ≤ (h : ℝ) := by exact_mod_cast hhiIn h hcase
            linarith
    · rcases hflex i hig with hfz | ⟨hdr, hhi⟩ | ⟨j, hdr, hjne, -, hlo, hhi⟩
      · rw [drivenValC_frozen hig hfz]
        exact (sat_envF.mp henv) i
      · rw [drivenValC_dactive hig hdr]
        have hbe := (sat_envF.mp henv) i
        unfold Band.memR at hbe ⊢
        rcases hbe with ⟨hbl, hbh⟩
        -- the integral of the (nonneg) active value is nonneg:
        -- c·t + (b_g − c)·expInt ≥ min(b_g, c)·t ≥ glo·t ≥ 0
        have hEI0 : 0 ≤ expInt (k : ℝ) t := expInt_nonneg hkR0 ht
        have hEIt : expInt (k : ℝ) t ≤ t := expInt_le hkR0 ht
        have hint : 0 ≤ (c : ℝ) * t + (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) t := by
          rcases le_or_gt (c : ℝ) (base (Rv m.gcoord)) with hbc | hbc
          · nlinarith
          · nlinarith
        constructor
        · cases hcase : (M.env i).lo with
          | none => trivial
          | some l =>
              rw [hcase] at hbl
              show (l : ℝ) ≤ base (Rv i) + (c : ℝ) * t
                + (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) t
              linarith
        · rw [hhi]; trivial
      · -- EXT 2: envelope-free coordinate
        rw [drivenValC_dfrozen hig hdr hjne]
        unfold Band.memR
        rw [hlo, hhi]
        exact ⟨trivial, trivial⟩
  have hstayGd : ∀ t, 0 ≤ t →
      Formula.sat (M.GdOf q) (drivenΦC m (k : ℝ) (c : ℝ) base t) := by
    intro t ht
    rw [sat_GdOf hq]
    obtain ⟨h1, h2⟩ := hband t ht
    exact ⟨hstayEnv t ht, by rw [drivenΦC_Rv]; exact h1, by rw [drivenΦC_Rv]; exact h2⟩
  refine ⟨drivenΦC m (k : ℝ) (c : ℝ) base, ?_, ?_, ?_,
    fun t ht => hstayEnv t ht.1, q, List.mem_cons_self .., hstayGd _ hdt⟩
  · -- t = 0 recovers the base
    funext x
    obtain ⟨sd, ix⟩ := x
    cases sd with
    | R =>
        show drivenValC m (k : ℝ) (c : ℝ) base 0 ix = base (Rv ix)
        unfold drivenValC
        by_cases hig : ix = m.gcoord
        · rw [if_pos hig]
          subst hig
          simp
        · rw [if_neg hig]
          rcases hshx : m.shapes ix with _ | _ | _ | _ <;> simp [expInt]
    | L => rfl
    | Aux => rfl
  · -- derivatives
    intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hig : i = m.gcoord
    · rw [hig]
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf m.gcoord))
          (drivenΦC m (k : ℝ) (c : ℝ) base t)
          = (k : ℝ) * ((c : ℝ) - drivenValC m (k : ℝ) (c : ℝ) base t m.gcoord) := by
        simp [SettlingMode.fieldOf, hsh, CoordShape.field, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => drivenΦC m (k : ℝ) (c : ℝ) base u (Rv m.gcoord))
          = fun u => (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)) := by
        funext u; rw [drivenΦC_Rv, hval_g]
      rw [hcurve]
      -- derivative of the contract closed form (the banked pattern)
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (-((k : ℝ) * u)))
          (-(k : ℝ) * Real.exp (-((k : ℝ) * t))) t := by
        have hinner : HasDerivAt (fun u : ℝ => -((k : ℝ) * u)) (-(k : ℝ)) t := by
          have h := (hasDerivAt_id t).const_mul (-(k : ℝ))
          simp only [id, mul_one, neg_mul] at h
          exact h
        have h := (Real.hasDerivAt_exp (-((k : ℝ) * t))).comp t hinner
        simp only [Function.comp_def] at h
        rw [mul_comm (Real.exp (-((k : ℝ) * t))) (-(k : ℝ))] at h
        exact h
      have h1 : HasDerivAt
          (fun u => (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)))
          ((base (Rv m.gcoord) - (c : ℝ)) * (-(k : ℝ) * Real.exp (-((k : ℝ) * t)))) t :=
        (hexp.const_mul (base (Rv m.gcoord) - (c : ℝ))).const_add (c : ℝ)
      have heq : (base (Rv m.gcoord) - (c : ℝ)) * (-(k : ℝ) * Real.exp (-((k : ℝ) * t)))
          = (k : ℝ) * ((c : ℝ) - drivenValC m (k : ℝ) (c : ℝ) base t m.gcoord) := by
        rw [hval_g]; ring
      rw [← heq]
      exact h1.hasDerivWithinAt
    · rcases hflex i hig with hfz | ⟨hdr, -⟩ | ⟨j, hdr, hjne, hjfz, -, -⟩
      · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦC m (k : ℝ) (c : ℝ) base t) = 0 := by
          simp [SettlingMode.fieldOf, hfz, CoordShape.field, Term.eval, AOp.interp]
        rw [heval]
        have hcurve : (fun u => drivenΦC m (k : ℝ) (c : ℝ) base u (Rv i))
            = fun _ => base (Rv i) := by
          funext u; rw [drivenΦC_Rv, drivenValC_frozen hig hfz]
        rw [hcurve]
        exact hasDerivWithinAt_const t _ _
      · -- driven: derivative = the CURRENT value of the active coordinate
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦC m (k : ℝ) (c : ℝ) base t)
            = (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * t)) := by
          simp [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp,
            drivenΦC_Rv, hval_g]
        rw [heval]
        have hcurve : (fun u => drivenΦC m (k : ℝ) (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + (c : ℝ) * u
                + (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) u := by
          funext u; rw [drivenΦC_Rv, drivenValC_dactive hig hdr]
        rw [hcurve]
        have h1 : HasDerivAt (fun u : ℝ => base (Rv i) + (c : ℝ) * u) (c : ℝ) t := by
          have h := ((hasDerivAt_id t).const_mul (c : ℝ)).const_add (base (Rv i))
          simpa using h
        have h2 : HasDerivAt
            (fun u : ℝ => (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) u)
            ((base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * t))) t :=
          (expInt_hasDeriv (k : ℝ) t).const_mul (base (Rv m.gcoord) - (c : ℝ))
        have h := h1.add h2
        exact h.hasDerivWithinAt
      · -- EXT 2: driven by a frozen non-active coordinate — linear curve, constant driver
        have hvalj : drivenΦC m (k : ℝ) (c : ℝ) base t (Rv j) = base (Rv j) := by
          rw [drivenΦC_Rv, drivenValC_frozen hjne hjfz]
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦC m (k : ℝ) (c : ℝ) base t) = base (Rv j) := by
          simp only [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp]
          rw [hvalj]; ring
        rw [heval]
        have hcurve : (fun u => drivenΦC m (k : ℝ) (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + base (Rv j) * u := by
          funext u; rw [drivenΦC_Rv, drivenValC_dfrozen hig hdr hjne]
        rw [hcurve]
        have h := ((hasDerivAt_id t).const_mul (base (Rv j))).const_add (base (Rv i))
        simp only [id, mul_one] at h
        exact h.hasDerivWithinAt
  · -- mask
    intro t ht x hx
    refine drivenΦC_nonR m (k : ℝ) (c : ℝ) base t ?_
    intro i hxi
    exact hx (by
      rw [hxi]
      simp only [rightBlock, ODESystem.bound, List.map_map]
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

/-- EXT 4: CONTRACT active coordinate with the equilibrium ABOVE its own band — a transit-up
mode; the flow stays in the hull `[glo, c]` and lands in the own band or the covering
successor band (endpoint case-split). -/
theorem settling_contract_above (M : SettlingModel n) {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m) {k c : ℤ}
    (hsh : m.shapes m.gcoord = CoordShape.contract k c)
    (hflex : FlexOthers M m)
    (hglo0 : 0 ≤ m.glo)
    (hk : 0 ≤ k) (hch : m.ghi < c)
    (hloIn : ∀ l', (M.env m.gcoord).lo = some l' → l' ≤ m.glo)
    (hEnvHi : ∀ h', (M.env m.gcoord).hi = some h' → c ≤ h')
    (hcover : ∃ q' ∈ m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
        m'.glo ≤ m.ghi ∧ c ≤ m'.ghi)
    (hdt : (0 : ℝ) ≤ (M.dt : ℝ)) :
    GuardSettlingB M.graph M.GdOf m.fieldOf (Term.const 1) M.envF ((M.dt : ℝ)) q := by
  intro base hb
  obtain ⟨henv, hblo, hbhi⟩ := (sat_GdOf hq).mp hb
  have hkR0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hchR : (m.ghi : ℝ) < (c : ℝ) := by exact_mod_cast hch
  have hglo0R : (0 : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hglo0
  -- the active coordinate's value and its band, for all t ≥ 0
  have hval_g : ∀ t, drivenValC m (k : ℝ) (c : ℝ) base t m.gcoord
      = (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * t)) := by
    intro t; unfold drivenValC; rw [if_pos rfl]
  -- the flow stays in the hull [base, c] ⊆ [glo, c] (base below the equilibrium)
  have hband : ∀ t, 0 ≤ t →
      base (Rv m.gcoord) ≤ drivenValC m (k : ℝ) (c : ℝ) base t m.gcoord
      ∧ drivenValC m (k : ℝ) (c : ℝ) base t m.gcoord ≤ (c : ℝ) := by
    intro t ht
    have hθpos : 0 < Real.exp (-((k : ℝ) * t)) := Real.exp_pos _
    have hθle : Real.exp (-((k : ℝ) * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have hbc : base (Rv m.gcoord) < (c : ℝ) := lt_of_le_of_lt hbhi hchR
    rw [hval_g]
    constructor
    · nlinarith
    · nlinarith
  -- staying in the envelope
  have hstayEnv : ∀ t, 0 ≤ t → Formula.sat M.envF (drivenΦC m (k : ℝ) (c : ℝ) base t) := by
    intro t ht
    rw [sat_envF]
    intro i
    rw [drivenΦC_Rv]
    by_cases hig : i = m.gcoord
    · rw [hig]
      obtain ⟨h1, h2⟩ := hband t ht
      unfold Band.memR
      constructor
      · cases hcase : (M.env m.gcoord).lo with
        | none => trivial
        | some l =>
            have hlG : (l : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hloIn l hcase
            -- value ≥ base ≥ glo ≥ l
            linarith
      · cases hcase : (M.env m.gcoord).hi with
        | none => trivial
        | some h =>
            have hhG : (c : ℝ) ≤ (h : ℝ) := by exact_mod_cast hEnvHi h hcase
            linarith
    · rcases hflex i hig with hfz | ⟨hdr, hhi⟩ | ⟨j, hdr, hjne, -, hlo, hhi⟩
      · rw [drivenValC_frozen hig hfz]
        exact (sat_envF.mp henv) i
      · rw [drivenValC_dactive hig hdr]
        have hbe := (sat_envF.mp henv) i
        unfold Band.memR at hbe ⊢
        rcases hbe with ⟨hbl, hbh⟩
        -- the integral of the (nonneg) active value is nonneg:
        -- c·t + (b_g − c)·expInt ≥ min(b_g, c)·t ≥ glo·t ≥ 0
        have hEI0 : 0 ≤ expInt (k : ℝ) t := expInt_nonneg hkR0 ht
        have hEIt : expInt (k : ℝ) t ≤ t := expInt_le hkR0 ht
        have hint : 0 ≤ (c : ℝ) * t + (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) t := by
          rcases le_or_gt (c : ℝ) (base (Rv m.gcoord)) with hbc | hbc
          · nlinarith
          · nlinarith
        constructor
        · cases hcase : (M.env i).lo with
          | none => trivial
          | some l =>
              rw [hcase] at hbl
              show (l : ℝ) ≤ base (Rv i) + (c : ℝ) * t
                + (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) t
              linarith
        · rw [hhi]; trivial
      · -- EXT 2: envelope-free coordinate
        rw [drivenValC_dfrozen hig hdr hjne]
        unfold Band.memR
        rw [hlo, hhi]
        exact ⟨trivial, trivial⟩
  -- landing: the own band, or the covering successor, chosen by the endpoint
  obtain ⟨q', hq'mem, m', hm', hgc', hcv1, hcv2⟩ := hcover
  have hcv1R : (m'.glo : ℝ) ≤ (m.ghi : ℝ) := by exact_mod_cast hcv1
  have hcv2R : (c : ℝ) ≤ (m'.ghi : ℝ) := by exact_mod_cast hcv2
  have hpick : ∃ q2 ∈ q :: M.graph.retainedSucc q, ∃ m2, M.modes[q2]? = some m2 ∧
      m2.gcoord = m.gcoord ∧
      (m2.glo : ℝ) ≤ drivenValC m (k : ℝ) (c : ℝ) base (M.dt : ℝ) m.gcoord ∧
      drivenValC m (k : ℝ) (c : ℝ) base (M.dt : ℝ) m.gcoord ≤ (m2.ghi : ℝ) := by
    obtain ⟨he1, he2⟩ := hband (M.dt : ℝ) hdt
    rcases le_or_gt (drivenValC m (k : ℝ) (c : ℝ) base (M.dt : ℝ) m.gcoord) (m.ghi : ℝ)
      with he | he
    · exact ⟨q, List.mem_cons_self .., m, hq, rfl, by linarith, he⟩
    · exact ⟨q', List.mem_cons_of_mem _ (succ_mem_retained M hq hq'mem), m', hm', hgc',
        by linarith, by linarith⟩
  obtain ⟨q2, hq2ret, m2, hm2, hgc2, hl1, hl2⟩ := hpick
  refine ⟨drivenΦC m (k : ℝ) (c : ℝ) base, ?_, ?_, ?_,
    fun t ht => hstayEnv t ht.1, q2, hq2ret, ?_⟩
  · -- t = 0 recovers the base
    funext x
    obtain ⟨sd, ix⟩ := x
    cases sd with
    | R =>
        show drivenValC m (k : ℝ) (c : ℝ) base 0 ix = base (Rv ix)
        unfold drivenValC
        by_cases hig : ix = m.gcoord
        · rw [if_pos hig]
          subst hig
          simp
        · rw [if_neg hig]
          rcases hshx : m.shapes ix with _ | _ | _ | _ <;> simp [expInt]
    | L => rfl
    | Aux => rfl
  · -- derivatives
    intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hig : i = m.gcoord
    · rw [hig]
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf m.gcoord))
          (drivenΦC m (k : ℝ) (c : ℝ) base t)
          = (k : ℝ) * ((c : ℝ) - drivenValC m (k : ℝ) (c : ℝ) base t m.gcoord) := by
        simp [SettlingMode.fieldOf, hsh, CoordShape.field, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => drivenΦC m (k : ℝ) (c : ℝ) base u (Rv m.gcoord))
          = fun u => (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)) := by
        funext u; rw [drivenΦC_Rv, hval_g]
      rw [hcurve]
      -- derivative of the contract closed form (the banked pattern)
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (-((k : ℝ) * u)))
          (-(k : ℝ) * Real.exp (-((k : ℝ) * t))) t := by
        have hinner : HasDerivAt (fun u : ℝ => -((k : ℝ) * u)) (-(k : ℝ)) t := by
          have h := (hasDerivAt_id t).const_mul (-(k : ℝ))
          simp only [id, mul_one, neg_mul] at h
          exact h
        have h := (Real.hasDerivAt_exp (-((k : ℝ) * t))).comp t hinner
        simp only [Function.comp_def] at h
        rw [mul_comm (Real.exp (-((k : ℝ) * t))) (-(k : ℝ))] at h
        exact h
      have h1 : HasDerivAt
          (fun u => (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)))
          ((base (Rv m.gcoord) - (c : ℝ)) * (-(k : ℝ) * Real.exp (-((k : ℝ) * t)))) t :=
        (hexp.const_mul (base (Rv m.gcoord) - (c : ℝ))).const_add (c : ℝ)
      have heq : (base (Rv m.gcoord) - (c : ℝ)) * (-(k : ℝ) * Real.exp (-((k : ℝ) * t)))
          = (k : ℝ) * ((c : ℝ) - drivenValC m (k : ℝ) (c : ℝ) base t m.gcoord) := by
        rw [hval_g]; ring
      rw [← heq]
      exact h1.hasDerivWithinAt
    · rcases hflex i hig with hfz | ⟨hdr, -⟩ | ⟨j, hdr, hjne, hjfz, -, -⟩
      · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦC m (k : ℝ) (c : ℝ) base t) = 0 := by
          simp [SettlingMode.fieldOf, hfz, CoordShape.field, Term.eval, AOp.interp]
        rw [heval]
        have hcurve : (fun u => drivenΦC m (k : ℝ) (c : ℝ) base u (Rv i))
            = fun _ => base (Rv i) := by
          funext u; rw [drivenΦC_Rv, drivenValC_frozen hig hfz]
        rw [hcurve]
        exact hasDerivWithinAt_const t _ _
      · -- driven: derivative = the CURRENT value of the active coordinate
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦC m (k : ℝ) (c : ℝ) base t)
            = (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * t)) := by
          simp [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp,
            drivenΦC_Rv, hval_g]
        rw [heval]
        have hcurve : (fun u => drivenΦC m (k : ℝ) (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + (c : ℝ) * u
                + (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) u := by
          funext u; rw [drivenΦC_Rv, drivenValC_dactive hig hdr]
        rw [hcurve]
        have h1 : HasDerivAt (fun u : ℝ => base (Rv i) + (c : ℝ) * u) (c : ℝ) t := by
          have h := ((hasDerivAt_id t).const_mul (c : ℝ)).const_add (base (Rv i))
          simpa using h
        have h2 : HasDerivAt
            (fun u : ℝ => (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) u)
            ((base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * t))) t :=
          (expInt_hasDeriv (k : ℝ) t).const_mul (base (Rv m.gcoord) - (c : ℝ))
        have h := h1.add h2
        exact h.hasDerivWithinAt
      · -- EXT 2: driven by a frozen non-active coordinate — linear curve, constant driver
        have hvalj : drivenΦC m (k : ℝ) (c : ℝ) base t (Rv j) = base (Rv j) := by
          rw [drivenΦC_Rv, drivenValC_frozen hjne hjfz]
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦC m (k : ℝ) (c : ℝ) base t) = base (Rv j) := by
          simp only [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp]
          rw [hvalj]; ring
        rw [heval]
        have hcurve : (fun u => drivenΦC m (k : ℝ) (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + base (Rv j) * u := by
          funext u; rw [drivenΦC_Rv, drivenValC_dfrozen hig hdr hjne]
        rw [hcurve]
        have h := ((hasDerivAt_id t).const_mul (base (Rv j))).const_add (base (Rv i))
        simp only [id, mul_one] at h
        exact h.hasDerivWithinAt
  · -- mask
    intro t ht x hx
    refine drivenΦC_nonR m (k : ℝ) (c : ℝ) base t ?_
    intro i hxi
    exact hx (by
      rw [hxi]
      simp only [rightBlock, ODESystem.bound, List.map_map]
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  · -- landing in the picked band
    rw [sat_GdOf hm2]
    refine ⟨hstayEnv _ hdt, ?_, ?_⟩
    · rw [hgc2, drivenΦC_Rv]; exact hl1
    · rw [hgc2, drivenΦC_Rv]; exact hl2


/-- EXT 4: CONTRACT active coordinate with the equilibrium BELOW its own band — a transit-down
mode (a drain); the flow stays in the hull `[c, ghi]` and lands in the own band or the
covering successor band (endpoint case-split). `0 ≤ c` keeps driven integrators monotone. -/
theorem settling_contract_below (M : SettlingModel n) {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m) {k c : ℤ}
    (hsh : m.shapes m.gcoord = CoordShape.contract k c)
    (hflex : FlexOthers M m)
    (hglo0 : 0 ≤ m.glo)
    (hk : 0 ≤ k) (hcl : c < m.glo) (hc0 : 0 ≤ c)
    (hEnvLo : ∀ l', (M.env m.gcoord).lo = some l' → l' ≤ c)
    (hhiIn : ∀ h', (M.env m.gcoord).hi = some h' → m.ghi ≤ h')
    (hcover : ∃ q' ∈ m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
        m.glo ≤ m'.ghi ∧ m'.glo ≤ c)
    (hdt : (0 : ℝ) ≤ (M.dt : ℝ)) :
    GuardSettlingB M.graph M.GdOf m.fieldOf (Term.const 1) M.envF ((M.dt : ℝ)) q := by
  intro base hb
  obtain ⟨henv, hblo, hbhi⟩ := (sat_GdOf hq).mp hb
  have hkR0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hclR : (c : ℝ) < (m.glo : ℝ) := by exact_mod_cast hcl
  have hglo0R : (0 : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hglo0
  -- the active coordinate's value and its band, for all t ≥ 0
  have hval_g : ∀ t, drivenValC m (k : ℝ) (c : ℝ) base t m.gcoord
      = (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * t)) := by
    intro t; unfold drivenValC; rw [if_pos rfl]
  -- the flow stays in the hull [c, base] ⊆ [c, ghi] (base above the equilibrium)
  have hband : ∀ t, 0 ≤ t →
      (c : ℝ) ≤ drivenValC m (k : ℝ) (c : ℝ) base t m.gcoord
      ∧ drivenValC m (k : ℝ) (c : ℝ) base t m.gcoord ≤ base (Rv m.gcoord) := by
    intro t ht
    have hθpos : 0 < Real.exp (-((k : ℝ) * t)) := Real.exp_pos _
    have hθle : Real.exp (-((k : ℝ) * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have hbc : (c : ℝ) < base (Rv m.gcoord) := lt_of_lt_of_le hclR hblo
    rw [hval_g]
    constructor
    · nlinarith
    · nlinarith
  -- staying in the envelope
  have hstayEnv : ∀ t, 0 ≤ t → Formula.sat M.envF (drivenΦC m (k : ℝ) (c : ℝ) base t) := by
    intro t ht
    rw [sat_envF]
    intro i
    rw [drivenΦC_Rv]
    by_cases hig : i = m.gcoord
    · rw [hig]
      obtain ⟨h1, h2⟩ := hband t ht
      unfold Band.memR
      constructor
      · cases hcase : (M.env m.gcoord).lo with
        | none => trivial
        | some l =>
            have hlG : (l : ℝ) ≤ (c : ℝ) := by exact_mod_cast hEnvLo l hcase
            linarith
      · cases hcase : (M.env m.gcoord).hi with
        | none => trivial
        | some h =>
            have hhG : (m.ghi : ℝ) ≤ (h : ℝ) := by exact_mod_cast hhiIn h hcase
            linarith
    · rcases hflex i hig with hfz | ⟨hdr, hhi⟩ | ⟨j, hdr, hjne, -, hlo, hhi⟩
      · rw [drivenValC_frozen hig hfz]
        exact (sat_envF.mp henv) i
      · rw [drivenValC_dactive hig hdr]
        have hbe := (sat_envF.mp henv) i
        unfold Band.memR at hbe ⊢
        rcases hbe with ⟨hbl, hbh⟩
        -- the integral of the (nonneg) active value is nonneg:
        -- c·t + (b_g − c)·expInt ≥ min(b_g, c)·t ≥ glo·t ≥ 0
        have hEI0 : 0 ≤ expInt (k : ℝ) t := expInt_nonneg hkR0 ht
        have hEIt : expInt (k : ℝ) t ≤ t := expInt_le hkR0 ht
        have hc0R : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc0
        have hint : 0 ≤ (c : ℝ) * t + (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) t := by
          have hbc : (c : ℝ) ≤ base (Rv m.gcoord) := le_of_lt (lt_of_lt_of_le hclR hblo)
          nlinarith
        constructor
        · cases hcase : (M.env i).lo with
          | none => trivial
          | some l =>
              rw [hcase] at hbl
              show (l : ℝ) ≤ base (Rv i) + (c : ℝ) * t
                + (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) t
              linarith
        · rw [hhi]; trivial
      · -- EXT 2: envelope-free coordinate
        rw [drivenValC_dfrozen hig hdr hjne]
        unfold Band.memR
        rw [hlo, hhi]
        exact ⟨trivial, trivial⟩
  -- landing: the own band, or the covering successor, chosen by the endpoint
  obtain ⟨q', hq'mem, m', hm', hgc', hcv1, hcv2⟩ := hcover
  have hcv1R : (m.glo : ℝ) ≤ (m'.ghi : ℝ) := by exact_mod_cast hcv1
  have hcv2R : (m'.glo : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcv2
  have hpick : ∃ q2 ∈ q :: M.graph.retainedSucc q, ∃ m2, M.modes[q2]? = some m2 ∧
      m2.gcoord = m.gcoord ∧
      (m2.glo : ℝ) ≤ drivenValC m (k : ℝ) (c : ℝ) base (M.dt : ℝ) m.gcoord ∧
      drivenValC m (k : ℝ) (c : ℝ) base (M.dt : ℝ) m.gcoord ≤ (m2.ghi : ℝ) := by
    obtain ⟨he1, he2⟩ := hband (M.dt : ℝ) hdt
    rcases le_or_gt (m.glo : ℝ) (drivenValC m (k : ℝ) (c : ℝ) base (M.dt : ℝ) m.gcoord)
      with he | he
    · exact ⟨q, List.mem_cons_self .., m, hq, rfl, he, by linarith⟩
    · exact ⟨q', List.mem_cons_of_mem _ (succ_mem_retained M hq hq'mem), m', hm', hgc',
        by linarith, by linarith⟩
  obtain ⟨q2, hq2ret, m2, hm2, hgc2, hl1, hl2⟩ := hpick
  refine ⟨drivenΦC m (k : ℝ) (c : ℝ) base, ?_, ?_, ?_,
    fun t ht => hstayEnv t ht.1, q2, hq2ret, ?_⟩
  · -- t = 0 recovers the base
    funext x
    obtain ⟨sd, ix⟩ := x
    cases sd with
    | R =>
        show drivenValC m (k : ℝ) (c : ℝ) base 0 ix = base (Rv ix)
        unfold drivenValC
        by_cases hig : ix = m.gcoord
        · rw [if_pos hig]
          subst hig
          simp
        · rw [if_neg hig]
          rcases hshx : m.shapes ix with _ | _ | _ | _ <;> simp [expInt]
    | L => rfl
    | Aux => rfl
  · -- derivatives
    intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hig : i = m.gcoord
    · rw [hig]
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf m.gcoord))
          (drivenΦC m (k : ℝ) (c : ℝ) base t)
          = (k : ℝ) * ((c : ℝ) - drivenValC m (k : ℝ) (c : ℝ) base t m.gcoord) := by
        simp [SettlingMode.fieldOf, hsh, CoordShape.field, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => drivenΦC m (k : ℝ) (c : ℝ) base u (Rv m.gcoord))
          = fun u => (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)) := by
        funext u; rw [drivenΦC_Rv, hval_g]
      rw [hcurve]
      -- derivative of the contract closed form (the banked pattern)
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (-((k : ℝ) * u)))
          (-(k : ℝ) * Real.exp (-((k : ℝ) * t))) t := by
        have hinner : HasDerivAt (fun u : ℝ => -((k : ℝ) * u)) (-(k : ℝ)) t := by
          have h := (hasDerivAt_id t).const_mul (-(k : ℝ))
          simp only [id, mul_one, neg_mul] at h
          exact h
        have h := (Real.hasDerivAt_exp (-((k : ℝ) * t))).comp t hinner
        simp only [Function.comp_def] at h
        rw [mul_comm (Real.exp (-((k : ℝ) * t))) (-(k : ℝ))] at h
        exact h
      have h1 : HasDerivAt
          (fun u => (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)))
          ((base (Rv m.gcoord) - (c : ℝ)) * (-(k : ℝ) * Real.exp (-((k : ℝ) * t)))) t :=
        (hexp.const_mul (base (Rv m.gcoord) - (c : ℝ))).const_add (c : ℝ)
      have heq : (base (Rv m.gcoord) - (c : ℝ)) * (-(k : ℝ) * Real.exp (-((k : ℝ) * t)))
          = (k : ℝ) * ((c : ℝ) - drivenValC m (k : ℝ) (c : ℝ) base t m.gcoord) := by
        rw [hval_g]; ring
      rw [← heq]
      exact h1.hasDerivWithinAt
    · rcases hflex i hig with hfz | ⟨hdr, -⟩ | ⟨j, hdr, hjne, hjfz, -, -⟩
      · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦC m (k : ℝ) (c : ℝ) base t) = 0 := by
          simp [SettlingMode.fieldOf, hfz, CoordShape.field, Term.eval, AOp.interp]
        rw [heval]
        have hcurve : (fun u => drivenΦC m (k : ℝ) (c : ℝ) base u (Rv i))
            = fun _ => base (Rv i) := by
          funext u; rw [drivenΦC_Rv, drivenValC_frozen hig hfz]
        rw [hcurve]
        exact hasDerivWithinAt_const t _ _
      · -- driven: derivative = the CURRENT value of the active coordinate
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦC m (k : ℝ) (c : ℝ) base t)
            = (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * t)) := by
          simp [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp,
            drivenΦC_Rv, hval_g]
        rw [heval]
        have hcurve : (fun u => drivenΦC m (k : ℝ) (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + (c : ℝ) * u
                + (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) u := by
          funext u; rw [drivenΦC_Rv, drivenValC_dactive hig hdr]
        rw [hcurve]
        have h1 : HasDerivAt (fun u : ℝ => base (Rv i) + (c : ℝ) * u) (c : ℝ) t := by
          have h := ((hasDerivAt_id t).const_mul (c : ℝ)).const_add (base (Rv i))
          simpa using h
        have h2 : HasDerivAt
            (fun u : ℝ => (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) u)
            ((base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * t))) t :=
          (expInt_hasDeriv (k : ℝ) t).const_mul (base (Rv m.gcoord) - (c : ℝ))
        have h := h1.add h2
        exact h.hasDerivWithinAt
      · -- EXT 2: driven by a frozen non-active coordinate — linear curve, constant driver
        have hvalj : drivenΦC m (k : ℝ) (c : ℝ) base t (Rv j) = base (Rv j) := by
          rw [drivenΦC_Rv, drivenValC_frozen hjne hjfz]
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦC m (k : ℝ) (c : ℝ) base t) = base (Rv j) := by
          simp only [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp]
          rw [hvalj]; ring
        rw [heval]
        have hcurve : (fun u => drivenΦC m (k : ℝ) (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + base (Rv j) * u := by
          funext u; rw [drivenΦC_Rv, drivenValC_dfrozen hig hdr hjne]
        rw [hcurve]
        have h := ((hasDerivAt_id t).const_mul (base (Rv j))).const_add (base (Rv i))
        simp only [id, mul_one] at h
        exact h.hasDerivWithinAt
  · -- mask
    intro t ht x hx
    refine drivenΦC_nonR m (k : ℝ) (c : ℝ) base t ?_
    intro i hxi
    exact hx (by
      rw [hxi]
      simp only [rightBlock, ODESystem.bound, List.map_map]
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  · -- landing in the picked band
    rw [sat_GdOf hm2]
    refine ⟨hstayEnv _ hdt, ?_, ?_⟩
    · rw [hgc2, drivenΦC_Rv]; exact hl1
    · rw [hgc2, drivenΦC_Rv]; exact hl2



/-! ### EXT 4b — the extended flex grammar (contract others, contract-driven integrators)

`FlexOthersC` extends `FlexOthers` with two arms needed by coupled integrator benchmarks
(rover_4d_box's `py' = vy` with `vy` contracting): a CONTRACT-shaped other coordinate whose
equilibrium sits inside its envelope band (it stays in the hull of base and equilibrium), and
an envelope-free coordinate DRIVEN BY such a contract other (its witness is the exp-integral
of the driver). The `flexVal` witness realizes every arm; `settling_contract_below_flex` is
the contract-below discharge over this grammar (the checker's below branch uses it — a
strict superset of the old grammar, so every previously accepted instance still passes). -/

/-- The extended flex condition on non-active coordinates. -/
def FlexOthersC (M : SettlingModel n) (m : SettlingMode n) : Prop :=
  ∀ i, i ≠ m.gcoord → m.shapes i = CoordShape.frozen ∨
    (m.shapes i = CoordShape.driven m.gcoord ∧ (M.env i).hi = none) ∨
    (∃ j, m.shapes i = CoordShape.driven j ∧ j ≠ m.gcoord ∧
      m.shapes j = CoordShape.frozen ∧ (M.env i).lo = none ∧ (M.env i).hi = none) ∨
    (∃ k' c', m.shapes i = CoordShape.contract k' c' ∧ 0 ≤ k' ∧
      (∀ l', (M.env i).lo = some l' → l' ≤ c') ∧
      (∀ h', (M.env i).hi = some h' → c' ≤ h')) ∨
    (∃ j kj cj, m.shapes i = CoordShape.driven j ∧ j ≠ m.gcoord ∧
      m.shapes j = CoordShape.contract kj cj ∧ (M.env i).lo = none ∧ (M.env i).hi = none)

/-- The old grammar embeds. -/
theorem FlexOthers.toC {M : SettlingModel n} {m : SettlingMode n} (h : FlexOthers M m) :
    FlexOthersC M m := by
  intro i hig
  rcases h i hig with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))

/-- Per-coordinate value of the extended-flex witness (contract active). -/
noncomputable def flexVal (m : SettlingMode n) (kR cR : ℝ) (base : State (Var n)) (t : ℝ)
    (i : Fin n) : ℝ :=
  if i = m.gcoord then cR + (base (Rv i) - cR) * Real.exp (-(kR * t))
  else match m.shapes i with
    | CoordShape.driven j =>
        if j = m.gcoord then
          base (Rv i) + cR * t + (base (Rv m.gcoord) - cR) * expInt kR t
        else match m.shapes j with
          | CoordShape.contract kj cj =>
              base (Rv i) + (cj : ℝ) * t + (base (Rv j) - (cj : ℝ)) * expInt (kj : ℝ) t
          | _ => base (Rv i) + base (Rv j) * t
    | CoordShape.contract k' c' =>
        (c' : ℝ) + (base (Rv i) - (c' : ℝ)) * Real.exp (-((k' : ℝ) * t))
    | _ => base (Rv i)

/-- The extended-flex witness flow. -/
noncomputable def flexΦ (m : SettlingMode n) (kR cR : ℝ) (base : State (Var n)) (t : ℝ) :
    State (Var n) :=
  fun x => match x with
    | (Side.R, i) => flexVal m kR cR base t i
    | _ => base x

@[simp] theorem flexΦ_Rv (m : SettlingMode n) (kR cR : ℝ) (base : State (Var n)) (t : ℝ)
    (i : Fin n) : flexΦ m kR cR base t (Rv i) = flexVal m kR cR base t i := rfl

theorem flexΦ_nonR (m : SettlingMode n) (kR cR : ℝ) (base : State (Var n)) (t : ℝ)
    {x : Var n} (hx : ∀ i : Fin n, x ≠ Rv i) : flexΦ m kR cR base t x = base x := by
  obtain ⟨sd, ix⟩ := x
  cases sd with
  | R => exact absurd rfl (hx ix)
  | L => rfl
  | Aux => rfl

theorem flexVal_g {m : SettlingMode n} {kR cR : ℝ} {base : State (Var n)} {t : ℝ} :
    flexVal m kR cR base t m.gcoord
      = cR + (base (Rv m.gcoord) - cR) * Real.exp (-(kR * t)) := by
  simp [flexVal]

theorem flexVal_frozen {m : SettlingMode n} {kR cR : ℝ} {base : State (Var n)} {t : ℝ}
    {i : Fin n} (hig : i ≠ m.gcoord) (hfz : m.shapes i = CoordShape.frozen) :
    flexVal m kR cR base t i = base (Rv i) := by
  simp [flexVal, hig, hfz]

theorem flexVal_dactive {m : SettlingMode n} {kR cR : ℝ} {base : State (Var n)} {t : ℝ}
    {i : Fin n} (hig : i ≠ m.gcoord) (hdr : m.shapes i = CoordShape.driven m.gcoord) :
    flexVal m kR cR base t i
      = base (Rv i) + cR * t + (base (Rv m.gcoord) - cR) * expInt kR t := by
  simp [flexVal, hig, hdr]

theorem flexVal_dfrozen {m : SettlingMode n} {kR cR : ℝ} {base : State (Var n)} {t : ℝ}
    {i j : Fin n} (hig : i ≠ m.gcoord) (hdr : m.shapes i = CoordShape.driven j)
    (hjne : j ≠ m.gcoord) (hjfz : m.shapes j = CoordShape.frozen) :
    flexVal m kR cR base t i = base (Rv i) + base (Rv j) * t := by
  simp [flexVal, hig, hdr, hjne, hjfz]

theorem flexVal_dcontract {m : SettlingMode n} {kR cR : ℝ} {base : State (Var n)} {t : ℝ}
    {i j : Fin n} {kj cj : ℤ} (hig : i ≠ m.gcoord) (hdr : m.shapes i = CoordShape.driven j)
    (hjne : j ≠ m.gcoord) (hjc : m.shapes j = CoordShape.contract kj cj) :
    flexVal m kR cR base t i
      = base (Rv i) + (cj : ℝ) * t + (base (Rv j) - (cj : ℝ)) * expInt (kj : ℝ) t := by
  simp [flexVal, hig, hdr, hjne, hjc]

theorem flexVal_contract {m : SettlingMode n} {kR cR : ℝ} {base : State (Var n)} {t : ℝ}
    {i : Fin n} {k' c' : ℤ} (hig : i ≠ m.gcoord)
    (hshc : m.shapes i = CoordShape.contract k' c') :
    flexVal m kR cR base t i
      = (c' : ℝ) + (base (Rv i) - (c' : ℝ)) * Real.exp (-((k' : ℝ) * t)) := by
  simp [flexVal, hig, hshc]

/-- EXT 4b: the contract-below discharge over the EXTENDED flex grammar (`FlexOthersC`) —
adds contract others and contract-driven integrators. CONTRACT active with equilibrium BELOW its own band — a transit-down
mode (a drain); the flow stays in the hull `[c, ghi]` and lands in the own band or the
covering successor band (endpoint case-split). `0 ≤ c` keeps driven integrators monotone. -/
theorem settling_contract_below_flex (M : SettlingModel n) {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m) {k c : ℤ}
    (hsh : m.shapes m.gcoord = CoordShape.contract k c)
    (hflex : FlexOthersC M m)
    (hglo0 : 0 ≤ m.glo)
    (hk : 0 ≤ k) (hcl : c < m.glo) (hc0 : 0 ≤ c)
    (hEnvLo : ∀ l', (M.env m.gcoord).lo = some l' → l' ≤ c)
    (hhiIn : ∀ h', (M.env m.gcoord).hi = some h' → m.ghi ≤ h')
    (hcover : ∃ q' ∈ m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
        m.glo ≤ m'.ghi ∧ m'.glo ≤ c)
    (hdt : (0 : ℝ) ≤ (M.dt : ℝ)) :
    GuardSettlingB M.graph M.GdOf m.fieldOf (Term.const 1) M.envF ((M.dt : ℝ)) q := by
  intro base hb
  obtain ⟨henv, hblo, hbhi⟩ := (sat_GdOf hq).mp hb
  have hkR0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hclR : (c : ℝ) < (m.glo : ℝ) := by exact_mod_cast hcl
  have hglo0R : (0 : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hglo0
  -- the active coordinate's value and its band, for all t ≥ 0
  have hval_g : ∀ t, flexVal m (k : ℝ) (c : ℝ) base t m.gcoord
      = (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * t)) := by
    intro t; unfold flexVal; rw [if_pos rfl]
  -- the flow stays in the hull [c, base] ⊆ [c, ghi] (base above the equilibrium)
  have hband : ∀ t, 0 ≤ t →
      (c : ℝ) ≤ flexVal m (k : ℝ) (c : ℝ) base t m.gcoord
      ∧ flexVal m (k : ℝ) (c : ℝ) base t m.gcoord ≤ base (Rv m.gcoord) := by
    intro t ht
    have hθpos : 0 < Real.exp (-((k : ℝ) * t)) := Real.exp_pos _
    have hθle : Real.exp (-((k : ℝ) * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have hbc : (c : ℝ) < base (Rv m.gcoord) := lt_of_lt_of_le hclR hblo
    rw [hval_g]
    constructor
    · nlinarith
    · nlinarith
  -- staying in the envelope
  have hstayEnv : ∀ t, 0 ≤ t → Formula.sat M.envF (flexΦ m (k : ℝ) (c : ℝ) base t) := by
    intro t ht
    rw [sat_envF]
    intro i
    rw [flexΦ_Rv]
    by_cases hig : i = m.gcoord
    · rw [hig]
      obtain ⟨h1, h2⟩ := hband t ht
      unfold Band.memR
      constructor
      · cases hcase : (M.env m.gcoord).lo with
        | none => trivial
        | some l =>
            have hlG : (l : ℝ) ≤ (c : ℝ) := by exact_mod_cast hEnvLo l hcase
            linarith
      · cases hcase : (M.env m.gcoord).hi with
        | none => trivial
        | some h =>
            have hhG : (m.ghi : ℝ) ≤ (h : ℝ) := by exact_mod_cast hhiIn h hcase
            linarith
    · rcases hflex i hig with hfz | ⟨hdr, hhi⟩ | ⟨j, hdr, hjne, hjfz, hlo, hhi⟩
        | ⟨k', c', hshc, hk', hloC, hhiC⟩ | ⟨j, kj, cj, hdr, hjne, hjc, hlo, hhi⟩
      · rw [flexVal_frozen hig hfz]
        exact (sat_envF.mp henv) i
      · rw [flexVal_dactive hig hdr]
        have hbe := (sat_envF.mp henv) i
        unfold Band.memR at hbe ⊢
        rcases hbe with ⟨hbl, hbh⟩
        -- the integral of the (nonneg) active value is nonneg:
        -- c·t + (b_g − c)·expInt ≥ min(b_g, c)·t ≥ glo·t ≥ 0
        have hEI0 : 0 ≤ expInt (k : ℝ) t := expInt_nonneg hkR0 ht
        have hEIt : expInt (k : ℝ) t ≤ t := expInt_le hkR0 ht
        have hc0R : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc0
        have hint : 0 ≤ (c : ℝ) * t + (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) t := by
          have hbc : (c : ℝ) ≤ base (Rv m.gcoord) := le_of_lt (lt_of_lt_of_le hclR hblo)
          nlinarith
        constructor
        · cases hcase : (M.env i).lo with
          | none => trivial
          | some l =>
              rw [hcase] at hbl
              show (l : ℝ) ≤ base (Rv i) + (c : ℝ) * t
                + (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) t
              linarith
        · rw [hhi]; trivial
      · -- EXT 2: envelope-free coordinate
        rw [flexVal_dfrozen hig hdr hjne hjfz]
        unfold Band.memR
        rw [hlo, hhi]
        exact ⟨trivial, trivial⟩
      · -- EXT 4b: contract other — hull of base and equilibrium, inside its envelope band
        have hk'R : (0 : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hk'
        have hθpos : 0 < Real.exp (-((k' : ℝ) * t)) := Real.exp_pos _
        have hθle : Real.exp (-((k' : ℝ) * t)) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith
        rw [flexVal_contract hig hshc]
        have hbe := (sat_envF.mp henv) i
        unfold Band.memR at hbe ⊢
        rcases hbe with ⟨hbl, hbh⟩
        constructor
        · cases hcase : (M.env i).lo with
          | none => trivial
          | some l =>
              rw [hcase] at hbl
              have hlc : (l : ℝ) ≤ (c' : ℝ) := by exact_mod_cast hloC l hcase
              nlinarith
        · cases hcase : (M.env i).hi with
          | none => trivial
          | some h =>
              rw [hcase] at hbh
              have hhc : (c' : ℝ) ≤ (h : ℝ) := by exact_mod_cast hhiC h hcase
              nlinarith
      · -- EXT 4b: envelope-free coordinate driven by a contract other
        rw [flexVal_dcontract hig hdr hjne hjc]
        unfold Band.memR
        rw [hlo, hhi]
        exact ⟨trivial, trivial⟩
  -- landing: the own band, or the covering successor, chosen by the endpoint
  obtain ⟨q', hq'mem, m', hm', hgc', hcv1, hcv2⟩ := hcover
  have hcv1R : (m.glo : ℝ) ≤ (m'.ghi : ℝ) := by exact_mod_cast hcv1
  have hcv2R : (m'.glo : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcv2
  have hpick : ∃ q2 ∈ q :: M.graph.retainedSucc q, ∃ m2, M.modes[q2]? = some m2 ∧
      m2.gcoord = m.gcoord ∧
      (m2.glo : ℝ) ≤ flexVal m (k : ℝ) (c : ℝ) base (M.dt : ℝ) m.gcoord ∧
      flexVal m (k : ℝ) (c : ℝ) base (M.dt : ℝ) m.gcoord ≤ (m2.ghi : ℝ) := by
    obtain ⟨he1, he2⟩ := hband (M.dt : ℝ) hdt
    rcases le_or_gt (m.glo : ℝ) (flexVal m (k : ℝ) (c : ℝ) base (M.dt : ℝ) m.gcoord)
      with he | he
    · exact ⟨q, List.mem_cons_self .., m, hq, rfl, he, by linarith⟩
    · exact ⟨q', List.mem_cons_of_mem _ (succ_mem_retained M hq hq'mem), m', hm', hgc',
        by linarith, by linarith⟩
  obtain ⟨q2, hq2ret, m2, hm2, hgc2, hl1, hl2⟩ := hpick
  refine ⟨flexΦ m (k : ℝ) (c : ℝ) base, ?_, ?_, ?_,
    fun t ht => hstayEnv t ht.1, q2, hq2ret, ?_⟩
  · -- t = 0 recovers the base
    funext x
    obtain ⟨sd, ix⟩ := x
    cases sd with
    | R =>
        show flexVal m (k : ℝ) (c : ℝ) base 0 ix = base (Rv ix)
        unfold flexVal
        by_cases hig : ix = m.gcoord
        · rw [if_pos hig]
          subst hig
          simp
        · rw [if_neg hig]
          rcases hshx : m.shapes ix with _ | _ | _ | _ | j2 | _ | _ | _ | _
          · simp
          · simp
          · simp
          · simp
          · by_cases hj2 : j2 = m.gcoord
            · simp [hj2, expInt]
            · rcases hshj : m.shapes j2 with _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
                simp [hj2, expInt] <;> (try rfl) <;> split <;> rfl
          · simp
          · simp
          · simp
          · simp
    | L => rfl
    | Aux => rfl
  · -- derivatives
    intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hig : i = m.gcoord
    · rw [hig]
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf m.gcoord))
          (flexΦ m (k : ℝ) (c : ℝ) base t)
          = (k : ℝ) * ((c : ℝ) - flexVal m (k : ℝ) (c : ℝ) base t m.gcoord) := by
        simp [SettlingMode.fieldOf, hsh, CoordShape.field, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => flexΦ m (k : ℝ) (c : ℝ) base u (Rv m.gcoord))
          = fun u => (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)) := by
        funext u; rw [flexΦ_Rv, hval_g]
      rw [hcurve]
      -- derivative of the contract closed form (the banked pattern)
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (-((k : ℝ) * u)))
          (-(k : ℝ) * Real.exp (-((k : ℝ) * t))) t := by
        have hinner : HasDerivAt (fun u : ℝ => -((k : ℝ) * u)) (-(k : ℝ)) t := by
          have h := (hasDerivAt_id t).const_mul (-(k : ℝ))
          simp only [id, mul_one, neg_mul] at h
          exact h
        have h := (Real.hasDerivAt_exp (-((k : ℝ) * t))).comp t hinner
        simp only [Function.comp_def] at h
        rw [mul_comm (Real.exp (-((k : ℝ) * t))) (-(k : ℝ))] at h
        exact h
      have h1 : HasDerivAt
          (fun u => (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)))
          ((base (Rv m.gcoord) - (c : ℝ)) * (-(k : ℝ) * Real.exp (-((k : ℝ) * t)))) t :=
        (hexp.const_mul (base (Rv m.gcoord) - (c : ℝ))).const_add (c : ℝ)
      have heq : (base (Rv m.gcoord) - (c : ℝ)) * (-(k : ℝ) * Real.exp (-((k : ℝ) * t)))
          = (k : ℝ) * ((c : ℝ) - flexVal m (k : ℝ) (c : ℝ) base t m.gcoord) := by
        rw [hval_g]; ring
      rw [← heq]
      exact h1.hasDerivWithinAt
    · rcases hflex i hig with hfz | ⟨hdr, -⟩ | ⟨j, hdr, hjne, hjfz, -, -⟩
        | ⟨k', c', hshc, -, -, -⟩ | ⟨j, kj, cj, hdr, hjne, hjc, -, -⟩
      · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (flexΦ m (k : ℝ) (c : ℝ) base t) = 0 := by
          simp [SettlingMode.fieldOf, hfz, CoordShape.field, Term.eval, AOp.interp]
        rw [heval]
        have hcurve : (fun u => flexΦ m (k : ℝ) (c : ℝ) base u (Rv i))
            = fun _ => base (Rv i) := by
          funext u; rw [flexΦ_Rv, flexVal_frozen hig hfz]
        rw [hcurve]
        exact hasDerivWithinAt_const t _ _
      · -- driven: derivative = the CURRENT value of the active coordinate
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (flexΦ m (k : ℝ) (c : ℝ) base t)
            = (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * t)) := by
          simp [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp,
            flexΦ_Rv, hval_g]
        rw [heval]
        have hcurve : (fun u => flexΦ m (k : ℝ) (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + (c : ℝ) * u
                + (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) u := by
          funext u; rw [flexΦ_Rv, flexVal_dactive hig hdr]
        rw [hcurve]
        have h1 : HasDerivAt (fun u : ℝ => base (Rv i) + (c : ℝ) * u) (c : ℝ) t := by
          have h := ((hasDerivAt_id t).const_mul (c : ℝ)).const_add (base (Rv i))
          simpa using h
        have h2 : HasDerivAt
            (fun u : ℝ => (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) u)
            ((base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * t))) t :=
          (expInt_hasDeriv (k : ℝ) t).const_mul (base (Rv m.gcoord) - (c : ℝ))
        have h := h1.add h2
        exact h.hasDerivWithinAt
      · -- EXT 2: driven by a frozen non-active coordinate — linear curve, constant driver
        have hvalj : flexΦ m (k : ℝ) (c : ℝ) base t (Rv j) = base (Rv j) := by
          rw [flexΦ_Rv, flexVal_frozen hjne hjfz]
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (flexΦ m (k : ℝ) (c : ℝ) base t) = base (Rv j) := by
          simp only [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp]
          rw [hvalj]; ring
        rw [heval]
        have hcurve : (fun u => flexΦ m (k : ℝ) (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + base (Rv j) * u := by
          funext u; rw [flexΦ_Rv, flexVal_dfrozen hig hdr hjne hjfz]
        rw [hcurve]
        have h := ((hasDerivAt_id t).const_mul (base (Rv j))).const_add (base (Rv i))
        simp only [id, mul_one] at h
        exact h.hasDerivWithinAt
      · -- EXT 4b: contract other — its own exponential
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (flexΦ m (k : ℝ) (c : ℝ) base t)
            = (k' : ℝ) * ((c' : ℝ) - flexVal m (k : ℝ) (c : ℝ) base t i) := by
          simp [SettlingMode.fieldOf, hshc, CoordShape.field, Term.eval, AOp.interp]
        rw [heval]
        have hcurve : (fun u => flexΦ m (k : ℝ) (c : ℝ) base u (Rv i))
            = fun u => (c' : ℝ) + (base (Rv i) - (c' : ℝ)) * Real.exp (-((k' : ℝ) * u)) := by
          funext u; rw [flexΦ_Rv, flexVal_contract hig hshc]
        rw [hcurve]
        have hexp : HasDerivAt (fun u : ℝ => Real.exp (-((k' : ℝ) * u)))
            (-(k' : ℝ) * Real.exp (-((k' : ℝ) * t))) t := by
          have hinner : HasDerivAt (fun u : ℝ => -((k' : ℝ) * u)) (-(k' : ℝ)) t := by
            have h := (hasDerivAt_id t).const_mul (-(k' : ℝ))
            simp only [id, mul_one, neg_mul] at h
            exact h
          have h := (Real.hasDerivAt_exp (-((k' : ℝ) * t))).comp t hinner
          simp only [Function.comp_def] at h
          rw [mul_comm (Real.exp (-((k' : ℝ) * t))) (-(k' : ℝ))] at h
          exact h
        have h1 : HasDerivAt
            (fun u => (c' : ℝ) + (base (Rv i) - (c' : ℝ)) * Real.exp (-((k' : ℝ) * u)))
            ((base (Rv i) - (c' : ℝ)) * (-(k' : ℝ) * Real.exp (-((k' : ℝ) * t)))) t :=
          (hexp.const_mul (base (Rv i) - (c' : ℝ))).const_add (c' : ℝ)
        have heq : (base (Rv i) - (c' : ℝ)) * (-(k' : ℝ) * Real.exp (-((k' : ℝ) * t)))
            = (k' : ℝ) * ((c' : ℝ) - flexVal m (k : ℝ) (c : ℝ) base t i) := by
          rw [flexVal_contract hig hshc]; ring
        rw [← heq]
        exact h1.hasDerivWithinAt
      · -- EXT 4b: driven by a contract other — exp-integral curve, exponential driver
        have hvalj : flexΦ m (k : ℝ) (c : ℝ) base t (Rv j)
            = (cj : ℝ) + (base (Rv j) - (cj : ℝ)) * Real.exp (-((kj : ℝ) * t)) := by
          rw [flexΦ_Rv, flexVal_contract hjne hjc]
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (flexΦ m (k : ℝ) (c : ℝ) base t)
            = (cj : ℝ) + (base (Rv j) - (cj : ℝ)) * Real.exp (-((kj : ℝ) * t)) := by
          simp only [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp]
          rw [hvalj]; ring
        rw [heval]
        have hcurve : (fun u => flexΦ m (k : ℝ) (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + (cj : ℝ) * u
                + (base (Rv j) - (cj : ℝ)) * expInt (kj : ℝ) u := by
          funext u; rw [flexΦ_Rv, flexVal_dcontract hig hdr hjne hjc]
        rw [hcurve]
        have h1 : HasDerivAt (fun u : ℝ => base (Rv i) + (cj : ℝ) * u) (cj : ℝ) t := by
          have h := ((hasDerivAt_id t).const_mul (cj : ℝ)).const_add (base (Rv i))
          simpa using h
        have h2 : HasDerivAt
            (fun u : ℝ => (base (Rv j) - (cj : ℝ)) * expInt (kj : ℝ) u)
            ((base (Rv j) - (cj : ℝ)) * Real.exp (-((kj : ℝ) * t))) t :=
          (expInt_hasDeriv (kj : ℝ) t).const_mul (base (Rv j) - (cj : ℝ))
        have h := h1.add h2
        exact h.hasDerivWithinAt
  · -- mask
    intro t ht x hx
    refine flexΦ_nonR m (k : ℝ) (c : ℝ) base t ?_
    intro i hxi
    exact hx (by
      rw [hxi]
      simp only [rightBlock, ODESystem.bound, List.map_map]
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  · -- landing in the picked band
    rw [sat_GdOf hm2]
    refine ⟨hstayEnv _ hdt, ?_, ?_⟩
    · rw [hgc2, flexΦ_Rv]; exact hl1
    · rw [hgc2, flexΦ_Rv]; exact hl2




/-- CONST-RATE active coordinate with a NEGATIVE rate (EXT 1 — a Return mode), others frozen:
the affine witness, lower-side margin, landing in the covering band. -/
theorem settling_const_neg (M : SettlingModel n) {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m) {c : ℤ}
    (hsh : m.shapes m.gcoord = CoordShape.constRate c)
    (hfr : ∀ i, i ≠ m.gcoord → m.shapes i = CoordShape.frozen)
    (hc : c < 0)
    (hloMargin : ∀ l', (M.env m.gcoord).lo = some l' → l' ≤ m.glo + c * M.dt)
    (hhiIn : ∀ h', (M.env m.gcoord).hi = some h' → m.ghi ≤ h')
    (hland : (∃ q' ∈ q :: m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
        m'.glo ≤ m.glo + c * M.dt ∧ m.ghi + c * M.dt ≤ m'.ghi) ∨
      (∃ q' ∈ m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
        m.glo ≤ m'.ghi ∧ m'.glo ≤ m.glo + c * M.dt))
    (hdt : (0 : ℝ) ≤ (M.dt : ℝ)) :
    GuardSettlingB M.graph M.GdOf m.fieldOf (Term.const 1) M.envF ((M.dt : ℝ)) q := by
  intro base hb
  obtain ⟨henv, hblo, hbhi⟩ := (sat_GdOf hq).mp hb
  have hcR : ((c : ℤ) : ℝ) < 0 := by exact_mod_cast hc
  have hstayEnv : ∀ t, 0 ≤ t → t ≤ (M.dt : ℝ) →
      Formula.sat M.envF (affineΦ m.gcoord (c : ℝ) base t) := by
    intro t ht htd
    have hct0 : (c : ℝ) * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hcR) ht
    have hctd : (c : ℝ) * (M.dt : ℝ) ≤ (c : ℝ) * t := by nlinarith
    refine envF_update henv (fun x hx => affineΦ_other m.gcoord (c : ℝ) base t hx) ?_
    unfold Band.memR
    constructor
    · cases hcase : (M.env m.gcoord).lo with
      | none => trivial
      | some l =>
          have hlG : (l : ℝ) ≤ (m.glo : ℝ) + (c : ℝ) * (M.dt : ℝ) := by
            exact_mod_cast hloMargin l hcase
          show (l : ℝ) ≤ affineΦ m.gcoord (c : ℝ) base t (Rv m.gcoord)
          simp [affineΦ]
          linarith
    · cases hcase : (M.env m.gcoord).hi with
      | none => trivial
      | some h =>
          have hhG : (m.ghi : ℝ) ≤ (h : ℝ) := by exact_mod_cast hhiIn h hcase
          show affineΦ m.gcoord (c : ℝ) base t (Rv m.gcoord) ≤ (h : ℝ)
          simp [affineΦ]
          linarith
  have hpick : ∃ q' ∈ q :: M.graph.retainedSucc q, ∃ m', M.modes[q']? = some m' ∧
      m'.gcoord = m.gcoord ∧
      (m'.glo : ℝ) ≤ base (Rv m.gcoord) + (c : ℝ) * (M.dt : ℝ) ∧
      base (Rv m.gcoord) + (c : ℝ) * (M.dt : ℝ) ≤ (m'.ghi : ℝ) := by
    have hcd0 : (c : ℝ) * (M.dt : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt hcR) hdt
    rcases hland with ⟨q', hq'mem, m', hm', hgc', hcov1, hcov2⟩ | ⟨q', hq'mem, m', hm', hgc', hcv1, hcv2⟩
    · have h1 : (m'.glo : ℝ) ≤ (m.glo : ℝ) + (c : ℝ) * (M.dt : ℝ) := by exact_mod_cast hcov1
      have h2 : (m.ghi : ℝ) + (c : ℝ) * (M.dt : ℝ) ≤ (m'.ghi : ℝ) := by exact_mod_cast hcov2
      refine ⟨q', ?_, m', hm', hgc', by linarith, by linarith⟩
      rcases List.mem_cons.mp hq'mem with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (succ_mem_retained M hq h)
    · have h1 : (m.glo : ℝ) ≤ (m'.ghi : ℝ) := by exact_mod_cast hcv1
      have h2 : (m'.glo : ℝ) ≤ (m.glo : ℝ) + (c : ℝ) * (M.dt : ℝ) := by exact_mod_cast hcv2
      rcases le_or_gt (m.glo : ℝ) (base (Rv m.gcoord) + (c : ℝ) * (M.dt : ℝ)) with he | he
      · exact ⟨q, List.mem_cons_self .., m, hq, rfl, he, by linarith⟩
      · exact ⟨q', List.mem_cons_of_mem _ (succ_mem_retained M hq hq'mem), m', hm', hgc',
          by linarith, by linarith⟩
  obtain ⟨q', hq'ret, m', hm', hgc', hcov1R, hcov2R⟩ := hpick
  refine ⟨affineΦ m.gcoord (c : ℝ) base, ?_, ?_, ?_,
    fun t ht => hstayEnv t ht.1 ht.2, q', hq'ret, ?_⟩
  · funext x
    by_cases hx : x = Rv m.gcoord
    · subst hx; simp [affineΦ]
    · exact affineΦ_other m.gcoord (c : ℝ) base 0 hx
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hij : i = m.gcoord
    · rw [hij]
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf m.gcoord))
          (affineΦ m.gcoord (c : ℝ) base t) = (c : ℝ) := by
        simp [SettlingMode.fieldOf, hsh, CoordShape.field, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => affineΦ m.gcoord (c : ℝ) base u (Rv m.gcoord))
          = fun u => base (Rv m.gcoord) + (c : ℝ) * u := by
        funext u; simp [affineΦ]
      rw [hcurve]
      have h := ((hasDerivAt_id t).const_mul (c : ℝ)).const_add (base (Rv m.gcoord))
      simp only [id, mul_one] at h
      exact h.hasDerivWithinAt
    · have hfz : m.shapes i = CoordShape.frozen := hfr i hij
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
          (affineΦ m.gcoord (c : ℝ) base t) = 0 := by
        simp [SettlingMode.fieldOf, hfz, CoordShape.field, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => affineΦ m.gcoord (c : ℝ) base u (Rv i))
          = fun _ => base (Rv i) := by
        funext u
        exact affineΦ_other m.gcoord (c : ℝ) base u
          (fun hc' => hij (by simpa [Rv, Prod.ext_iff] using hc'))
      rw [hcurve]
      exact hasDerivWithinAt_const t _ _
  · intro t ht x hx
    have hxj : x ≠ Rv m.gcoord := by
      intro hcx; subst hcx
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map]
        exact List.mem_map.mpr ⟨m.gcoord, List.mem_finRange m.gcoord, rfl⟩)
    exact affineΦ_other m.gcoord (c : ℝ) base t hxj
  · rw [sat_GdOf hm']
    refine ⟨hstayEnv _ hdt le_rfl, ?_, ?_⟩
    · rw [hgc']
      show (m'.glo : ℝ) ≤ affineΦ m.gcoord (c : ℝ) base (M.dt : ℝ) (Rv m.gcoord)
      simp [affineΦ]
      linarith
    · rw [hgc']
      show affineΦ m.gcoord (c : ℝ) base (M.dt : ℝ) (Rv m.gcoord) ≤ (m'.ghi : ℝ)
      simp [affineΦ]
      linarith


/-- RATIONAL-GAIN (`contractQ`) variant: CONTRACT active coordinate (equilibrium in its own band), others frozen OR driven by it
(integrators with no upper envelope wall, nonneg band): the exponential/exp-integral witness. -/
theorem settling_contractQ_driven (M : SettlingModel n) {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m) {kn kd c : ℤ}
    (hsh : m.shapes m.gcoord = CoordShape.contractQ kn kd c)
    (hflex : FlexOthers M m)
    (hglo0 : 0 ≤ m.glo)
    (hkn : 0 ≤ kn) (hkd : 0 < kd) (hcl : m.glo ≤ c) (hch : c ≤ m.ghi)
    (hloIn : ∀ l', (M.env m.gcoord).lo = some l' → l' ≤ m.glo)
    (hhiIn : ∀ h', (M.env m.gcoord).hi = some h' → m.ghi ≤ h')
    (hdt : (0 : ℝ) ≤ (M.dt : ℝ)) :
    GuardSettlingB M.graph M.GdOf m.fieldOf (Term.const 1) M.envF ((M.dt : ℝ)) q := by
  intro base hb
  obtain ⟨henv, hblo, hbhi⟩ := (sat_GdOf hq).mp hb
  have hkdR : (0 : ℝ) < (kd : ℝ) := by exact_mod_cast hkd
  have hkR0 : (0 : ℝ) ≤ (kn : ℝ) / (kd : ℝ) :=
    div_nonneg (by exact_mod_cast hkn) hkdR.le
  have hclR : (m.glo : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcl
  have hchR : (c : ℝ) ≤ (m.ghi : ℝ) := by exact_mod_cast hch
  have hglo0R : (0 : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hglo0
  -- the active coordinate's value and its band, for all t ≥ 0
  have hval_g : ∀ t, drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t m.gcoord
      = (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)) := by
    intro t; unfold drivenValC; rw [if_pos rfl]
  have hband : ∀ t, 0 ≤ t →
      (m.glo : ℝ) ≤ drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t m.gcoord
      ∧ drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t m.gcoord ≤ (m.ghi : ℝ) := by
    intro t ht
    have hθpos : 0 < Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)) := Real.exp_pos _
    have hθle : Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    rw [hval_g]
    constructor
    · rcases le_or_gt (c : ℝ) (base (Rv m.gcoord)) with hbc | hbc
      · nlinarith
      · nlinarith
    · rcases le_or_gt (c : ℝ) (base (Rv m.gcoord)) with hbc | hbc
      · nlinarith
      · nlinarith
  -- staying in the envelope
  have hstayEnv : ∀ t, 0 ≤ t → Formula.sat M.envF (drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t) := by
    intro t ht
    rw [sat_envF]
    intro i
    rw [drivenΦC_Rv]
    by_cases hig : i = m.gcoord
    · rw [hig]
      obtain ⟨h1, h2⟩ := hband t ht
      unfold Band.memR
      constructor
      · cases hcase : (M.env m.gcoord).lo with
        | none => trivial
        | some l =>
            have hlG : (l : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hloIn l hcase
            linarith
      · cases hcase : (M.env m.gcoord).hi with
        | none => trivial
        | some h =>
            have hhG : (m.ghi : ℝ) ≤ (h : ℝ) := by exact_mod_cast hhiIn h hcase
            linarith
    · rcases hflex i hig with hfz | ⟨hdr, hhi⟩ | ⟨j, hdr, hjne, -, hlo, hhi⟩
      · rw [drivenValC_frozen hig hfz]
        exact (sat_envF.mp henv) i
      · rw [drivenValC_dactive hig hdr]
        have hbe := (sat_envF.mp henv) i
        unfold Band.memR at hbe ⊢
        rcases hbe with ⟨hbl, hbh⟩
        -- the integral of the (nonneg) active value is nonneg:
        -- c·t + (b_g − c)·expInt ≥ min(b_g, c)·t ≥ glo·t ≥ 0
        have hEI0 : 0 ≤ expInt ((kn : ℝ) / (kd : ℝ)) t := expInt_nonneg hkR0 ht
        have hEIt : expInt ((kn : ℝ) / (kd : ℝ)) t ≤ t := expInt_le hkR0 ht
        have hint : 0 ≤ (c : ℝ) * t + (base (Rv m.gcoord) - (c : ℝ)) * expInt ((kn : ℝ) / (kd : ℝ)) t := by
          rcases le_or_gt (c : ℝ) (base (Rv m.gcoord)) with hbc | hbc
          · nlinarith
          · nlinarith
        constructor
        · cases hcase : (M.env i).lo with
          | none => trivial
          | some l =>
              rw [hcase] at hbl
              show (l : ℝ) ≤ base (Rv i) + (c : ℝ) * t
                + (base (Rv m.gcoord) - (c : ℝ)) * expInt ((kn : ℝ) / (kd : ℝ)) t
              linarith
        · rw [hhi]; trivial
      · -- EXT 2: envelope-free coordinate
        rw [drivenValC_dfrozen hig hdr hjne]
        unfold Band.memR
        rw [hlo, hhi]
        exact ⟨trivial, trivial⟩
  have hstayGd : ∀ t, 0 ≤ t →
      Formula.sat (M.GdOf q) (drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t) := by
    intro t ht
    rw [sat_GdOf hq]
    obtain ⟨h1, h2⟩ := hband t ht
    exact ⟨hstayEnv t ht, by rw [drivenΦC_Rv]; exact h1, by rw [drivenΦC_Rv]; exact h2⟩
  refine ⟨drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base, ?_, ?_, ?_,
    fun t ht => hstayEnv t ht.1, q, List.mem_cons_self .., hstayGd _ hdt⟩
  · -- t = 0 recovers the base
    funext x
    obtain ⟨sd, ix⟩ := x
    cases sd with
    | R =>
        show drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base 0 ix = base (Rv ix)
        unfold drivenValC
        by_cases hig : ix = m.gcoord
        · rw [if_pos hig]
          subst hig
          simp
        · rw [if_neg hig]
          rcases hshx : m.shapes ix with _ | _ | _ | _ <;> simp [expInt]
    | L => rfl
    | Aux => rfl
  · -- derivatives
    intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hig : i = m.gcoord
    · rw [hig]
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf m.gcoord))
          (drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t)
          = ((kn : ℝ) / (kd : ℝ)) * ((c : ℝ) - drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t m.gcoord) := by
        simp [SettlingMode.fieldOf, hsh, CoordShape.field, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base u (Rv m.gcoord))
          = fun u => (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * u)) := by
        funext u; rw [drivenΦC_Rv, hval_g]
      rw [hcurve]
      -- derivative of the contract closed form (the banked pattern)
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (-(((kn : ℝ) / (kd : ℝ)) * u)))
          (-((kn : ℝ) / (kd : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t))) t := by
        have hinner : HasDerivAt (fun u : ℝ => -(((kn : ℝ) / (kd : ℝ)) * u)) (-((kn : ℝ) / (kd : ℝ))) t := by
          have h := (hasDerivAt_id t).const_mul (-((kn : ℝ) / (kd : ℝ)))
          simp only [id, mul_one, neg_mul] at h
          exact h
        have h := (Real.hasDerivAt_exp (-(((kn : ℝ) / (kd : ℝ)) * t))).comp t hinner
        simp only [Function.comp_def] at h
        rw [mul_comm (Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t))) (-((kn : ℝ) / (kd : ℝ)))] at h
        exact h
      have h1 : HasDerivAt
          (fun u => (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * u)))
          ((base (Rv m.gcoord) - (c : ℝ)) * (-((kn : ℝ) / (kd : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)))) t :=
        (hexp.const_mul (base (Rv m.gcoord) - (c : ℝ))).const_add (c : ℝ)
      have heq : (base (Rv m.gcoord) - (c : ℝ)) * (-((kn : ℝ) / (kd : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)))
          = ((kn : ℝ) / (kd : ℝ)) * ((c : ℝ) - drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t m.gcoord) := by
        rw [hval_g]; ring
      rw [← heq]
      exact h1.hasDerivWithinAt
    · rcases hflex i hig with hfz | ⟨hdr, -⟩ | ⟨j, hdr, hjne, hjfz, -, -⟩
      · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t) = 0 := by
          simp [SettlingMode.fieldOf, hfz, CoordShape.field, Term.eval, AOp.interp]
        rw [heval]
        have hcurve : (fun u => drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base u (Rv i))
            = fun _ => base (Rv i) := by
          funext u; rw [drivenΦC_Rv, drivenValC_frozen hig hfz]
        rw [hcurve]
        exact hasDerivWithinAt_const t _ _
      · -- driven: derivative = the CURRENT value of the active coordinate
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t)
            = (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)) := by
          simp [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp,
            drivenΦC_Rv, hval_g]
        rw [heval]
        have hcurve : (fun u => drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + (c : ℝ) * u
                + (base (Rv m.gcoord) - (c : ℝ)) * expInt ((kn : ℝ) / (kd : ℝ)) u := by
          funext u; rw [drivenΦC_Rv, drivenValC_dactive hig hdr]
        rw [hcurve]
        have h1 : HasDerivAt (fun u : ℝ => base (Rv i) + (c : ℝ) * u) (c : ℝ) t := by
          have h := ((hasDerivAt_id t).const_mul (c : ℝ)).const_add (base (Rv i))
          simpa using h
        have h2 : HasDerivAt
            (fun u : ℝ => (base (Rv m.gcoord) - (c : ℝ)) * expInt ((kn : ℝ) / (kd : ℝ)) u)
            ((base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t))) t :=
          (expInt_hasDeriv ((kn : ℝ) / (kd : ℝ)) t).const_mul (base (Rv m.gcoord) - (c : ℝ))
        have h := h1.add h2
        exact h.hasDerivWithinAt
      · -- EXT 2: driven by a frozen non-active coordinate — linear curve, constant driver
        have hvalj : drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t (Rv j) = base (Rv j) := by
          rw [drivenΦC_Rv, drivenValC_frozen hjne hjfz]
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t) = base (Rv j) := by
          simp only [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp]
          rw [hvalj]; ring
        rw [heval]
        have hcurve : (fun u => drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + base (Rv j) * u := by
          funext u; rw [drivenΦC_Rv, drivenValC_dfrozen hig hdr hjne]
        rw [hcurve]
        have h := ((hasDerivAt_id t).const_mul (base (Rv j))).const_add (base (Rv i))
        simp only [id, mul_one] at h
        exact h.hasDerivWithinAt
  · -- mask
    intro t ht x hx
    refine drivenΦC_nonR m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t ?_
    intro i hxi
    exact hx (by
      rw [hxi]
      simp only [rightBlock, ODESystem.bound, List.map_map]
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)


/-- RATIONAL-GAIN (`contractQ`) variant of EXT 4: CONTRACT active coordinate with the equilibrium ABOVE its own band — a transit-up
mode; the flow stays in the hull `[glo, c]` and lands in the own band or the covering
successor band (endpoint case-split). -/
theorem settling_contractQ_above (M : SettlingModel n) {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m) {kn kd c : ℤ}
    (hsh : m.shapes m.gcoord = CoordShape.contractQ kn kd c)
    (hflex : FlexOthers M m)
    (hglo0 : 0 ≤ m.glo)
    (hkn : 0 ≤ kn) (hkd : 0 < kd) (hch : m.ghi < c)
    (hloIn : ∀ l', (M.env m.gcoord).lo = some l' → l' ≤ m.glo)
    (hEnvHi : ∀ h', (M.env m.gcoord).hi = some h' → c ≤ h')
    (hcover : ∃ q' ∈ m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
        m'.glo ≤ m.ghi ∧ m.ghi * kd + (c - m.ghi) * (kn * M.dt) ≤ m'.ghi * kd)
    (hdt : (0 : ℝ) ≤ (M.dt : ℝ)) :
    GuardSettlingB M.graph M.GdOf m.fieldOf (Term.const 1) M.envF ((M.dt : ℝ)) q := by
  intro base hb
  obtain ⟨henv, hblo, hbhi⟩ := (sat_GdOf hq).mp hb
  have hkdR : (0 : ℝ) < (kd : ℝ) := by exact_mod_cast hkd
  have hkR0 : (0 : ℝ) ≤ (kn : ℝ) / (kd : ℝ) :=
    div_nonneg (by exact_mod_cast hkn) hkdR.le
  have hchR : (m.ghi : ℝ) < (c : ℝ) := by exact_mod_cast hch
  have hglo0R : (0 : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hglo0
  -- the active coordinate's value and its band, for all t ≥ 0
  have hval_g : ∀ t, drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t m.gcoord
      = (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)) := by
    intro t; unfold drivenValC; rw [if_pos rfl]
  -- the flow stays in the hull [base, c] ⊆ [glo, c] (base below the equilibrium)
  have hband : ∀ t, 0 ≤ t →
      base (Rv m.gcoord) ≤ drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t m.gcoord
      ∧ drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t m.gcoord ≤ (c : ℝ) := by
    intro t ht
    have hθpos : 0 < Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)) := Real.exp_pos _
    have hθle : Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have hbc : base (Rv m.gcoord) < (c : ℝ) := lt_of_le_of_lt hbhi hchR
    rw [hval_g]
    constructor
    · nlinarith
    · nlinarith
  -- staying in the envelope
  have hstayEnv : ∀ t, 0 ≤ t → Formula.sat M.envF (drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t) := by
    intro t ht
    rw [sat_envF]
    intro i
    rw [drivenΦC_Rv]
    by_cases hig : i = m.gcoord
    · rw [hig]
      obtain ⟨h1, h2⟩ := hband t ht
      unfold Band.memR
      constructor
      · cases hcase : (M.env m.gcoord).lo with
        | none => trivial
        | some l =>
            have hlG : (l : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hloIn l hcase
            -- value ≥ base ≥ glo ≥ l
            linarith
      · cases hcase : (M.env m.gcoord).hi with
        | none => trivial
        | some h =>
            have hhG : (c : ℝ) ≤ (h : ℝ) := by exact_mod_cast hEnvHi h hcase
            linarith
    · rcases hflex i hig with hfz | ⟨hdr, hhi⟩ | ⟨j, hdr, hjne, -, hlo, hhi⟩
      · rw [drivenValC_frozen hig hfz]
        exact (sat_envF.mp henv) i
      · rw [drivenValC_dactive hig hdr]
        have hbe := (sat_envF.mp henv) i
        unfold Band.memR at hbe ⊢
        rcases hbe with ⟨hbl, hbh⟩
        -- the integral of the (nonneg) active value is nonneg:
        -- c·t + (b_g − c)·expInt ≥ min(b_g, c)·t ≥ glo·t ≥ 0
        have hEI0 : 0 ≤ expInt ((kn : ℝ) / (kd : ℝ)) t := expInt_nonneg hkR0 ht
        have hEIt : expInt ((kn : ℝ) / (kd : ℝ)) t ≤ t := expInt_le hkR0 ht
        have hint : 0 ≤ (c : ℝ) * t + (base (Rv m.gcoord) - (c : ℝ)) * expInt ((kn : ℝ) / (kd : ℝ)) t := by
          rcases le_or_gt (c : ℝ) (base (Rv m.gcoord)) with hbc | hbc
          · nlinarith
          · nlinarith
        constructor
        · cases hcase : (M.env i).lo with
          | none => trivial
          | some l =>
              rw [hcase] at hbl
              show (l : ℝ) ≤ base (Rv i) + (c : ℝ) * t
                + (base (Rv m.gcoord) - (c : ℝ)) * expInt ((kn : ℝ) / (kd : ℝ)) t
              linarith
        · rw [hhi]; trivial
      · -- EXT 2: envelope-free coordinate
        rw [drivenValC_dfrozen hig hdr hjne]
        unfold Band.memR
        rw [hlo, hhi]
        exact ⟨trivial, trivial⟩
  -- landing: the own band, or the covering successor, chosen by the endpoint
  obtain ⟨q', hq'mem, m', hm', hgc', hcv1, hcv2⟩ := hcover
  have hcv1R : (m'.glo : ℝ) ≤ (m.ghi : ℝ) := by exact_mod_cast hcv1
  have hcv2R : (m.ghi : ℝ) * (kd : ℝ) + ((c : ℝ) - (m.ghi : ℝ)) * ((kn : ℝ) * (M.dt : ℝ))
      ≤ (m'.ghi : ℝ) * (kd : ℝ) := by exact_mod_cast hcv2
  -- the sharpened landing cap: endpoint ≤ ghi + (c − ghi)·(kn/kd)·dt ≤ m'.ghi, by 1 − e⁻ˣ ≤ x
  have hθdt : 1 - Real.exp (-(((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ)))
      ≤ ((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ) := by
    have h := Real.add_one_le_exp (-(((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ)))
    linarith
  have hcap : drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base (M.dt : ℝ) m.gcoord
      ≤ (m'.ghi : ℝ) := by
    have hθpos : 0 < Real.exp (-(((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ))) := Real.exp_pos _
    have hchR' : (0 : ℝ) < (c : ℝ) - (m.ghi : ℝ) := by linarith
    have e3' : ((c : ℝ) - (m.ghi : ℝ)) * (1 - Real.exp (-(((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ))))
        ≤ ((c : ℝ) - (m.ghi : ℝ)) * (((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ)) :=
      mul_le_mul_of_nonneg_left hθdt hchR'.le
    have e3 := mul_le_mul_of_nonneg_right e3' hkdR.le
    have e1 : ((c : ℝ) + (base (Rv m.gcoord) - (c : ℝ))
          * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ)))) * (kd : ℝ)
        ≤ ((c : ℝ) + ((m.ghi : ℝ) - (c : ℝ))
          * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ)))) * (kd : ℝ) := by
      nlinarith [mul_pos hθpos hkdR, hbhi]
    have e4 : ((c : ℝ) - (m.ghi : ℝ)) * (((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ)) * (kd : ℝ)
        = ((c : ℝ) - (m.ghi : ℝ)) * ((kn : ℝ) * (M.dt : ℝ)) := by
      field_simp
    have key : ((c : ℝ) + (base (Rv m.gcoord) - (c : ℝ))
          * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ)))) * (kd : ℝ)
        ≤ (m'.ghi : ℝ) * (kd : ℝ) := by nlinarith [e1, e3, e4, hcv2R]
    have hdiv := le_of_mul_le_mul_right key hkdR
    rw [hval_g]; exact hdiv
  have hpick : ∃ q2 ∈ q :: M.graph.retainedSucc q, ∃ m2, M.modes[q2]? = some m2 ∧
      m2.gcoord = m.gcoord ∧
      (m2.glo : ℝ) ≤ drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base (M.dt : ℝ) m.gcoord ∧
      drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base (M.dt : ℝ) m.gcoord ≤ (m2.ghi : ℝ) := by
    obtain ⟨he1, he2⟩ := hband (M.dt : ℝ) hdt
    rcases le_or_gt (drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base (M.dt : ℝ) m.gcoord) (m.ghi : ℝ)
      with he | he
    · exact ⟨q, List.mem_cons_self .., m, hq, rfl, by linarith, he⟩
    · exact ⟨q', List.mem_cons_of_mem _ (succ_mem_retained M hq hq'mem), m', hm', hgc',
        by linarith, hcap⟩
  obtain ⟨q2, hq2ret, m2, hm2, hgc2, hl1, hl2⟩ := hpick
  refine ⟨drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base, ?_, ?_, ?_,
    fun t ht => hstayEnv t ht.1, q2, hq2ret, ?_⟩
  · -- t = 0 recovers the base
    funext x
    obtain ⟨sd, ix⟩ := x
    cases sd with
    | R =>
        show drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base 0 ix = base (Rv ix)
        unfold drivenValC
        by_cases hig : ix = m.gcoord
        · rw [if_pos hig]
          subst hig
          simp
        · rw [if_neg hig]
          rcases hshx : m.shapes ix with _ | _ | _ | _ <;> simp [expInt]
    | L => rfl
    | Aux => rfl
  · -- derivatives
    intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hig : i = m.gcoord
    · rw [hig]
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf m.gcoord))
          (drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t)
          = ((kn : ℝ) / (kd : ℝ)) * ((c : ℝ) - drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t m.gcoord) := by
        simp [SettlingMode.fieldOf, hsh, CoordShape.field, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base u (Rv m.gcoord))
          = fun u => (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * u)) := by
        funext u; rw [drivenΦC_Rv, hval_g]
      rw [hcurve]
      -- derivative of the contract closed form (the banked pattern)
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (-(((kn : ℝ) / (kd : ℝ)) * u)))
          (-((kn : ℝ) / (kd : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t))) t := by
        have hinner : HasDerivAt (fun u : ℝ => -(((kn : ℝ) / (kd : ℝ)) * u)) (-((kn : ℝ) / (kd : ℝ))) t := by
          have h := (hasDerivAt_id t).const_mul (-((kn : ℝ) / (kd : ℝ)))
          simp only [id, mul_one, neg_mul] at h
          exact h
        have h := (Real.hasDerivAt_exp (-(((kn : ℝ) / (kd : ℝ)) * t))).comp t hinner
        simp only [Function.comp_def] at h
        rw [mul_comm (Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t))) (-((kn : ℝ) / (kd : ℝ)))] at h
        exact h
      have h1 : HasDerivAt
          (fun u => (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * u)))
          ((base (Rv m.gcoord) - (c : ℝ)) * (-((kn : ℝ) / (kd : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)))) t :=
        (hexp.const_mul (base (Rv m.gcoord) - (c : ℝ))).const_add (c : ℝ)
      have heq : (base (Rv m.gcoord) - (c : ℝ)) * (-((kn : ℝ) / (kd : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)))
          = ((kn : ℝ) / (kd : ℝ)) * ((c : ℝ) - drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t m.gcoord) := by
        rw [hval_g]; ring
      rw [← heq]
      exact h1.hasDerivWithinAt
    · rcases hflex i hig with hfz | ⟨hdr, -⟩ | ⟨j, hdr, hjne, hjfz, -, -⟩
      · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t) = 0 := by
          simp [SettlingMode.fieldOf, hfz, CoordShape.field, Term.eval, AOp.interp]
        rw [heval]
        have hcurve : (fun u => drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base u (Rv i))
            = fun _ => base (Rv i) := by
          funext u; rw [drivenΦC_Rv, drivenValC_frozen hig hfz]
        rw [hcurve]
        exact hasDerivWithinAt_const t _ _
      · -- driven: derivative = the CURRENT value of the active coordinate
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t)
            = (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)) := by
          simp [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp,
            drivenΦC_Rv, hval_g]
        rw [heval]
        have hcurve : (fun u => drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + (c : ℝ) * u
                + (base (Rv m.gcoord) - (c : ℝ)) * expInt ((kn : ℝ) / (kd : ℝ)) u := by
          funext u; rw [drivenΦC_Rv, drivenValC_dactive hig hdr]
        rw [hcurve]
        have h1 : HasDerivAt (fun u : ℝ => base (Rv i) + (c : ℝ) * u) (c : ℝ) t := by
          have h := ((hasDerivAt_id t).const_mul (c : ℝ)).const_add (base (Rv i))
          simpa using h
        have h2 : HasDerivAt
            (fun u : ℝ => (base (Rv m.gcoord) - (c : ℝ)) * expInt ((kn : ℝ) / (kd : ℝ)) u)
            ((base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t))) t :=
          (expInt_hasDeriv ((kn : ℝ) / (kd : ℝ)) t).const_mul (base (Rv m.gcoord) - (c : ℝ))
        have h := h1.add h2
        exact h.hasDerivWithinAt
      · -- EXT 2: driven by a frozen non-active coordinate — linear curve, constant driver
        have hvalj : drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t (Rv j) = base (Rv j) := by
          rw [drivenΦC_Rv, drivenValC_frozen hjne hjfz]
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t) = base (Rv j) := by
          simp only [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp]
          rw [hvalj]; ring
        rw [heval]
        have hcurve : (fun u => drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + base (Rv j) * u := by
          funext u; rw [drivenΦC_Rv, drivenValC_dfrozen hig hdr hjne]
        rw [hcurve]
        have h := ((hasDerivAt_id t).const_mul (base (Rv j))).const_add (base (Rv i))
        simp only [id, mul_one] at h
        exact h.hasDerivWithinAt
  · -- mask
    intro t ht x hx
    refine drivenΦC_nonR m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t ?_
    intro i hxi
    exact hx (by
      rw [hxi]
      simp only [rightBlock, ODESystem.bound, List.map_map]
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  · -- landing in the picked band
    rw [sat_GdOf hm2]
    refine ⟨hstayEnv _ hdt, ?_, ?_⟩
    · rw [hgc2, drivenΦC_Rv]; exact hl1
    · rw [hgc2, drivenΦC_Rv]; exact hl2



/-- RATIONAL-GAIN (`contractQ`) variant of EXT 4: CONTRACT active coordinate with the equilibrium BELOW its own band — a transit-down
mode (a drain); the flow stays in the hull `[c, ghi]` and lands in the own band or the
covering successor band (endpoint case-split). `0 ≤ c` keeps driven integrators monotone. -/
theorem settling_contractQ_below (M : SettlingModel n) {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m) {kn kd c : ℤ}
    (hsh : m.shapes m.gcoord = CoordShape.contractQ kn kd c)
    (hflex : FlexOthers M m)
    (hglo0 : 0 ≤ m.glo)
    (hkn : 0 ≤ kn) (hkd : 0 < kd) (hcl : c < m.glo) (hc0 : 0 ≤ c)
    (hEnvLo : ∀ l', (M.env m.gcoord).lo = some l' → l' ≤ c)
    (hhiIn : ∀ h', (M.env m.gcoord).hi = some h' → m.ghi ≤ h')
    (hcover : ∃ q' ∈ m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
        m.glo ≤ m'.ghi ∧ m'.glo * kd ≤ m.glo * kd - (m.glo - c) * (kn * M.dt))
    (hdt : (0 : ℝ) ≤ (M.dt : ℝ)) :
    GuardSettlingB M.graph M.GdOf m.fieldOf (Term.const 1) M.envF ((M.dt : ℝ)) q := by
  intro base hb
  obtain ⟨henv, hblo, hbhi⟩ := (sat_GdOf hq).mp hb
  have hkdR : (0 : ℝ) < (kd : ℝ) := by exact_mod_cast hkd
  have hkR0 : (0 : ℝ) ≤ (kn : ℝ) / (kd : ℝ) :=
    div_nonneg (by exact_mod_cast hkn) hkdR.le
  have hclR : (c : ℝ) < (m.glo : ℝ) := by exact_mod_cast hcl
  have hglo0R : (0 : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hglo0
  -- the active coordinate's value and its band, for all t ≥ 0
  have hval_g : ∀ t, drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t m.gcoord
      = (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)) := by
    intro t; unfold drivenValC; rw [if_pos rfl]
  -- the flow stays in the hull [c, base] ⊆ [c, ghi] (base above the equilibrium)
  have hband : ∀ t, 0 ≤ t →
      (c : ℝ) ≤ drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t m.gcoord
      ∧ drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t m.gcoord ≤ base (Rv m.gcoord) := by
    intro t ht
    have hθpos : 0 < Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)) := Real.exp_pos _
    have hθle : Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have hbc : (c : ℝ) < base (Rv m.gcoord) := lt_of_lt_of_le hclR hblo
    rw [hval_g]
    constructor
    · nlinarith
    · nlinarith
  -- staying in the envelope
  have hstayEnv : ∀ t, 0 ≤ t → Formula.sat M.envF (drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t) := by
    intro t ht
    rw [sat_envF]
    intro i
    rw [drivenΦC_Rv]
    by_cases hig : i = m.gcoord
    · rw [hig]
      obtain ⟨h1, h2⟩ := hband t ht
      unfold Band.memR
      constructor
      · cases hcase : (M.env m.gcoord).lo with
        | none => trivial
        | some l =>
            have hlG : (l : ℝ) ≤ (c : ℝ) := by exact_mod_cast hEnvLo l hcase
            linarith
      · cases hcase : (M.env m.gcoord).hi with
        | none => trivial
        | some h =>
            have hhG : (m.ghi : ℝ) ≤ (h : ℝ) := by exact_mod_cast hhiIn h hcase
            linarith
    · rcases hflex i hig with hfz | ⟨hdr, hhi⟩ | ⟨j, hdr, hjne, -, hlo, hhi⟩
      · rw [drivenValC_frozen hig hfz]
        exact (sat_envF.mp henv) i
      · rw [drivenValC_dactive hig hdr]
        have hbe := (sat_envF.mp henv) i
        unfold Band.memR at hbe ⊢
        rcases hbe with ⟨hbl, hbh⟩
        -- the integral of the (nonneg) active value is nonneg:
        -- c·t + (b_g − c)·expInt ≥ min(b_g, c)·t ≥ glo·t ≥ 0
        have hEI0 : 0 ≤ expInt ((kn : ℝ) / (kd : ℝ)) t := expInt_nonneg hkR0 ht
        have hEIt : expInt ((kn : ℝ) / (kd : ℝ)) t ≤ t := expInt_le hkR0 ht
        have hc0R : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc0
        have hint : 0 ≤ (c : ℝ) * t + (base (Rv m.gcoord) - (c : ℝ)) * expInt ((kn : ℝ) / (kd : ℝ)) t := by
          have hbc : (c : ℝ) ≤ base (Rv m.gcoord) := le_of_lt (lt_of_lt_of_le hclR hblo)
          nlinarith
        constructor
        · cases hcase : (M.env i).lo with
          | none => trivial
          | some l =>
              rw [hcase] at hbl
              show (l : ℝ) ≤ base (Rv i) + (c : ℝ) * t
                + (base (Rv m.gcoord) - (c : ℝ)) * expInt ((kn : ℝ) / (kd : ℝ)) t
              linarith
        · rw [hhi]; trivial
      · -- EXT 2: envelope-free coordinate
        rw [drivenValC_dfrozen hig hdr hjne]
        unfold Band.memR
        rw [hlo, hhi]
        exact ⟨trivial, trivial⟩
  -- landing: the own band, or the covering successor, chosen by the endpoint
  obtain ⟨q', hq'mem, m', hm', hgc', hcv1, hcv2⟩ := hcover
  have hcv1R : (m.glo : ℝ) ≤ (m'.ghi : ℝ) := by exact_mod_cast hcv1
  have hcv2R : (m'.glo : ℝ) * (kd : ℝ)
      ≤ (m.glo : ℝ) * (kd : ℝ) - ((m.glo : ℝ) - (c : ℝ)) * ((kn : ℝ) * (M.dt : ℝ)) := by
    exact_mod_cast hcv2
  -- the sharpened landing floor: endpoint ≥ glo − (glo − c)·(kn/kd)·dt ≥ m'.glo, by 1 − e⁻ˣ ≤ x
  have hθdt : 1 - Real.exp (-(((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ)))
      ≤ ((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ) := by
    have h := Real.add_one_le_exp (-(((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ)))
    linarith
  have hcap : (m'.glo : ℝ)
      ≤ drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base (M.dt : ℝ) m.gcoord := by
    have hθpos : 0 < Real.exp (-(((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ))) := Real.exp_pos _
    have hclR' : (0 : ℝ) < (m.glo : ℝ) - (c : ℝ) := by linarith
    have e3' : ((m.glo : ℝ) - (c : ℝ)) * (1 - Real.exp (-(((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ))))
        ≤ ((m.glo : ℝ) - (c : ℝ)) * (((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ)) :=
      mul_le_mul_of_nonneg_left hθdt hclR'.le
    have e3 := mul_le_mul_of_nonneg_right e3' hkdR.le
    have e1 : ((c : ℝ) + ((m.glo : ℝ) - (c : ℝ))
          * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ)))) * (kd : ℝ)
        ≤ ((c : ℝ) + (base (Rv m.gcoord) - (c : ℝ))
          * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ)))) * (kd : ℝ) := by
      nlinarith [mul_pos hθpos hkdR, hblo]
    have e4 : ((m.glo : ℝ) - (c : ℝ)) * (((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ)) * (kd : ℝ)
        = ((m.glo : ℝ) - (c : ℝ)) * ((kn : ℝ) * (M.dt : ℝ)) := by
      field_simp
    have key : (m'.glo : ℝ) * (kd : ℝ)
        ≤ ((c : ℝ) + (base (Rv m.gcoord) - (c : ℝ))
          * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * (M.dt : ℝ)))) * (kd : ℝ) := by
      nlinarith [e1, e3, e4, hcv2R]
    have hdiv := le_of_mul_le_mul_right key hkdR
    rw [hval_g]; exact hdiv
  have hpick : ∃ q2 ∈ q :: M.graph.retainedSucc q, ∃ m2, M.modes[q2]? = some m2 ∧
      m2.gcoord = m.gcoord ∧
      (m2.glo : ℝ) ≤ drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base (M.dt : ℝ) m.gcoord ∧
      drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base (M.dt : ℝ) m.gcoord ≤ (m2.ghi : ℝ) := by
    obtain ⟨he1, he2⟩ := hband (M.dt : ℝ) hdt
    rcases le_or_gt (m.glo : ℝ) (drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base (M.dt : ℝ) m.gcoord)
      with he | he
    · exact ⟨q, List.mem_cons_self .., m, hq, rfl, he, by linarith⟩
    · exact ⟨q', List.mem_cons_of_mem _ (succ_mem_retained M hq hq'mem), m', hm', hgc',
        hcap, by linarith⟩
  obtain ⟨q2, hq2ret, m2, hm2, hgc2, hl1, hl2⟩ := hpick
  refine ⟨drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base, ?_, ?_, ?_,
    fun t ht => hstayEnv t ht.1, q2, hq2ret, ?_⟩
  · -- t = 0 recovers the base
    funext x
    obtain ⟨sd, ix⟩ := x
    cases sd with
    | R =>
        show drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base 0 ix = base (Rv ix)
        unfold drivenValC
        by_cases hig : ix = m.gcoord
        · rw [if_pos hig]
          subst hig
          simp
        · rw [if_neg hig]
          rcases hshx : m.shapes ix with _ | _ | _ | _ <;> simp [expInt]
    | L => rfl
    | Aux => rfl
  · -- derivatives
    intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hig : i = m.gcoord
    · rw [hig]
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf m.gcoord))
          (drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t)
          = ((kn : ℝ) / (kd : ℝ)) * ((c : ℝ) - drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t m.gcoord) := by
        simp [SettlingMode.fieldOf, hsh, CoordShape.field, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base u (Rv m.gcoord))
          = fun u => (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * u)) := by
        funext u; rw [drivenΦC_Rv, hval_g]
      rw [hcurve]
      -- derivative of the contract closed form (the banked pattern)
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (-(((kn : ℝ) / (kd : ℝ)) * u)))
          (-((kn : ℝ) / (kd : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t))) t := by
        have hinner : HasDerivAt (fun u : ℝ => -(((kn : ℝ) / (kd : ℝ)) * u)) (-((kn : ℝ) / (kd : ℝ))) t := by
          have h := (hasDerivAt_id t).const_mul (-((kn : ℝ) / (kd : ℝ)))
          simp only [id, mul_one, neg_mul] at h
          exact h
        have h := (Real.hasDerivAt_exp (-(((kn : ℝ) / (kd : ℝ)) * t))).comp t hinner
        simp only [Function.comp_def] at h
        rw [mul_comm (Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t))) (-((kn : ℝ) / (kd : ℝ)))] at h
        exact h
      have h1 : HasDerivAt
          (fun u => (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * u)))
          ((base (Rv m.gcoord) - (c : ℝ)) * (-((kn : ℝ) / (kd : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)))) t :=
        (hexp.const_mul (base (Rv m.gcoord) - (c : ℝ))).const_add (c : ℝ)
      have heq : (base (Rv m.gcoord) - (c : ℝ)) * (-((kn : ℝ) / (kd : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)))
          = ((kn : ℝ) / (kd : ℝ)) * ((c : ℝ) - drivenValC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t m.gcoord) := by
        rw [hval_g]; ring
      rw [← heq]
      exact h1.hasDerivWithinAt
    · rcases hflex i hig with hfz | ⟨hdr, -⟩ | ⟨j, hdr, hjne, hjfz, -, -⟩
      · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t) = 0 := by
          simp [SettlingMode.fieldOf, hfz, CoordShape.field, Term.eval, AOp.interp]
        rw [heval]
        have hcurve : (fun u => drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base u (Rv i))
            = fun _ => base (Rv i) := by
          funext u; rw [drivenΦC_Rv, drivenValC_frozen hig hfz]
        rw [hcurve]
        exact hasDerivWithinAt_const t _ _
      · -- driven: derivative = the CURRENT value of the active coordinate
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t)
            = (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)) := by
          simp [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp,
            drivenΦC_Rv, hval_g]
        rw [heval]
        have hcurve : (fun u => drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + (c : ℝ) * u
                + (base (Rv m.gcoord) - (c : ℝ)) * expInt ((kn : ℝ) / (kd : ℝ)) u := by
          funext u; rw [drivenΦC_Rv, drivenValC_dactive hig hdr]
        rw [hcurve]
        have h1 : HasDerivAt (fun u : ℝ => base (Rv i) + (c : ℝ) * u) (c : ℝ) t := by
          have h := ((hasDerivAt_id t).const_mul (c : ℝ)).const_add (base (Rv i))
          simpa using h
        have h2 : HasDerivAt
            (fun u : ℝ => (base (Rv m.gcoord) - (c : ℝ)) * expInt ((kn : ℝ) / (kd : ℝ)) u)
            ((base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t))) t :=
          (expInt_hasDeriv ((kn : ℝ) / (kd : ℝ)) t).const_mul (base (Rv m.gcoord) - (c : ℝ))
        have h := h1.add h2
        exact h.hasDerivWithinAt
      · -- EXT 2: driven by a frozen non-active coordinate — linear curve, constant driver
        have hvalj : drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t (Rv j) = base (Rv j) := by
          rw [drivenΦC_Rv, drivenValC_frozen hjne hjfz]
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t) = base (Rv j) := by
          simp only [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp]
          rw [hvalj]; ring
        rw [heval]
        have hcurve : (fun u => drivenΦC m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + base (Rv j) * u := by
          funext u; rw [drivenΦC_Rv, drivenValC_dfrozen hig hdr hjne]
        rw [hcurve]
        have h := ((hasDerivAt_id t).const_mul (base (Rv j))).const_add (base (Rv i))
        simp only [id, mul_one] at h
        exact h.hasDerivWithinAt
  · -- mask
    intro t ht x hx
    refine drivenΦC_nonR m ((kn : ℝ) / (kd : ℝ)) (c : ℝ) base t ?_
    intro i hxi
    exact hx (by
      rw [hxi]
      simp only [rightBlock, ODESystem.bound, List.map_map]
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  · -- landing in the picked band
    rw [sat_GdOf hm2]
    refine ⟨hstayEnv _ hdt, ?_, ?_⟩
    · rw [hgc2, drivenΦC_Rv]; exact hl1
    · rw [hgc2, drivenΦC_Rv]; exact hl2

/-! ### EXT P — the coupled-pair discharge (weakly coupled symmetric linear pair)

`p' = c − p + ε·q`, `q' = c − q + ε·p` (ε = h/1000 < 1/3) diagonalizes by `u = p + q`,
`w = p − q` into contractions with rates `1 ∓ ε`, so `p(t) = p* + A·e^{−r₁t} + B·e^{−r₂t}`
with `p* = c/(1−ε)`, `A = (u₀ − 2p*)/2`, `B = w₀/2`. The two-exponential is bounded by pure
algebra: with `y = e^{−r₁t}` and `z = e^{−r₂t}`, monotonicity gives `y² ≤ z ≤ y` (using
`r₁ ≤ r₂ ≤ 2r₁`), and a quadratic-vertex case analysis closes `p ≤ T` from just three
rational facts — `p* ≤ T`, `p(0) ≤ T`, and `A ≤ 2(T − p*)`. The same lemma applied to the
negated data gives every lower bound and every `q`-bound (whose coefficients are `(A, −B)`).
-/

/-- `1 + x + x²/2 ≤ eˣ` for `x ≥ 0` (monotonicity from `add_one_le_exp`). -/
theorem quadExp (x : ℝ) (hx : 0 ≤ x) : 1 + x + x ^ 2 / 2 ≤ Real.exp x := by
  have hD : ∀ y : ℝ, HasDerivAt (fun z => Real.exp z - (1 + z + z ^ 2 / 2))
      (Real.exp y - (1 + y)) y := by
    intro y
    have h1 := Real.hasDerivAt_exp y
    have h2 : HasDerivAt (fun z : ℝ => 1 + z + z ^ 2 / 2) (1 + y) y := by
      have ha : HasDerivAt (fun z : ℝ => z ^ 2 / 2) y y := by
        have hp := (hasDerivAt_pow 2 y).div_const 2
        have : ((2 : ℕ) : ℝ) * y ^ (2 - 1) / 2 = y := by push_cast; ring
        rw [this] at hp
        exact hp
      have hb : HasDerivAt (fun z : ℝ => 1 + z) 1 y := by
        simpa using (hasDerivAt_id y).const_add (1 : ℝ)
      exact hb.add ha
    exact h1.sub h2
  have hmono : MonotoneOn (fun z => Real.exp z - (1 + z + z ^ 2 / 2)) (Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
    · exact fun y _ => (hD y).continuousAt.continuousWithinAt
    · exact fun y _ => (hD y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hD y).deriv]
      have := Real.add_one_le_exp y
      linarith
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) x := ⟨le_refl _, hx⟩
  have hxm : x ∈ Icc (0 : ℝ) x := ⟨hx, le_refl _⟩
  have := hmono h0 hxm hx
  simp only [Real.exp_zero] at this
  linarith

/-- The poly-exponential bound: `(a + b·t)e^{−gt} ≤ T` for `t ≥ 0`, from `a ≤ T`, `0 ≤ T`
and either linear dominance (`b ≤ gT`) or the quadratic discriminant certificate. -/
theorem polyExp_le (a b g T t : ℝ) (hg : 0 < g) (ht : 0 ≤ t) (hT : 0 ≤ T) (ha : a ≤ T)
    (hbr : b ≤ g * T ∨ (g * T - b) ^ 2 ≤ 2 * T * g ^ 2 * (T - a)) :
    (a + b * t) * Real.exp (-(g * t)) ≤ T := by
  have hexp := quadExp (g * t) (by positivity)
  have he : (0 : ℝ) < Real.exp (g * t) := Real.exp_pos _
  have key : a + b * t ≤ T * Real.exp (g * t) := by
    have hTq : T * (1 + g * t + (g * t) ^ 2 / 2) ≤ T * Real.exp (g * t) :=
      mul_le_mul_of_nonneg_left hexp hT
    have hQ : 0 ≤ (T - a) + (g * T - b) * t + T * g ^ 2 * t ^ 2 / 2 := by
      rcases hbr with hb | hd
      · have h1 : 0 ≤ (g * T - b) * t := mul_nonneg (by linarith) ht
        have h2 : 0 ≤ T * g ^ 2 * t ^ 2 / 2 := by positivity
        linarith
      · rcases eq_or_lt_of_le hT with rfl | hT'
        · -- degenerate target: the discriminant condition forces `b = 0`
          have hb0 : b = 0 := by
            have hb2 : b ^ 2 = 0 := le_antisymm (by nlinarith [hd]) (sq_nonneg b)
            exact pow_eq_zero_iff two_ne_zero |>.mp hb2
          subst hb0
          nlinarith [ha]
        · have h2 : 0 ≤ 2 * T * g ^ 2 *
              ((T - a) + (g * T - b) * t + T * g ^ 2 * t ^ 2 / 2) := by
            nlinarith [sq_nonneg (T * g ^ 2 * t + (g * T - b)), hd]
          have hpos : 0 < 2 * T * g ^ 2 := by positivity
          nlinarith [h2, hpos]
    nlinarith [hQ, hTq]
  have hrw : (a + b * t) * Real.exp (-(g * t)) = (a + b * t) / Real.exp (g * t) := by
    rw [Real.exp_neg]
    ring
  rw [hrw, div_le_iff₀ he]
  linarith [key]

/-! ## Poly-exponential antiderivatives (EXT 4c dampers)

Closed forms of `∫₀ᵗ uⁱ e^{−mu} du` for `i = 1, 2` (nonzero rate `m`): the cascade
damper's square `((p + w·u)e^{−gu})²` expands into `uⁱ e^{−2gu}` and `uⁱ e^{−(k+2g)u}`
terms, so the damped position still integrates in closed form. -/

/-- `∫₀ᵗ u·e^{−mu} du` for `m ≠ 0`. -/
noncomputable def polyExpInt₁ (m t : ℝ) : ℝ :=
  (1 - (1 + m * t) * Real.exp (-(m * t))) / m ^ 2

/-- `∫₀ᵗ u²·e^{−mu} du` for `m ≠ 0`. -/
noncomputable def polyExpInt₂ (m t : ℝ) : ℝ :=
  (2 - (2 + 2 * m * t + m ^ 2 * t ^ 2) * Real.exp (-(m * t))) / m ^ 3

theorem expNeg_hasDeriv (m t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (-(m * u))) (-m * Real.exp (-(m * t))) t := by
  have hinner : HasDerivAt (fun u : ℝ => -(m * u)) (-m) t := by
    have h := (hasDerivAt_id t).const_mul (-m)
    simp only [id, mul_one, neg_mul] at h
    exact h
  have h := (Real.hasDerivAt_exp (-(m * t))).comp t hinner
  simp only [Function.comp_def] at h
  rw [mul_comm (Real.exp (-(m * t))) (-m)] at h
  exact h

theorem polyExpInt₁_hasDeriv {m : ℝ} (hm : m ≠ 0) (t : ℝ) :
    HasDerivAt (fun u => polyExpInt₁ m u) (t * Real.exp (-(m * t))) t := by
  unfold polyExpInt₁
  have hpoly : HasDerivAt (fun u : ℝ => 1 + m * u) m t := by
    simpa using ((hasDerivAt_id t).const_mul m).const_add 1
  have h := ((hpoly.mul (expNeg_hasDeriv m t)).const_sub 1).div_const (m ^ 2)
  have heq : -(m * Real.exp (-(m * t)) + (1 + m * t) * (-m * Real.exp (-(m * t)))) / m ^ 2
      = t * Real.exp (-(m * t)) := by
    field_simp
    ring
  rw [← heq]
  exact h

theorem polyExpInt₂_hasDeriv {m : ℝ} (hm : m ≠ 0) (t : ℝ) :
    HasDerivAt (fun u => polyExpInt₂ m u) (t ^ 2 * Real.exp (-(m * t))) t := by
  unfold polyExpInt₂
  have hpoly : HasDerivAt (fun u : ℝ => 2 + 2 * m * u + m ^ 2 * u ^ 2)
      (2 * m + m ^ 2 * (2 * t)) t := by
    have h1 : HasDerivAt (fun u : ℝ => 2 + 2 * m * u) (2 * m) t := by
      simpa using ((hasDerivAt_id t).const_mul (2 * m)).const_add 2
    have h2 : HasDerivAt (fun u : ℝ => m ^ 2 * u ^ 2) (m ^ 2 * (2 * t)) t := by
      have hp := (hasDerivAt_pow 2 t).const_mul (m ^ 2)
      have hc : ((2 : ℕ) : ℝ) * t ^ (2 - 1) = 2 * t := by push_cast; ring
      rw [hc] at hp
      exact hp
    exact h1.add h2
  have h := ((hpoly.mul (expNeg_hasDeriv m t)).const_sub 2).div_const (m ^ 3)
  have heq : -((2 * m + m ^ 2 * (2 * t)) * Real.exp (-(m * t))
        + (2 + 2 * m * t + m ^ 2 * t ^ 2) * (-m * Real.exp (-(m * t)))) / m ^ 3
      = t ^ 2 * Real.exp (-(m * t)) := by
    field_simp
    ring
  rw [← heq]
  exact h

@[simp] theorem polyExpInt₁_zero (m : ℝ) : polyExpInt₁ m 0 = 0 := by
  simp [polyExpInt₁]

@[simp] theorem polyExpInt₂_zero (m : ℝ) : polyExpInt₂ m 0 = 0 := by
  simp [polyExpInt₂]

/-! ## EXT G — the chase GUARD coordinate (critically damped guard blocks)

`x_g' = x_j − k·x_g` with the driver `x_j` a contract-to-`c` coordinate at the SAME rate:
the eigen-cascade chart of a critically damped `(λ+k)²` block whose position carries the
guard bands (endurance_orderlift_2to3's order-2 intermediate model). Value
`v* + (A + B·t)e^{−kt}` with `v* = c/k`, `A = v₀ − v*`, `B = u₀ − c` — non-monotone (a dip
below the band or an overshoot above it), so the mode's one-step image is bounded by
`polyExp_le` on both sides and lands in a CHAIN of up to two bands per side (the pair
cover: a far band holding the staying bound, a near band bridging it to the own band). -/

/-- Per-coordinate value of the chase-guard witness: chase active (`v* + (A + Bt)e^{−kt}`),
integrators driven by it pick up the `polyExpInt₁` term, other shapes as in `flexVal`. -/
noncomputable def chaseGVal (m : SettlingMode n) (jd : Fin n) (kR cR : ℝ)
    (base : State (Var n)) (t : ℝ) (i : Fin n) : ℝ :=
  if i = m.gcoord then
    cR / kR + (base (Rv i) - cR / kR + (base (Rv jd) - cR) * t) * Real.exp (-(kR * t))
  else match m.shapes i with
    | CoordShape.driven j =>
        if j = m.gcoord then
          base (Rv i) + (cR / kR) * t + (base (Rv m.gcoord) - cR / kR) * expInt kR t
            + (base (Rv jd) - cR) * polyExpInt₁ kR t
        else match m.shapes j with
          | CoordShape.contract kj cj =>
              base (Rv i) + (cj : ℝ) * t + (base (Rv j) - (cj : ℝ)) * expInt (kj : ℝ) t
          | _ => base (Rv i) + base (Rv j) * t
    | CoordShape.contract k' c' =>
        (c' : ℝ) + (base (Rv i) - (c' : ℝ)) * Real.exp (-((k' : ℝ) * t))
    | _ => base (Rv i)

/-- The chase-guard witness flow. -/
noncomputable def chaseGΦ (m : SettlingMode n) (jd : Fin n) (kR cR : ℝ)
    (base : State (Var n)) (t : ℝ) : State (Var n) :=
  fun x => match x with
    | (Side.R, i) => chaseGVal m jd kR cR base t i
    | _ => base x

@[simp] theorem chaseGΦ_Rv (m : SettlingMode n) (jd : Fin n) (kR cR : ℝ)
    (base : State (Var n)) (t : ℝ) (i : Fin n) :
    chaseGΦ m jd kR cR base t (Rv i) = chaseGVal m jd kR cR base t i := rfl

theorem chaseGΦ_nonR (m : SettlingMode n) (jd : Fin n) (kR cR : ℝ) (base : State (Var n))
    (t : ℝ) {x : Var n} (hx : ∀ i : Fin n, x ≠ Rv i) : chaseGΦ m jd kR cR base t x = base x := by
  obtain ⟨sd, ix⟩ := x
  cases sd with
  | R => exact absurd rfl (hx ix)
  | L => rfl
  | Aux => rfl

theorem chaseGVal_g {m : SettlingMode n} {jd : Fin n} {kR cR : ℝ} {base : State (Var n)}
    {t : ℝ} :
    chaseGVal m jd kR cR base t m.gcoord
      = cR / kR + (base (Rv m.gcoord) - cR / kR + (base (Rv jd) - cR) * t)
          * Real.exp (-(kR * t)) := by
  simp [chaseGVal]

theorem chaseGVal_frozen {m : SettlingMode n} {jd : Fin n} {kR cR : ℝ}
    {base : State (Var n)} {t : ℝ} {i : Fin n} (hig : i ≠ m.gcoord)
    (hfz : m.shapes i = CoordShape.frozen) :
    chaseGVal m jd kR cR base t i = base (Rv i) := by
  simp [chaseGVal, hig, hfz]

theorem chaseGVal_dactive {m : SettlingMode n} {jd : Fin n} {kR cR : ℝ}
    {base : State (Var n)} {t : ℝ} {i : Fin n} (hig : i ≠ m.gcoord)
    (hdr : m.shapes i = CoordShape.driven m.gcoord) :
    chaseGVal m jd kR cR base t i
      = base (Rv i) + (cR / kR) * t + (base (Rv m.gcoord) - cR / kR) * expInt kR t
          + (base (Rv jd) - cR) * polyExpInt₁ kR t := by
  simp [chaseGVal, hig, hdr]

theorem chaseGVal_dfrozen {m : SettlingMode n} {jd : Fin n} {kR cR : ℝ}
    {base : State (Var n)} {t : ℝ} {i j : Fin n} (hig : i ≠ m.gcoord)
    (hdr : m.shapes i = CoordShape.driven j) (hjne : j ≠ m.gcoord)
    (hjfz : m.shapes j = CoordShape.frozen) :
    chaseGVal m jd kR cR base t i = base (Rv i) + base (Rv j) * t := by
  simp [chaseGVal, hig, hdr, hjne, hjfz]

theorem chaseGVal_dcontract {m : SettlingMode n} {jd : Fin n} {kR cR : ℝ}
    {base : State (Var n)} {t : ℝ} {i j : Fin n} {kj cj : ℤ} (hig : i ≠ m.gcoord)
    (hdr : m.shapes i = CoordShape.driven j) (hjne : j ≠ m.gcoord)
    (hjc : m.shapes j = CoordShape.contract kj cj) :
    chaseGVal m jd kR cR base t i
      = base (Rv i) + (cj : ℝ) * t + (base (Rv j) - (cj : ℝ)) * expInt (kj : ℝ) t := by
  simp [chaseGVal, hig, hdr, hjne, hjc]

theorem chaseGVal_contract {m : SettlingMode n} {jd : Fin n} {kR cR : ℝ}
    {base : State (Var n)} {t : ℝ} {i : Fin n} {k' c' : ℤ} (hig : i ≠ m.gcoord)
    (hshc : m.shapes i = CoordShape.contract k' c') :
    chaseGVal m jd kR cR base t i
      = (c' : ℝ) + (base (Rv i) - (c' : ℝ)) * Real.exp (-((k' : ℝ) * t)) := by
  simp [chaseGVal, hig, hshc]

/-- One-sided staying bound for the chase value from CORNER data: the `A`-corner enters the
discriminant monotonically, and a `B` beyond the linear-dominance threshold is squeezed
between the threshold and its corner, so ONE corner discriminant suffices. -/
theorem chaseG_stay_upper {A Ah B Bh kR T : ℝ} (hk : 0 < kR) {t : ℝ} (ht : 0 ≤ t)
    (hT : 0 ≤ T) (hA : A ≤ Ah) (hAh : Ah ≤ T) (hBh : B ≤ Bh)
    (hbr : Bh ≤ kR * T ∨ (kR * T - Bh) ^ 2 ≤ 2 * T * kR ^ 2 * (T - Ah)) :
    (A + B * t) * Real.exp (-(kR * t)) ≤ T := by
  apply polyExp_le A B kR T t hk ht hT (le_trans hA hAh)
  rcases le_or_gt B (kR * T) with hbb | hbb
  · exact Or.inl hbb
  · refine Or.inr ?_
    rcases hbr with h1 | h2
    · exact absurd (le_trans hBh h1) (not_le.mpr hbb)
    · have h1' : -(Bh - kR * T) ≤ kR * T - B := by linarith
      have h2' : kR * T - B ≤ Bh - kR * T := by linarith
      have hx2 : (kR * T - B) ^ 2 ≤ (Bh - kR * T) ^ 2 := sq_le_sq' h1' h2'
      have hflip : (Bh - kR * T) ^ 2 = (kR * T - Bh) ^ 2 := by ring
      have h2T : (0 : ℝ) ≤ 2 * T * kR ^ 2 := by positivity
      have hDA : 2 * T * kR ^ 2 * (T - Ah) ≤ 2 * T * kR ^ 2 * (T - A) :=
        mul_le_mul_of_nonneg_left (by linarith) h2T
      calc (kR * T - B) ^ 2 ≤ (kR * T - Bh) ^ 2 := by rw [← hflip]; exact hx2
        _ ≤ 2 * T * kR ^ 2 * (T - Ah) := h2
        _ ≤ 2 * T * kR ^ 2 * (T - A) := hDA

/-- EXT G discharge: CHASE guard coordinate (`x_g' = x_j − k·x_g`, driver contract-to-`c`
at the same rate), others over the extended flex grammar. The value dips/overshoots, so
staying is `polyExp_le` on both sides against the PAIR covers' far bands, and landing
case-splits the endpoint through the near bands. -/
theorem settling_chaseG (M : SettlingModel n) {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m) {j : Fin n} {k c : ℤ}
    (hsh : m.shapes m.gcoord = CoordShape.chase j k)
    (hjg : j ≠ m.gcoord)
    (hjsh : m.shapes j = CoordShape.contract k c)
    (hk : 0 < k)
    (hflex : FlexOthersC M m)
    {ulo uhi : ℤ}
    (hjlo : (M.env j).lo = some ulo) (hjhi : (M.env j).hi = some uhi)
    (hcovLo : ∃ q1 ∈ q :: m.succs, ∃ m1, M.modes[q1]? = some m1 ∧ m1.gcoord = m.gcoord ∧
        m1.glo ≤ m.glo ∧ 0 ≤ m1.glo ∧ k * m1.glo ≤ c ∧
        (∀ l', (M.env m.gcoord).lo = some l' → l' ≤ m1.glo) ∧
        (k * m1.glo ≤ ulo ∨
          (ulo - k * m1.glo) ^ 2 ≤ 2 * (c - k * m1.glo) * (k * m.glo - k * m1.glo)) ∧
        ∃ q2 ∈ q :: m.succs, ∃ m2, M.modes[q2]? = some m2 ∧ m2.gcoord = m.gcoord ∧
          m2.glo ≤ m1.ghi ∧ m.glo ≤ m2.ghi)
    (hcovHi : ∃ q3 ∈ q :: m.succs, ∃ m3, M.modes[q3]? = some m3 ∧ m3.gcoord = m.gcoord ∧
        m.ghi ≤ m3.ghi ∧ c ≤ k * m3.ghi ∧
        (∀ h', (M.env m.gcoord).hi = some h' → m3.ghi ≤ h') ∧
        (uhi ≤ k * m3.ghi ∨
          (k * m3.ghi - uhi) ^ 2 ≤ 2 * (k * m3.ghi - c) * (k * m3.ghi - k * m.ghi)) ∧
        ∃ q4 ∈ q :: m.succs, ∃ m4, M.modes[q4]? = some m4 ∧ m4.gcoord = m.gcoord ∧
          m4.glo ≤ m.ghi ∧ m3.glo ≤ m4.ghi)
    (hdt : (0 : ℝ) ≤ (M.dt : ℝ)) :
    GuardSettlingB M.graph M.GdOf m.fieldOf (Term.const 1) M.envF ((M.dt : ℝ)) q := by
  intro base hb
  obtain ⟨henv, hblo, hbhi⟩ := (sat_GdOf hq).mp hb
  obtain ⟨q1, hq1mem, m1, hm1, hgc1, h1glo, h1nn, h1kc, hEnvLo1, hbr1,
    q2, hq2mem, m2, hm2, hgc2, h2a, h2b⟩ := hcovLo
  obtain ⟨q3, hq3mem, m3, hm3, hgc3, h3ghi, h3kc, hEnvHi3, hbr3,
    q4, hq4mem, m4, hm4, hgc4, h4a, h4b⟩ := hcovHi
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkR
  have hkc : (k : ℝ) * ((c : ℝ) / (k : ℝ)) = (c : ℝ) := mul_div_cancel₀ _ hk0
  -- the driver's base sits in its envelope band
  have hbj := (sat_envF.mp henv) j
  unfold Band.memR at hbj
  rw [hjlo, hjhi] at hbj
  obtain ⟨hbjl, hbjh⟩ := hbj
  have h1gloR : (m1.glo : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast h1glo
  have h1nnR : (0 : ℝ) ≤ (m1.glo : ℝ) := by exact_mod_cast h1nn
  have h3ghiR : (m.ghi : ℝ) ≤ (m3.ghi : ℝ) := by exact_mod_cast h3ghi
  -- the active value's closed form and its staying corridor [m1.glo, m3.ghi]
  have hband : ∀ t, 0 ≤ t →
      (m1.glo : ℝ) ≤ chaseGVal m j (k : ℝ) (c : ℝ) base t m.gcoord
      ∧ chaseGVal m j (k : ℝ) (c : ℝ) base t m.gcoord ≤ (m3.ghi : ℝ) := by
    intro t ht
    rw [chaseGVal_g]
    constructor
    · -- lower side: `polyExp_le` on the negated data, far band m1
      have h := chaseG_stay_upper (A := (c : ℝ) / (k : ℝ) - base (Rv m.gcoord))
          (Ah := (c : ℝ) / (k : ℝ) - (m.glo : ℝ)) (B := (c : ℝ) - base (Rv j))
          (Bh := (c : ℝ) - (ulo : ℝ)) (kR := (k : ℝ))
          (T := (c : ℝ) / (k : ℝ) - (m1.glo : ℝ)) hkR ht ?_ (by linarith) ?_ (by linarith) ?_
      · have hre : ((c : ℝ) / (k : ℝ) - base (Rv m.gcoord) + ((c : ℝ) - base (Rv j)) * t)
            * Real.exp (-((k : ℝ) * t))
            = -((base (Rv m.gcoord) - (c : ℝ) / (k : ℝ) + (base (Rv j) - (c : ℝ)) * t)
                * Real.exp (-((k : ℝ) * t))) := by ring
        rw [hre] at h
        linarith
      · rw [sub_nonneg, le_div_iff₀ hkR]
        have : (k : ℝ) * (m1.glo : ℝ) ≤ (c : ℝ) := by exact_mod_cast h1kc
        linarith
      · linarith
      · rcases hbr1 with h1 | h2
        · refine Or.inl ?_
          rw [show (k : ℝ) * ((c : ℝ) / (k : ℝ) - (m1.glo : ℝ))
              = (c : ℝ) - (k : ℝ) * (m1.glo : ℝ) by rw [mul_sub, hkc]]
          have : (k : ℝ) * (m1.glo : ℝ) ≤ (ulo : ℝ) := by exact_mod_cast h1
          linarith
        · refine Or.inr ?_
          have h2R : ((ulo : ℝ) - (k : ℝ) * (m1.glo : ℝ)) ^ 2
              ≤ 2 * ((c : ℝ) - (k : ℝ) * (m1.glo : ℝ))
                  * ((k : ℝ) * (m.glo : ℝ) - (k : ℝ) * (m1.glo : ℝ)) := by exact_mod_cast h2
          have hL : ((k : ℝ) * ((c : ℝ) / (k : ℝ) - (m1.glo : ℝ)) - ((c : ℝ) - (ulo : ℝ))) ^ 2
              = ((ulo : ℝ) - (k : ℝ) * (m1.glo : ℝ)) ^ 2 := by
            rw [mul_sub, hkc]; ring
          have hR : 2 * ((c : ℝ) / (k : ℝ) - (m1.glo : ℝ)) * (k : ℝ) ^ 2
                * (((c : ℝ) / (k : ℝ) - (m1.glo : ℝ)) - ((c : ℝ) / (k : ℝ) - (m.glo : ℝ)))
              = 2 * ((c : ℝ) - (k : ℝ) * (m1.glo : ℝ))
                  * ((k : ℝ) * (m.glo : ℝ) - (k : ℝ) * (m1.glo : ℝ)) := by
            field_simp
            ring
          rw [hL, hR]
          exact h2R
    · -- upper side: far band m3
      have h := chaseG_stay_upper (A := base (Rv m.gcoord) - (c : ℝ) / (k : ℝ))
          (Ah := (m.ghi : ℝ) - (c : ℝ) / (k : ℝ)) (B := base (Rv j) - (c : ℝ))
          (Bh := (uhi : ℝ) - (c : ℝ)) (kR := (k : ℝ))
          (T := (m3.ghi : ℝ) - (c : ℝ) / (k : ℝ)) hkR ht ?_ (by linarith) ?_ (by linarith) ?_
      · linarith
      · rw [sub_nonneg, div_le_iff₀ hkR]
        have : (c : ℝ) ≤ (k : ℝ) * (m3.ghi : ℝ) := by exact_mod_cast h3kc
        linarith
      · linarith
      · rcases hbr3 with h1 | h2
        · refine Or.inl ?_
          rw [show (k : ℝ) * ((m3.ghi : ℝ) - (c : ℝ) / (k : ℝ))
              = (k : ℝ) * (m3.ghi : ℝ) - (c : ℝ) by rw [mul_sub, hkc]]
          have : (uhi : ℝ) ≤ (k : ℝ) * (m3.ghi : ℝ) := by exact_mod_cast h1
          linarith
        · refine Or.inr ?_
          have h2R : ((k : ℝ) * (m3.ghi : ℝ) - (uhi : ℝ)) ^ 2
              ≤ 2 * ((k : ℝ) * (m3.ghi : ℝ) - (c : ℝ))
                  * ((k : ℝ) * (m3.ghi : ℝ) - (k : ℝ) * (m.ghi : ℝ)) := by exact_mod_cast h2
          have hL : ((k : ℝ) * ((m3.ghi : ℝ) - (c : ℝ) / (k : ℝ)) - ((uhi : ℝ) - (c : ℝ))) ^ 2
              = ((k : ℝ) * (m3.ghi : ℝ) - (uhi : ℝ)) ^ 2 := by
            rw [mul_sub, hkc]; ring
          have hR : 2 * ((m3.ghi : ℝ) - (c : ℝ) / (k : ℝ)) * (k : ℝ) ^ 2
                * (((m3.ghi : ℝ) - (c : ℝ) / (k : ℝ)) - ((m.ghi : ℝ) - (c : ℝ) / (k : ℝ)))
              = 2 * ((k : ℝ) * (m3.ghi : ℝ) - (c : ℝ))
                  * ((k : ℝ) * (m3.ghi : ℝ) - (k : ℝ) * (m.ghi : ℝ)) := by
            field_simp
            ring
          rw [hL, hR]
          exact h2R
  -- the integral of the active value (for driven integrators), with its derivative
  have hSder : ∀ u : ℝ, HasDerivAt (fun w => (c : ℝ) / (k : ℝ) * w
      + (base (Rv m.gcoord) - (c : ℝ) / (k : ℝ)) * expInt (k : ℝ) w
      + (base (Rv j) - (c : ℝ)) * polyExpInt₁ (k : ℝ) w)
      ((c : ℝ) / (k : ℝ) + (base (Rv m.gcoord) - (c : ℝ) / (k : ℝ)
        + (base (Rv j) - (c : ℝ)) * u) * Real.exp (-((k : ℝ) * u))) u := by
    intro u
    have h1 : HasDerivAt (fun w : ℝ => (c : ℝ) / (k : ℝ) * w) ((c : ℝ) / (k : ℝ)) u := by
      simpa using (hasDerivAt_id u).const_mul ((c : ℝ) / (k : ℝ))
    have h2 := (expInt_hasDeriv (k : ℝ) u).const_mul (base (Rv m.gcoord) - (c : ℝ) / (k : ℝ))
    have h3 := (polyExpInt₁_hasDeriv hk0 u).const_mul (base (Rv j) - (c : ℝ))
    have h := (h1.add h2).add h3
    have heq : (c : ℝ) / (k : ℝ)
        + (base (Rv m.gcoord) - (c : ℝ) / (k : ℝ)) * Real.exp (-((k : ℝ) * u))
        + (base (Rv j) - (c : ℝ)) * (u * Real.exp (-((k : ℝ) * u)))
        = (c : ℝ) / (k : ℝ) + (base (Rv m.gcoord) - (c : ℝ) / (k : ℝ)
            + (base (Rv j) - (c : ℝ)) * u) * Real.exp (-((k : ℝ) * u)) := by ring
    rw [← heq]
    exact h
  -- the integral is nonneg (the integrand sits above m1.glo ≥ 0)
  have hSint : ∀ t, 0 ≤ t → 0 ≤ (c : ℝ) / (k : ℝ) * t
      + (base (Rv m.gcoord) - (c : ℝ) / (k : ℝ)) * expInt (k : ℝ) t
      + (base (Rv j) - (c : ℝ)) * polyExpInt₁ (k : ℝ) t := by
    intro t ht
    have hmono : MonotoneOn (fun w => (c : ℝ) / (k : ℝ) * w
        + (base (Rv m.gcoord) - (c : ℝ) / (k : ℝ)) * expInt (k : ℝ) w
        + (base (Rv j) - (c : ℝ)) * polyExpInt₁ (k : ℝ) w) (Icc 0 t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
      · exact fun u _ => (hSder u).continuousAt.continuousWithinAt
      · exact fun u _ => (hSder u).differentiableAt.differentiableWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        rw [(hSder u).deriv]
        have hv := (hband u (le_of_lt hu.1)).1
        rw [chaseGVal_g] at hv
        linarith
    have h0m : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_refl _, ht⟩
    have htm : t ∈ Icc (0 : ℝ) t := ⟨ht, le_refl _⟩
    have := hmono h0m htm ht
    simpa [expInt] using this
  -- staying in the envelope
  have hstayEnv : ∀ t, 0 ≤ t →
      Formula.sat M.envF (chaseGΦ m j (k : ℝ) (c : ℝ) base t) := by
    intro t ht
    rw [sat_envF]
    intro i
    rw [chaseGΦ_Rv]
    by_cases hig : i = m.gcoord
    · rw [hig]
      obtain ⟨h1, h2⟩ := hband t ht
      unfold Band.memR
      constructor
      · cases hcase : (M.env m.gcoord).lo with
        | none => trivial
        | some l =>
            have hlG : (l : ℝ) ≤ (m1.glo : ℝ) := by exact_mod_cast hEnvLo1 l hcase
            linarith
      · cases hcase : (M.env m.gcoord).hi with
        | none => trivial
        | some h =>
            have hhG : (m3.ghi : ℝ) ≤ (h : ℝ) := by exact_mod_cast hEnvHi3 h hcase
            linarith
    · rcases hflex i hig with hfz | ⟨hdr, hhi⟩ | ⟨j2, hdr, hjne, hjfz, hlo, hhi⟩
        | ⟨k', c', hshc, hk', hloC, hhiC⟩ | ⟨j2, kj, cj, hdr, hjne, hjc, hlo, hhi⟩
      · rw [chaseGVal_frozen hig hfz]
        exact (sat_envF.mp henv) i
      · rw [chaseGVal_dactive hig hdr]
        have hbe := (sat_envF.mp henv) i
        unfold Band.memR at hbe ⊢
        rcases hbe with ⟨hbl, hbh⟩
        have hint := hSint t ht
        constructor
        · cases hcase : (M.env i).lo with
          | none => trivial
          | some l =>
              rw [hcase] at hbl
              show (l : ℝ) ≤ base (Rv i) + (c : ℝ) / (k : ℝ) * t
                + (base (Rv m.gcoord) - (c : ℝ) / (k : ℝ)) * expInt (k : ℝ) t
                + (base (Rv j) - (c : ℝ)) * polyExpInt₁ (k : ℝ) t
              linarith
        · rw [hhi]; trivial
      · rw [chaseGVal_dfrozen hig hdr hjne hjfz]
        unfold Band.memR
        rw [hlo, hhi]
        exact ⟨trivial, trivial⟩
      · have hk'R : (0 : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hk'
        have hθpos : 0 < Real.exp (-((k' : ℝ) * t)) := Real.exp_pos _
        have hθle : Real.exp (-((k' : ℝ) * t)) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith
        rw [chaseGVal_contract hig hshc]
        have hbe := (sat_envF.mp henv) i
        unfold Band.memR at hbe ⊢
        rcases hbe with ⟨hbl, hbh⟩
        constructor
        · cases hcase : (M.env i).lo with
          | none => trivial
          | some l =>
              rw [hcase] at hbl
              have hlc : (l : ℝ) ≤ (c' : ℝ) := by exact_mod_cast hloC l hcase
              nlinarith
        · cases hcase : (M.env i).hi with
          | none => trivial
          | some h =>
              rw [hcase] at hbh
              have hhc : (c' : ℝ) ≤ (h : ℝ) := by exact_mod_cast hhiC h hcase
              nlinarith
      · rw [chaseGVal_dcontract hig hdr hjne hjc]
        unfold Band.memR
        rw [hlo, hhi]
        exact ⟨trivial, trivial⟩
  -- landing: endpoint case-split through the pair covers
  have hmem : ∀ q' ∈ q :: m.succs, q' ∈ q :: M.graph.retainedSucc q := by
    intro q' hq'
    rcases List.mem_cons.mp hq' with rfl | hmem'
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (succ_mem_retained M hq hmem')
  have hpick : ∃ q5 ∈ q :: M.graph.retainedSucc q, ∃ m5, M.modes[q5]? = some m5 ∧
      m5.gcoord = m.gcoord ∧
      (m5.glo : ℝ) ≤ chaseGVal m j (k : ℝ) (c : ℝ) base (M.dt : ℝ) m.gcoord ∧
      chaseGVal m j (k : ℝ) (c : ℝ) base (M.dt : ℝ) m.gcoord ≤ (m5.ghi : ℝ) := by
    obtain ⟨hd1, hd2⟩ := hband (M.dt : ℝ) hdt
    rcases le_or_gt (chaseGVal m j (k : ℝ) (c : ℝ) base (M.dt : ℝ) m.gcoord) ((m.ghi : ℝ))
      with hup | hup
    · rcases le_or_gt ((m.glo : ℝ)) (chaseGVal m j (k : ℝ) (c : ℝ) base (M.dt : ℝ) m.gcoord)
        with hlo | hlo
      · exact ⟨q, List.mem_cons_self .., m, hq, rfl, hlo, hup⟩
      · rcases le_or_gt ((m2.glo : ℝ)) (chaseGVal m j (k : ℝ) (c : ℝ) base (M.dt : ℝ) m.gcoord)
          with h2c | h2c
        · have : (m.glo : ℝ) ≤ (m2.ghi : ℝ) := by exact_mod_cast h2b
          exact ⟨q2, hmem q2 hq2mem, m2, hm2, hgc2, h2c, by linarith⟩
        · have : (m2.glo : ℝ) ≤ (m1.ghi : ℝ) := by exact_mod_cast h2a
          exact ⟨q1, hmem q1 hq1mem, m1, hm1, hgc1, hd1, by linarith⟩
    · rcases le_or_gt (chaseGVal m j (k : ℝ) (c : ℝ) base (M.dt : ℝ) m.gcoord) ((m4.ghi : ℝ))
        with h4c | h4c
      · have : (m4.glo : ℝ) ≤ (m.ghi : ℝ) := by exact_mod_cast h4a
        exact ⟨q4, hmem q4 hq4mem, m4, hm4, hgc4, by linarith, h4c⟩
      · have : (m3.glo : ℝ) ≤ (m4.ghi : ℝ) := by exact_mod_cast h4b
        exact ⟨q3, hmem q3 hq3mem, m3, hm3, hgc3, by linarith, hd2⟩
  obtain ⟨q5, hq5ret, m5, hm5, hgc5, hl1, hl2⟩ := hpick
  refine ⟨chaseGΦ m j (k : ℝ) (c : ℝ) base, ?_, ?_, ?_,
    fun t ht => hstayEnv t ht.1, q5, hq5ret, ?_⟩
  · -- t = 0 recovers the base
    funext x
    obtain ⟨sd, ix⟩ := x
    cases sd with
    | R =>
        show chaseGVal m j (k : ℝ) (c : ℝ) base 0 ix = base (Rv ix)
        unfold chaseGVal
        by_cases hig : ix = m.gcoord
        · rw [if_pos hig]
          subst hig
          simp
        · rw [if_neg hig]
          rcases hshx : m.shapes ix with _ | _ | _ | _ | j2 | _ | _ | _ | _
          · simp
          · simp
          · simp
          · simp
          · by_cases hj2 : j2 = m.gcoord
            · simp [hj2, expInt]
            · rcases hshj : m.shapes j2 with _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
                simp [hj2, expInt] <;> (try rfl) <;> split <;> rfl
          · simp
          · simp
          · simp
          · simp
    | L => rfl
    | Aux => rfl
  · -- derivatives
    intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hig : i = m.gcoord
    · rw [hig]
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf m.gcoord))
          (chaseGΦ m j (k : ℝ) (c : ℝ) base t)
          = chaseGVal m j (k : ℝ) (c : ℝ) base t j
            - (k : ℝ) * chaseGVal m j (k : ℝ) (c : ℝ) base t m.gcoord := by
        simp [SettlingMode.fieldOf, hsh, CoordShape.field, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => chaseGΦ m j (k : ℝ) (c : ℝ) base u (Rv m.gcoord))
          = fun u => (c : ℝ) / (k : ℝ) + (base (Rv m.gcoord) - (c : ℝ) / (k : ℝ)
              + (base (Rv j) - (c : ℝ)) * u) * Real.exp (-((k : ℝ) * u)) := by
        funext u; rw [chaseGΦ_Rv, chaseGVal_g]
      rw [hcurve]
      have hlin : HasDerivAt (fun u : ℝ => base (Rv m.gcoord) - (c : ℝ) / (k : ℝ)
          + (base (Rv j) - (c : ℝ)) * u) (base (Rv j) - (c : ℝ)) t := by
        simpa using ((hasDerivAt_id t).const_mul (base (Rv j) - (c : ℝ))).const_add
          (base (Rv m.gcoord) - (c : ℝ) / (k : ℝ))
      have hexp := expNeg_hasDeriv (k : ℝ) t
      have h1 := (hlin.mul hexp).const_add ((c : ℝ) / (k : ℝ))
      have heq : (base (Rv j) - (c : ℝ)) * Real.exp (-((k : ℝ) * t))
          + (base (Rv m.gcoord) - (c : ℝ) / (k : ℝ) + (base (Rv j) - (c : ℝ)) * t)
            * (-(k : ℝ) * Real.exp (-((k : ℝ) * t)))
          = chaseGVal m j (k : ℝ) (c : ℝ) base t j
            - (k : ℝ) * chaseGVal m j (k : ℝ) (c : ℝ) base t m.gcoord := by
        rw [chaseGVal_g, chaseGVal_contract hjg hjsh]
        field_simp
        ring
      rw [← heq]
      exact h1.hasDerivWithinAt
    · rcases hflex i hig with hfz | ⟨hdr, -⟩ | ⟨j2, hdr, hjne, hjfz, -, -⟩
        | ⟨k', c', hshc, -, -, -⟩ | ⟨j2, kj, cj, hdr, hjne, hjc, -, -⟩
      · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (chaseGΦ m j (k : ℝ) (c : ℝ) base t) = 0 := by
          simp [SettlingMode.fieldOf, hfz, CoordShape.field, Term.eval, AOp.interp]
        rw [heval]
        have hcurve : (fun u => chaseGΦ m j (k : ℝ) (c : ℝ) base u (Rv i))
            = fun _ => base (Rv i) := by
          funext u; rw [chaseGΦ_Rv, chaseGVal_frozen hig hfz]
        rw [hcurve]
        exact hasDerivWithinAt_const t _ _
      · -- driven by the chase active: derivative = its current value
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (chaseGΦ m j (k : ℝ) (c : ℝ) base t)
            = (c : ℝ) / (k : ℝ) + (base (Rv m.gcoord) - (c : ℝ) / (k : ℝ)
                + (base (Rv j) - (c : ℝ)) * t) * Real.exp (-((k : ℝ) * t)) := by
          simp [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp,
            chaseGΦ_Rv, chaseGVal_g]
        rw [heval]
        have hcurve : (fun u => chaseGΦ m j (k : ℝ) (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + ((c : ℝ) / (k : ℝ) * u
                + (base (Rv m.gcoord) - (c : ℝ) / (k : ℝ)) * expInt (k : ℝ) u
                + (base (Rv j) - (c : ℝ)) * polyExpInt₁ (k : ℝ) u) := by
          funext u
          rw [chaseGΦ_Rv, chaseGVal_dactive hig hdr]
          ring
        rw [hcurve]
        exact ((hSder t).const_add (base (Rv i))).hasDerivWithinAt
      · have hvalj : chaseGΦ m j (k : ℝ) (c : ℝ) base t (Rv j2) = base (Rv j2) := by
          rw [chaseGΦ_Rv, chaseGVal_frozen hjne hjfz]
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (chaseGΦ m j (k : ℝ) (c : ℝ) base t) = base (Rv j2) := by
          simp only [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp]
          rw [hvalj]; ring
        rw [heval]
        have hcurve : (fun u => chaseGΦ m j (k : ℝ) (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + base (Rv j2) * u := by
          funext u; rw [chaseGΦ_Rv, chaseGVal_dfrozen hig hdr hjne hjfz]
        rw [hcurve]
        have h := ((hasDerivAt_id t).const_mul (base (Rv j2))).const_add (base (Rv i))
        simp only [id, mul_one] at h
        exact h.hasDerivWithinAt
      · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (chaseGΦ m j (k : ℝ) (c : ℝ) base t)
            = (k' : ℝ) * ((c' : ℝ) - chaseGVal m j (k : ℝ) (c : ℝ) base t i) := by
          simp [SettlingMode.fieldOf, hshc, CoordShape.field, Term.eval, AOp.interp]
        rw [heval]
        have hcurve : (fun u => chaseGΦ m j (k : ℝ) (c : ℝ) base u (Rv i))
            = fun u => (c' : ℝ) + (base (Rv i) - (c' : ℝ)) * Real.exp (-((k' : ℝ) * u)) := by
          funext u; rw [chaseGΦ_Rv, chaseGVal_contract hig hshc]
        rw [hcurve]
        have hexp := expNeg_hasDeriv (k' : ℝ) t
        have h1 : HasDerivAt
            (fun u => (c' : ℝ) + (base (Rv i) - (c' : ℝ)) * Real.exp (-((k' : ℝ) * u)))
            ((base (Rv i) - (c' : ℝ)) * (-(k' : ℝ) * Real.exp (-((k' : ℝ) * t)))) t :=
          (hexp.const_mul (base (Rv i) - (c' : ℝ))).const_add (c' : ℝ)
        have heq : (base (Rv i) - (c' : ℝ)) * (-(k' : ℝ) * Real.exp (-((k' : ℝ) * t)))
            = (k' : ℝ) * ((c' : ℝ) - chaseGVal m j (k : ℝ) (c : ℝ) base t i) := by
          rw [chaseGVal_contract hig hshc]; ring
        rw [← heq]
        exact h1.hasDerivWithinAt
      · have hvalj : chaseGΦ m j (k : ℝ) (c : ℝ) base t (Rv j2)
            = (cj : ℝ) + (base (Rv j2) - (cj : ℝ)) * Real.exp (-((kj : ℝ) * t)) := by
          rw [chaseGΦ_Rv, chaseGVal_contract hjne hjc]
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (chaseGΦ m j (k : ℝ) (c : ℝ) base t)
            = (cj : ℝ) + (base (Rv j2) - (cj : ℝ)) * Real.exp (-((kj : ℝ) * t)) := by
          simp only [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp]
          rw [hvalj]; ring
        rw [heval]
        have hcurve : (fun u => chaseGΦ m j (k : ℝ) (c : ℝ) base u (Rv i))
            = fun u => base (Rv i) + (cj : ℝ) * u
                + (base (Rv j2) - (cj : ℝ)) * expInt (kj : ℝ) u := by
          funext u; rw [chaseGΦ_Rv, chaseGVal_dcontract hig hdr hjne hjc]
        rw [hcurve]
        have h1 : HasDerivAt (fun u : ℝ => base (Rv i) + (cj : ℝ) * u) (cj : ℝ) t := by
          have h := ((hasDerivAt_id t).const_mul (cj : ℝ)).const_add (base (Rv i))
          simpa using h
        have h2 : HasDerivAt
            (fun u : ℝ => (base (Rv j2) - (cj : ℝ)) * expInt (kj : ℝ) u)
            ((base (Rv j2) - (cj : ℝ)) * Real.exp (-((kj : ℝ) * t))) t :=
          (expInt_hasDeriv (kj : ℝ) t).const_mul (base (Rv j2) - (cj : ℝ))
        exact (h1.add h2).hasDerivWithinAt
  · -- mask
    intro t ht x hx
    refine chaseGΦ_nonR m j (k : ℝ) (c : ℝ) base t ?_
    intro i hxi
    exact hx (by
      rw [hxi]
      simp only [rightBlock, ODESystem.bound, List.map_map]
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  · -- landing in the picked band
    rw [sat_GdOf hm5]
    refine ⟨hstayEnv _ hdt, ?_, ?_⟩
    · rw [hgc5, chaseGΦ_Rv]; exact hl1
    · rw [hgc5, chaseGΦ_Rv]; exact hl2

/-- The two-exponential bound: `p* + A·e^{−r₁t} + B·e^{−r₂t} ≤ T` for `t ≥ 0`, given
`0 < r₁ ≤ r₂ ≤ 2r₁` and the three rational facts. -/
theorem twoExp_le (pstar A B r1 r2 T t : ℝ)
    (hr1 : 0 < r1) (hr12 : r1 ≤ r2) (hr2 : r2 ≤ 2 * r1) (ht : 0 ≤ t)
    (hpT : pstar ≤ T) (hp0 : pstar + A + B ≤ T) (hAT : A ≤ 2 * (T - pstar)) :
    pstar + A * Real.exp (-(r1 * t)) + B * Real.exp (-(r2 * t)) ≤ T := by
  set y := Real.exp (-(r1 * t)) with hydef
  set z := Real.exp (-(r2 * t)) with hzdef
  have hy0 : 0 < y := Real.exp_pos _
  have hy1 : y ≤ 1 := by
    rw [hydef, Real.exp_le_one_iff]
    nlinarith
  have hzy : z ≤ y := by
    rw [hydef, hzdef]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hyz : y ^ 2 ≤ z := by
    rw [hydef, hzdef, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  rcases le_total 0 B with hB | hB
  · -- B ≥ 0: both exponentials bounded by y, linear in y
    have hle : A * y + B * z ≤ (A + B) * y := by nlinarith
    rcases le_total 0 (A + B) with hAB | hAB
    · nlinarith
    · nlinarith
  · -- B ≤ 0: z ≥ y², so B·z ≤ B·y² and the quadratic vertex analysis applies
    have hle : A * y + B * z ≤ A * y + B * y ^ 2 := by nlinarith
    rcases le_total A 0 with hA | hA
    · -- A ≤ 0: the quadratic is nonpositive
      nlinarith
    · rcases le_total A (2 * (-B)) with hAB | hAB
      · -- vertex inside: (2(−B)y − A)² ≥ 0 plus A² ≤ 4(−B)(T − p*)
        -- (from A ≤ 2(−B) and A ≤ 2(T − p*)) assemble 4(−B)·(T − p* − Ay − By²) ≥ 0
        have hTp : (0 : ℝ) ≤ T - pstar := by linarith
        have hA2 : A * A ≤ (2 * (-B)) * (2 * (T - pstar)) :=
          mul_le_mul hAB hAT hA (by linarith)
        rcases eq_or_lt_of_le hB with hB0 | hB0
        · have hA0 : A = 0 := le_antisymm (by linarith) hA
          nlinarith
        · have expand : 4 * (-B) * (T - pstar - (A * y + B * y ^ 2))
              = (2 * (-B) * y - A) ^ 2 - A * A + 4 * (-B) * (T - pstar) := by
            ring
          have hpos : 0 ≤ 4 * (-B) * (T - pstar - (A * y + B * y ^ 2)) := by
            rw [expand]
            nlinarith [sq_nonneg (2 * (-B) * y - A), hA2]
          have hBpos : (0 : ℝ) < -B := by linarith
          nlinarith [hpos, hBpos, hle]
      · -- vertex beyond 1: increasing on [0, 1], so the value at y = 1 caps it
        have hkey : 0 ≤ (1 - y) * (-(B * (1 + y)) - A) → True := fun _ => trivial
        nlinarith [mul_nonneg (sub_nonneg.mpr hy1) (by nlinarith : (0 : ℝ) ≤ B * (1 + y) + A)]

/-- Per-coordinate value of the pair witness (`ps`, `A`, `B`, rates computed at the base). -/
noncomputable def pairVal (m : SettlingMode n) (j : Fin n) (ps r1 r2 A B : ℝ)
    (base : State (Var n)) (t : ℝ) (i : Fin n) : ℝ :=
  if i = m.gcoord then ps + A * Real.exp (-(r1 * t)) + B * Real.exp (-(r2 * t))
  else if i = j then ps + A * Real.exp (-(r1 * t)) - B * Real.exp (-(r2 * t))
  else match m.shapes i with
    | CoordShape.driven j2 =>
        if j2 = m.gcoord then
          base (Rv i) + ps * t + A * expInt r1 t + B * expInt r2 t
        else if j2 = j then
          base (Rv i) + ps * t + A * expInt r1 t - B * expInt r2 t
        else match m.shapes j2 with
          | CoordShape.contractQ kn kd cc =>
              base (Rv i) + (cc : ℝ) * t
                + (base (Rv j2) - (cc : ℝ)) * expInt ((kn : ℝ) / (kd : ℝ)) t
          | _ => base (Rv i)
    | CoordShape.contractQ kn kd cc =>
        (cc : ℝ) + (base (Rv i) - (cc : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t))
    | _ => base (Rv i)

/-- The pair witness flow. -/
noncomputable def pairΦ (m : SettlingMode n) (j : Fin n) (ps r1 r2 A B : ℝ)
    (base : State (Var n)) (t : ℝ) : State (Var n) :=
  fun x => match x with
    | (Side.R, i) => pairVal m j ps r1 r2 A B base t i
    | _ => base x

@[simp] theorem pairΦ_Rv (m : SettlingMode n) (j : Fin n) (ps r1 r2 A B : ℝ)
    (base : State (Var n)) (t : ℝ) (i : Fin n) :
    pairΦ m j ps r1 r2 A B base t (Rv i) = pairVal m j ps r1 r2 A B base t i := rfl

theorem pairΦ_nonR (m : SettlingMode n) (j : Fin n) (ps r1 r2 A B : ℝ)
    (base : State (Var n)) (t : ℝ) {x : Var n} (hx : ∀ i : Fin n, x ≠ Rv i) :
    pairΦ m j ps r1 r2 A B base t x = base x := by
  obtain ⟨sd, ix⟩ := x
  cases sd with
  | R => exact absurd rfl (hx ix)
  | L => rfl
  | Aux => rfl

set_option maxHeartbeats 1000000 in
theorem pairVal_g {m : SettlingMode n} {j : Fin n} {ps r1 r2 A B : ℝ}
    {base : State (Var n)} {t : ℝ} :
    pairVal m j ps r1 r2 A B base t m.gcoord
      = ps + A * Real.exp (-(r1 * t)) + B * Real.exp (-(r2 * t)) := by
  simp [pairVal]

set_option maxHeartbeats 1000000 in
theorem pairVal_j {m : SettlingMode n} {j : Fin n} {ps r1 r2 A B : ℝ}
    {base : State (Var n)} {t : ℝ} (hjne : j ≠ m.gcoord) :
    pairVal m j ps r1 r2 A B base t j
      = ps + A * Real.exp (-(r1 * t)) - B * Real.exp (-(r2 * t)) := by
  simp [pairVal, hjne]

set_option maxHeartbeats 1000000 in
theorem pairVal_dg {m : SettlingMode n} {j : Fin n} {ps r1 r2 A B : ℝ}
    {base : State (Var n)} {t : ℝ} {i : Fin n}
    (hig : i ≠ m.gcoord) (hij : i ≠ j) (hdr : m.shapes i = CoordShape.driven m.gcoord) :
    pairVal m j ps r1 r2 A B base t i
      = base (Rv i) + ps * t + A * expInt r1 t + B * expInt r2 t := by
  simp [pairVal, hig, hij, hdr]

set_option maxHeartbeats 1000000 in
theorem pairVal_dj {m : SettlingMode n} {j : Fin n} {ps r1 r2 A B : ℝ}
    {base : State (Var n)} {t : ℝ} {i : Fin n}
    (hig : i ≠ m.gcoord) (hij : i ≠ j) (hjne : j ≠ m.gcoord)
    (hdr : m.shapes i = CoordShape.driven j) :
    pairVal m j ps r1 r2 A B base t i
      = base (Rv i) + ps * t + A * expInt r1 t - B * expInt r2 t := by
  simp [pairVal, hig, hij, hdr, hjne]

set_option maxHeartbeats 1000000 in
theorem pairVal_cq {m : SettlingMode n} {j : Fin n} {ps r1 r2 A B : ℝ}
    {base : State (Var n)} {t : ℝ} {i : Fin n} {kn kd cc : ℤ}
    (hig : i ≠ m.gcoord) (hij : i ≠ j)
    (hsh : m.shapes i = CoordShape.contractQ kn kd cc) :
    pairVal m j ps r1 r2 A B base t i
      = (cc : ℝ) + (base (Rv i) - (cc : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)) := by
  simp [pairVal, hig, hij, hsh]

set_option maxHeartbeats 1000000 in
theorem pairVal_dcq {m : SettlingMode n} {j j2 : Fin n} {ps r1 r2 A B : ℝ}
    {base : State (Var n)} {t : ℝ} {i : Fin n} {kn kd cc : ℤ}
    (hig : i ≠ m.gcoord) (hij : i ≠ j) (hj2g : j2 ≠ m.gcoord) (hj2j : j2 ≠ j)
    (hdr : m.shapes i = CoordShape.driven j2)
    (hj2 : m.shapes j2 = CoordShape.contractQ kn kd cc) :
    pairVal m j ps r1 r2 A B base t i
      = base (Rv i) + (cc : ℝ) * t
        + (base (Rv j2) - (cc : ℝ)) * expInt ((kn : ℝ) / (kd : ℝ)) t := by
  simp [pairVal, hig, hij, hdr, hj2g, hj2j, hj2]

set_option maxHeartbeats 1000000 in
theorem pairVal_frozen {m : SettlingMode n} {j : Fin n} {ps r1 r2 A B : ℝ}
    {base : State (Var n)} {t : ℝ} {i : Fin n}
    (hig : i ≠ m.gcoord) (hij : i ≠ j) (hfz : m.shapes i = CoordShape.frozen) :
    pairVal m j ps r1 r2 A B base t i = base (Rv i) := by
  simp [pairVal, hig, hij, hfz]

set_option maxHeartbeats 4000000 in
/-- COUPLED-PAIR active coordinate (EXT P): the two-exponential witness for both members,
integrators of either member, contractQ others and their integrators — stays within
`[glo, TT] × [qlo, qhi]` by `twoExp_le` from the `PairConds` rational facts, lands by an
endpoint case-split at the own band top. -/
theorem settling_pair (M : SettlingModel n) {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m) {j : Fin n} {c h : ℤ}
    (hsh : m.shapes m.gcoord = CoordShape.pairSym j c h)
    (hjne : j ≠ m.gcoord)
    (hjsh : m.shapes j = CoordShape.pairSym m.gcoord c h)
    (hh0 : 0 < h) (hh3 : 3 * h ≤ 1000) (hglo0 : 0 ≤ m.glo)
    {plo phi qlo qhi : ℤ}
    (hplo : (M.env m.gcoord).lo = some plo) (hphi : (M.env m.gcoord).hi = some phi)
    (hqloE : (M.env j).lo = some qlo) (hqhiE : (M.env j).hi = some qhi)
    (hqlo0 : 0 ≤ qlo)
    (hOth : ∀ i, i ≠ m.gcoord → i ≠ j →
        m.shapes i = CoordShape.frozen ∨
        ((m.shapes i = CoordShape.driven m.gcoord ∨ m.shapes i = CoordShape.driven j) ∧
          (M.env i).lo = none ∧ (M.env i).hi = none) ∨
        (∃ kn kd cc, m.shapes i = CoordShape.contractQ kn kd cc ∧ 0 ≤ kn ∧ 0 < kd ∧
          (∀ l', (M.env i).lo = some l' → l' ≤ cc) ∧
          (∀ h', (M.env i).hi = some h' → cc ≤ h')) ∨
        (∃ j2, m.shapes i = CoordShape.driven j2 ∧ j2 ≠ m.gcoord ∧ j2 ≠ j ∧
          (∃ kn2 kd2 cc2, m.shapes j2 = CoordShape.contractQ kn2 kd2 cc2 ∧ 0 < kd2) ∧
          (M.env i).lo = none ∧ (M.env i).hi = none))
    (hcov : PairConds m.glo m.ghi plo phi qlo qhi c h m.ghi ∨
        ∃ q' ∈ m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
          m'.glo ≤ m.ghi ∧ PairConds m.glo m.ghi plo phi qlo qhi c h m'.ghi)
    (hdt : (0 : ℝ) ≤ (M.dt : ℝ)) :
    GuardSettlingB M.graph M.GdOf m.fieldOf (Term.const 1) M.envF ((M.dt : ℝ)) q := by
  intro base hb
  obtain ⟨henv, hblo, hbhi⟩ := (sat_GdOf hq).mp hb
  have hDR : (0 : ℝ) < 1000 - (h : ℝ) := by
    have h3 : (3 : ℝ) * (h : ℝ) ≤ 1000 := by exact_mod_cast hh3
    have h0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh0
    linarith
  set psR : ℝ := 1000 * (c : ℝ) / (1000 - (h : ℝ)) with hpsdef
  set r1 : ℝ := (1000 - (h : ℝ)) / 1000 with hr1def
  set r2 : ℝ := (1000 + (h : ℝ)) / 1000 with hr2def
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh0
  have hr1 : 0 < r1 := by rw [hr1def]; positivity
  have hr12 : r1 ≤ r2 := by
    rw [hr1def, hr2def]
    apply div_le_div_of_nonneg_right ?_ (by norm_num)
    · linarith
  have hr2b : r2 ≤ 2 * r1 := by
    rw [hr1def, hr2def]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1000)]
    have h3 : (3 : ℝ) * (h : ℝ) ≤ 1000 := by exact_mod_cast hh3
    ring_nf
    nlinarith
  set p0 : ℝ := base (Rv m.gcoord) with hp0def
  set q0 : ℝ := base (Rv j) with hq0def
  set A : ℝ := (p0 + q0) / 2 - psR with hAdef
  set B : ℝ := (p0 - q0) / 2 with hBdef
  -- base membership of the partner (from the envelope)
  have hqbase : (qlo : ℝ) ≤ q0 ∧ q0 ≤ (qhi : ℝ) := by
    have hbe := (sat_envF.mp henv) j
    unfold Band.memR at hbe
    rw [hqloE, hqhiE] at hbe
    exact hbe
  -- the bound machinery, parameterized by the landing target TT
  have hbounds : ∀ (TT : ℤ), PairConds m.glo m.ghi plo phi qlo qhi c h TT →
      ∀ t, 0 ≤ t →
      ((m.glo : ℝ) ≤ psR + A * Real.exp (-(r1 * t)) + B * Real.exp (-(r2 * t))
        ∧ psR + A * Real.exp (-(r1 * t)) + B * Real.exp (-(r2 * t)) ≤ (TT : ℝ))
      ∧ ((qlo : ℝ) ≤ psR + A * Real.exp (-(r1 * t)) - B * Real.exp (-(r2 * t))
        ∧ psR + A * Real.exp (-(r1 * t)) - B * Real.exp (-(r2 * t)) ≤ (qhi : ℝ)) := by
    intro TT hC t ht
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ := hC
    have c4R : 1000 * (c : ℝ) ≤ (TT : ℝ) * (1000 - (h : ℝ)) := by exact_mod_cast c4
    have c5R : (m.glo : ℝ) * (1000 - (h : ℝ)) ≤ 1000 * (c : ℝ) := by exact_mod_cast c5
    have c6R : ((m.ghi : ℝ) + (qhi : ℝ)) * (1000 - (h : ℝ)) + 2 * (1000 * (c : ℝ))
        ≤ 4 * (TT : ℝ) * (1000 - (h : ℝ)) := by exact_mod_cast c6
    have c7R : 4 * (m.glo : ℝ) * (1000 - (h : ℝ))
        ≤ ((m.glo : ℝ) + (qlo : ℝ)) * (1000 - (h : ℝ)) + 2 * (1000 * (c : ℝ)) := by
      exact_mod_cast c7
    have c8R : 1000 * (c : ℝ) ≤ (qhi : ℝ) * (1000 - (h : ℝ)) := by exact_mod_cast c8
    have c9R : (qlo : ℝ) * (1000 - (h : ℝ)) ≤ 1000 * (c : ℝ) := by exact_mod_cast c9
    have c10R : ((m.ghi : ℝ) + (qhi : ℝ)) * (1000 - (h : ℝ)) + 2 * (1000 * (c : ℝ))
        ≤ 4 * (qhi : ℝ) * (1000 - (h : ℝ)) := by exact_mod_cast c10
    have c11R : 4 * (qlo : ℝ) * (1000 - (h : ℝ))
        ≤ ((m.glo : ℝ) + (qlo : ℝ)) * (1000 - (h : ℝ)) + 2 * (1000 * (c : ℝ)) := by
      exact_mod_cast c11
    have hpsT : psR ≤ (TT : ℝ) := by
      rw [hpsdef, div_le_iff₀ hDR]
      linarith
    have hglops : (m.glo : ℝ) ≤ psR := by
      rw [hpsdef, le_div_iff₀ hDR]
      linarith
    have hpsqhi : psR ≤ (qhi : ℝ) := by
      rw [hpsdef, div_le_iff₀ hDR]
      linarith
    have hqlops : (qlo : ℝ) ≤ psR := by
      rw [hpsdef, le_div_iff₀ hDR]
      linarith
    have hghiT : (m.ghi : ℝ) ≤ (TT : ℝ) := by exact_mod_cast c1
    have hAub : A ≤ ((m.ghi : ℝ) + (qhi : ℝ)) / 2 - psR := by
      rw [hAdef]
      have := hqbase.2
      have := hbhi
      linarith
    have hAlb : ((m.glo : ℝ) + (qlo : ℝ)) / 2 - psR ≤ A := by
      rw [hAdef]
      have := hqbase.1
      have := hblo
      linarith
    have hAT : A ≤ 2 * ((TT : ℝ) - psR) := by
      have hps' : psR * (1000 - (h : ℝ)) = 1000 * (c : ℝ) := by
        rw [hpsdef]
        field_simp
      nlinarith [hAub, hDR]
    have hATq : A ≤ 2 * ((qhi : ℝ) - psR) := by
      have hps' : psR * (1000 - (h : ℝ)) = 1000 * (c : ℝ) := by
        rw [hpsdef]
        field_simp
      nlinarith [hAub, hDR]
    have hATl : -A ≤ 2 * (psR - (m.glo : ℝ)) := by
      have hps' : psR * (1000 - (h : ℝ)) = 1000 * (c : ℝ) := by
        rw [hpsdef]
        field_simp
      nlinarith [hAlb, hDR]
    have hATlq : -A ≤ 2 * (psR - (qlo : ℝ)) := by
      have hps' : psR * (1000 - (h : ℝ)) = 1000 * (c : ℝ) := by
        rw [hpsdef]
        field_simp
      nlinarith [hAlb, hDR]
    have hp0AB : psR + A + B = p0 := by
      rw [hAdef, hBdef]
      ring
    have hq0AB : psR + A + -B = q0 := by
      rw [hAdef, hBdef]
      ring
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · -- glo ≤ p(t): twoExp_le on the negated data
      have := twoExp_le (-psR) (-A) (-B) r1 r2 (-(m.glo : ℝ)) t hr1 hr12 hr2b ht
        (by linarith) (by rw [show -psR + -A + -B = -(psR + A + B) from by ring, hp0AB]
                          linarith [hblo])
        (by linarith [hATl])
      linarith [this]
    · exact twoExp_le psR A B r1 r2 (TT : ℝ) t hr1 hr12 hr2b ht hpsT
        (by rw [hp0AB]; linarith [hbhi, hghiT]) hAT
    · -- qlo ≤ q(t)
      have := twoExp_le (-psR) (-A) B r1 r2 (-(qlo : ℝ)) t hr1 hr12 hr2b ht
        (by linarith) (by rw [show -psR + -A + B = -(psR + A + -B) from by ring, hq0AB]
                          linarith [hqbase.1])
        (by linarith [hATlq])
      linarith [this]
    · have := twoExp_le psR A (-B) r1 r2 (qhi : ℝ) t hr1 hr12 hr2b ht hpsqhi
        (by rw [hq0AB]; linarith [hqbase.2]) hATq
      linarith [this]
  -- choose the landing target and box (self, or the covering successor by endpoint split)
  obtain ⟨TT, hC, q2, hq2ret, m2, hm2, hgc2, hl1, hl2⟩ :
      ∃ TT, PairConds m.glo m.ghi plo phi qlo qhi c h TT ∧
        ∃ q2 ∈ q :: M.graph.retainedSucc q, ∃ m2, M.modes[q2]? = some m2 ∧
          m2.gcoord = m.gcoord ∧
          ((m2.glo : ℝ) ≤ pairVal m j psR r1 r2 A B base (M.dt : ℝ) m.gcoord
            ∧ pairVal m j psR r1 r2 A B base (M.dt : ℝ) m.gcoord ≤ (m2.ghi : ℝ)) := by
    rcases hcov with hC | ⟨q', hq'mem, m', hm', hgc', hglo', hC⟩
    · refine ⟨m.ghi, hC, q, List.mem_cons_self .., m, hq, rfl, ?_, ?_⟩
      · have hbb := ((hbounds m.ghi hC (M.dt : ℝ) hdt).1).1
        rw [pairVal_g]
        linarith
      · have hbb := ((hbounds m.ghi hC (M.dt : ℝ) hdt).1).2
        rw [pairVal_g]
        linarith
    · rcases le_or_gt (pairVal m j psR r1 r2 A B base (M.dt : ℝ) m.gcoord)
        ((m.ghi : ℝ)) with he | he
      · refine ⟨m'.ghi, hC, q, List.mem_cons_self .., m, hq, rfl, ?_, he⟩
        have hbb := ((hbounds m'.ghi hC (M.dt : ℝ) hdt).1).1
        rw [pairVal_g]
        linarith
      · refine ⟨m'.ghi, hC, q', List.mem_cons_of_mem _ (succ_mem_retained M hq hq'mem),
          m', hm', hgc', ?_, ?_⟩
        · have hglo'R : (m'.glo : ℝ) ≤ (m.ghi : ℝ) := by exact_mod_cast hglo'
          linarith
        · have hbb := ((hbounds m'.ghi hC (M.dt : ℝ) hdt).1).2
          rw [pairVal_g]
          linarith
  have hc2R : (TT : ℝ) ≤ (phi : ℝ) := by exact_mod_cast hC.2.1
  have hc3R : (plo : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hC.2.2.1
  -- staying in the envelope
  have hstayEnv : ∀ t, 0 ≤ t →
      Formula.sat M.envF (pairΦ m j psR r1 r2 A B base t) := by
    intro t ht
    rw [sat_envF]
    intro i
    rw [pairΦ_Rv]
    by_cases hig : i = m.gcoord
    · rw [hig, pairVal_g]
      obtain ⟨⟨h1, h2⟩, -⟩ := hbounds TT hC t ht
      simp only [Band.memR, hplo, hphi]
      exact ⟨by linarith, by linarith⟩
    · by_cases hij : i = j
      · rw [hij, pairVal_j hjne]
        obtain ⟨-, hq1, hq2b⟩ := hbounds TT hC t ht
        simp only [Band.memR, hqloE, hqhiE]
        exact ⟨by linarith, by linarith⟩
      · rcases hOth i hig hij with hfz | ⟨hdr, hloN, hhiN⟩
          | ⟨kn, kd, cc, hcq, hkn, hkd, hloC, hhiC⟩
          | ⟨j2, hdr, hj2g, hj2j, ⟨kn2, kd2, cc2, hj2cq, hkd2⟩, hloN, hhiN⟩
        · rw [pairVal_frozen hig hij hfz]
          exact (sat_envF.mp henv) i
        · rcases hdr with hdr | hdr
          · rw [pairVal_dg hig hij hdr]
            simp only [Band.memR, hloN, hhiN]
            exact ⟨trivial, trivial⟩
          · rw [pairVal_dj hig hij hjne hdr]
            simp only [Band.memR, hloN, hhiN]
            exact ⟨trivial, trivial⟩
        · have hkdR : (0 : ℝ) < (kd : ℝ) := by exact_mod_cast hkd
          have hgq : (0 : ℝ) ≤ (kn : ℝ) / (kd : ℝ) :=
            div_nonneg (by exact_mod_cast hkn) hkdR.le
          have hθpos : 0 < Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)) := Real.exp_pos _
          have hθle : Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)) ≤ 1 := by
            rw [Real.exp_le_one_iff]
            nlinarith
          rw [pairVal_cq hig hij hcq]
          have hbe := (sat_envF.mp henv) i
          unfold Band.memR at hbe ⊢
          rcases hbe with ⟨hbl, hbh⟩
          constructor
          · cases hcase : (M.env i).lo with
            | none => trivial
            | some l =>
                rw [hcase] at hbl
                have hlc : (l : ℝ) ≤ (cc : ℝ) := by exact_mod_cast hloC l hcase
                nlinarith
          · cases hcase : (M.env i).hi with
            | none => trivial
            | some hh =>
                rw [hcase] at hbh
                have hhc : (cc : ℝ) ≤ (hh : ℝ) := by exact_mod_cast hhiC hh hcase
                nlinarith
        · rw [pairVal_dcq hig hij hj2g hj2j hdr hj2cq]
          simp only [Band.memR, hloN, hhiN]
          exact ⟨trivial, trivial⟩
  -- exponential derivative helpers and the rate identities
  have hexpD : ∀ (r : ℝ) (t : ℝ), HasDerivAt (fun u : ℝ => Real.exp (-(r * u)))
      (-r * Real.exp (-(r * t))) t := by
    intro r t
    have hinner : HasDerivAt (fun u : ℝ => -(r * u)) (-r) t := by
      have hh := (hasDerivAt_id t).const_mul (-r)
      simp only [id, mul_one, neg_mul] at hh
      exact hh
    have hh := (Real.hasDerivAt_exp (-(r * t))).comp t hinner
    simp only [Function.comp_def] at hh
    rw [mul_comm (Real.exp (-(r * t))) (-r)] at hh
    exact hh
  have hDne : (1000 : ℝ) - (h : ℝ) ≠ 0 := ne_of_gt hDR
  have hpsr : psR * r1 = (c : ℝ) := by
    rw [hpsdef, hr1def]
    field_simp
  have hr1' : 1 - (h : ℝ) / 1000 = r1 := by
    rw [hr1def]
    ring
  have hr2' : 1 + (h : ℝ) / 1000 = r2 := by
    rw [hr2def]
    ring
  refine ⟨pairΦ m j psR r1 r2 A B base, ?_, ?_, ?_,
    fun t ht => hstayEnv t ht.1, q2, hq2ret, ?_⟩
  · -- t = 0 recovers the base
    funext x
    obtain ⟨sd, ix⟩ := x
    cases sd with
    | R =>
        show pairVal m j psR r1 r2 A B base 0 ix = base (Rv ix)
        by_cases hig : ix = m.gcoord
        · rw [hig, pairVal_g]
          simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
          rw [hAdef, hBdef, hp0def, hq0def]
          ring
        · by_cases hij : ix = j
          · rw [hij, pairVal_j hjne]
            simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
            rw [hAdef, hBdef, hp0def, hq0def]
            ring
          · rcases hOth ix hig hij with hfz | ⟨hdr, -, -⟩
              | ⟨kn, kd, cc, hcq, -, -, -, -⟩
              | ⟨j2, hdr, hj2g, hj2j, ⟨kn2, kd2, cc2, hj2cq, -⟩, -, -⟩
            · rw [pairVal_frozen hig hij hfz]
            · rcases hdr with hdr | hdr
              · rw [pairVal_dg hig hij hdr]
                simp [expInt]
              · rw [pairVal_dj hig hij hjne hdr]
                simp [expInt]
            · rw [pairVal_cq hig hij hcq]
              simp
            · rw [pairVal_dcq hig hij hj2g hj2j hdr hj2cq]
              simp [expInt]
    | L => rfl
    | Aux => rfl
  · -- derivatives
    intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hig : i = m.gcoord
    · rw [hig]
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf m.gcoord))
          (pairΦ m j psR r1 r2 A B base t)
          = ((c : ℝ) - (psR + A * Real.exp (-(r1 * t)) + B * Real.exp (-(r2 * t))))
            + (h : ℝ) / 1000
              * (psR + A * Real.exp (-(r1 * t)) - B * Real.exp (-(r2 * t))) := by
        simp only [SettlingMode.fieldOf, hsh, CoordShape.field, Term.eval, AOp.interp,
          pairΦ_Rv, pairVal_g, pairVal_j hjne]
        ring
      rw [heval]
      have hcurve : (fun u => pairΦ m j psR r1 r2 A B base u (Rv m.gcoord))
          = fun u => psR + A * Real.exp (-(r1 * u)) + B * Real.exp (-(r2 * u)) := by
        funext u
        rw [pairΦ_Rv, pairVal_g]
      rw [hcurve]
      have hd : HasDerivAt
          (fun u => psR + A * Real.exp (-(r1 * u)) + B * Real.exp (-(r2 * u)))
          (A * (-r1 * Real.exp (-(r1 * t))) + B * (-r2 * Real.exp (-(r2 * t)))) t :=
        (((hexpD r1 t).const_mul A).const_add psR).add ((hexpD r2 t).const_mul B)
      have heq : A * (-r1 * Real.exp (-(r1 * t))) + B * (-r2 * Real.exp (-(r2 * t)))
          = ((c : ℝ) - (psR + A * Real.exp (-(r1 * t)) + B * Real.exp (-(r2 * t))))
            + (h : ℝ) / 1000
              * (psR + A * Real.exp (-(r1 * t)) - B * Real.exp (-(r2 * t))) := by
        linear_combination (A * Real.exp (-(r1 * t)) + psR) * hr1'
          + (B * Real.exp (-(r2 * t))) * hr2' + hpsr
      rw [← heq]
      exact hd.hasDerivWithinAt
    · by_cases hij : i = j
      · rw [hij]
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf j))
            (pairΦ m j psR r1 r2 A B base t)
            = ((c : ℝ) - (psR + A * Real.exp (-(r1 * t)) - B * Real.exp (-(r2 * t))))
              + (h : ℝ) / 1000
                * (psR + A * Real.exp (-(r1 * t)) + B * Real.exp (-(r2 * t))) := by
          simp only [SettlingMode.fieldOf, hjsh, CoordShape.field, Term.eval, AOp.interp,
            pairΦ_Rv, pairVal_g, pairVal_j hjne]
          ring
        rw [heval]
        have hcurve : (fun u => pairΦ m j psR r1 r2 A B base u (Rv j))
            = fun u => psR + A * Real.exp (-(r1 * u)) - B * Real.exp (-(r2 * u)) := by
          funext u
          rw [pairΦ_Rv, pairVal_j hjne]
        rw [hcurve]
        have hd : HasDerivAt
            (fun u => psR + A * Real.exp (-(r1 * u)) - B * Real.exp (-(r2 * u)))
            (A * (-r1 * Real.exp (-(r1 * t))) - B * (-r2 * Real.exp (-(r2 * t)))) t :=
          (((hexpD r1 t).const_mul A).const_add psR).sub ((hexpD r2 t).const_mul B)
        have heq : A * (-r1 * Real.exp (-(r1 * t))) - B * (-r2 * Real.exp (-(r2 * t)))
            = ((c : ℝ) - (psR + A * Real.exp (-(r1 * t)) - B * Real.exp (-(r2 * t))))
              + (h : ℝ) / 1000
                * (psR + A * Real.exp (-(r1 * t)) + B * Real.exp (-(r2 * t))) := by
          linear_combination (A * Real.exp (-(r1 * t)) + psR) * hr1'
            - (B * Real.exp (-(r2 * t))) * hr2' + hpsr
        rw [← heq]
        exact hd.hasDerivWithinAt
      · rcases hOth i hig hij with hfz | ⟨hdr, -, -⟩
          | ⟨kn, kd, cc, hcq, -, -, -, -⟩
          | ⟨j2, hdr, hj2g, hj2j, ⟨kn2, kd2, cc2, hj2cq, hkd2⟩, -, -⟩
        · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
              (pairΦ m j psR r1 r2 A B base t) = 0 := by
            simp [SettlingMode.fieldOf, hfz, CoordShape.field, Term.eval, AOp.interp]
          rw [heval]
          have hcurve : (fun u => pairΦ m j psR r1 r2 A B base u (Rv i))
              = fun _ => base (Rv i) := by
            funext u
            rw [pairΦ_Rv, pairVal_frozen hig hij hfz]
          rw [hcurve]
          exact hasDerivWithinAt_const t _ _
        · rcases hdr with hdr | hdr
          · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
                (pairΦ m j psR r1 r2 A B base t)
                = psR + A * Real.exp (-(r1 * t)) + B * Real.exp (-(r2 * t)) := by
              simp only [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval,
                AOp.interp, pairΦ_Rv, pairVal_g]
              ring
            rw [heval]
            have hcurve : (fun u => pairΦ m j psR r1 r2 A B base u (Rv i))
                = fun u => base (Rv i) + psR * u + A * expInt r1 u + B * expInt r2 u := by
              funext u
              rw [pairΦ_Rv, pairVal_dg hig hij hdr]
            rw [hcurve]
            have h1 : HasDerivAt (fun u : ℝ => base (Rv i) + psR * u) psR t := by
              have hh := ((hasDerivAt_id t).const_mul psR).const_add (base (Rv i))
              simpa using hh
            have h2 : HasDerivAt (fun u : ℝ => A * expInt r1 u)
                (A * Real.exp (-(r1 * t))) t := (expInt_hasDeriv r1 t).const_mul A
            have h3 : HasDerivAt (fun u : ℝ => B * expInt r2 u)
                (B * Real.exp (-(r2 * t))) t := (expInt_hasDeriv r2 t).const_mul B
            exact ((h1.add h2).add h3).hasDerivWithinAt
          · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
                (pairΦ m j psR r1 r2 A B base t)
                = psR + A * Real.exp (-(r1 * t)) - B * Real.exp (-(r2 * t)) := by
              simp only [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval,
                AOp.interp, pairΦ_Rv, pairVal_j hjne]
              ring
            rw [heval]
            have hcurve : (fun u => pairΦ m j psR r1 r2 A B base u (Rv i))
                = fun u => base (Rv i) + psR * u + A * expInt r1 u - B * expInt r2 u := by
              funext u
              rw [pairΦ_Rv, pairVal_dj hig hij hjne hdr]
            rw [hcurve]
            have h1 : HasDerivAt (fun u : ℝ => base (Rv i) + psR * u) psR t := by
              have hh := ((hasDerivAt_id t).const_mul psR).const_add (base (Rv i))
              simpa using hh
            have h2 : HasDerivAt (fun u : ℝ => A * expInt r1 u)
                (A * Real.exp (-(r1 * t))) t := (expInt_hasDeriv r1 t).const_mul A
            have h3 : HasDerivAt (fun u : ℝ => B * expInt r2 u)
                (B * Real.exp (-(r2 * t))) t := (expInt_hasDeriv r2 t).const_mul B
            exact (((h1.add h2).sub h3)).hasDerivWithinAt
        · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
              (pairΦ m j psR r1 r2 A B base t)
              = (kn : ℝ) / (kd : ℝ)
                * ((cc : ℝ) - pairVal m j psR r1 r2 A B base t i) := by
            simp [SettlingMode.fieldOf, hcq, CoordShape.field, Term.eval, AOp.interp]
          rw [heval]
          have hcurve : (fun u => pairΦ m j psR r1 r2 A B base u (Rv i))
              = fun u => (cc : ℝ)
                  + (base (Rv i) - (cc : ℝ))
                    * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * u)) := by
            funext u
            rw [pairΦ_Rv, pairVal_cq hig hij hcq]
          rw [hcurve]
          have h1 : HasDerivAt
              (fun u => (cc : ℝ)
                + (base (Rv i) - (cc : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * u)))
              ((base (Rv i) - (cc : ℝ))
                * (-((kn : ℝ) / (kd : ℝ))
                  * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)))) t :=
            ((hexpD ((kn : ℝ) / (kd : ℝ)) t).const_mul
              (base (Rv i) - (cc : ℝ))).const_add (cc : ℝ)
          have heq : (base (Rv i) - (cc : ℝ))
              * (-((kn : ℝ) / (kd : ℝ)) * Real.exp (-(((kn : ℝ) / (kd : ℝ)) * t)))
              = (kn : ℝ) / (kd : ℝ)
                * ((cc : ℝ) - pairVal m j psR r1 r2 A B base t i) := by
            rw [pairVal_cq hig hij hcq]
            ring
          rw [← heq]
          exact h1.hasDerivWithinAt
        · have hvalj2 : pairΦ m j psR r1 r2 A B base t (Rv j2)
              = (cc2 : ℝ) + (base (Rv j2) - (cc2 : ℝ))
                * Real.exp (-(((kn2 : ℝ) / (kd2 : ℝ)) * t)) := by
            rw [pairΦ_Rv, pairVal_cq hj2g hj2j hj2cq]
          have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
              (pairΦ m j psR r1 r2 A B base t)
              = (cc2 : ℝ) + (base (Rv j2) - (cc2 : ℝ))
                * Real.exp (-(((kn2 : ℝ) / (kd2 : ℝ)) * t)) := by
            simp only [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp]
            rw [hvalj2]
            ring
          rw [heval]
          have hcurve : (fun u => pairΦ m j psR r1 r2 A B base u (Rv i))
              = fun u => base (Rv i) + (cc2 : ℝ) * u
                  + (base (Rv j2) - (cc2 : ℝ)) * expInt ((kn2 : ℝ) / (kd2 : ℝ)) u := by
            funext u
            rw [pairΦ_Rv, pairVal_dcq hig hij hj2g hj2j hdr hj2cq]
          rw [hcurve]
          have h1 : HasDerivAt (fun u : ℝ => base (Rv i) + (cc2 : ℝ) * u) (cc2 : ℝ) t := by
            have hh := ((hasDerivAt_id t).const_mul (cc2 : ℝ)).const_add (base (Rv i))
            simpa using hh
          have h2 : HasDerivAt
              (fun u : ℝ => (base (Rv j2) - (cc2 : ℝ)) * expInt ((kn2 : ℝ) / (kd2 : ℝ)) u)
              ((base (Rv j2) - (cc2 : ℝ))
                * Real.exp (-(((kn2 : ℝ) / (kd2 : ℝ)) * t))) t :=
            (expInt_hasDeriv ((kn2 : ℝ) / (kd2 : ℝ)) t).const_mul
              (base (Rv j2) - (cc2 : ℝ))
          exact (h1.add h2).hasDerivWithinAt
  · -- mask
    intro t ht x hx
    refine pairΦ_nonR m j psR r1 r2 A B base t ?_
    intro i hxi
    exact hx (by
      rw [hxi]
      simp only [rightBlock, ODESystem.bound, List.map_map]
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  · -- landing in the picked box
    rw [sat_GdOf hm2]
    refine ⟨hstayEnv _ hdt, ?_, ?_⟩
    · rw [hgc2, pairΦ_Rv]
      exact hl1
    · rw [hgc2, pairΦ_Rv]
      exact hl2

/-! ### EXT R — the Riccati discharge (quadratic drag, hyperbolic-Möbius witness)

`x' = b − (a/10⁶)x²` contracts toward `q = √(10⁶b/a)`; the exact flow is the Möbius form
`v(t) = q·N/D` with `N = v₀·cosh(αt) + q·sinh(αt)`, `D = q·cosh(αt) + v₀·sinh(αt)`,
`α = (a/10⁶)·q` — `N' = αD`, `D' = αN`, and `D² − N² = q² − v₀²` (from `cosh² − sinh² = 1`)
give the field identity by the quotient rule. The value stays in the hull of `v₀` and `q`
(`v − q` carries the sign of `v₀ − q` via the positive factor `e^{−αt}/D`; `v − v₀` carries
the sign of `q − v₀` via `sinh/D`), so with the equilibrium inside the band the mode
self-lands — no successor conditions at all. -/

/-- The Möbius value of the Riccati flow. -/
noncomputable def riccVal (qR α v0 t : ℝ) : ℝ :=
  qR * (v0 * Real.cosh (α * t) + qR * Real.sinh (α * t))
    / (qR * Real.cosh (α * t) + v0 * Real.sinh (α * t))

/-- The Riccati witness flow (frozen off the active coordinate). -/
noncomputable def riccΦ (m : SettlingMode n) (qR α : ℝ) (base : State (Var n)) (t : ℝ) :
    State (Var n) :=
  fun x => match x with
    | (Side.R, i) =>
        if i = m.gcoord then riccVal qR α (base (Rv m.gcoord)) t else base (Rv i)
    | _ => base x

@[simp] theorem riccΦ_Rv (m : SettlingMode n) (qR α : ℝ) (base : State (Var n)) (t : ℝ)
    (i : Fin n) : riccΦ m qR α base t (Rv i)
      = if i = m.gcoord then riccVal qR α (base (Rv m.gcoord)) t else base (Rv i) := rfl

theorem riccΦ_nonR (m : SettlingMode n) (qR α : ℝ) (base : State (Var n)) (t : ℝ)
    {x : Var n} (hx : ∀ i : Fin n, x ≠ Rv i) : riccΦ m qR α base t x = base x := by
  obtain ⟨sd, ix⟩ := x
  cases sd with
  | R => exact absurd rfl (hx ix)
  | L => rfl
  | Aux => rfl

/-- RICCATI active coordinate: quadratic drag with the equilibrium inside the band — stays
in the hull of base and equilibrium and self-lands. Frozen others. -/
theorem settling_riccati (M : SettlingModel n) {q : ℕ} {m : SettlingMode n}
    (hq : M.modes[q]? = some m) {b a : ℤ}
    (hsh : m.shapes m.gcoord = CoordShape.riccati b a)
    (hfr : ∀ i, i ≠ m.gcoord → m.shapes i = CoordShape.frozen)
    (hb : 0 < b) (ha : 0 < a) (hglo0 : 0 ≤ m.glo) (hord : m.glo ≤ m.ghi)
    (hql : m.glo^2 * a ≤ 1000000 * b) (hqh : 1000000 * b ≤ m.ghi^2 * a)
    (hloIn : ∀ l', (M.env m.gcoord).lo = some l' → l' ≤ m.glo)
    (hhiIn : ∀ h', (M.env m.gcoord).hi = some h' → m.ghi ≤ h')
    (hdt : (0 : ℝ) ≤ (M.dt : ℝ)) :
    GuardSettlingB M.graph M.GdOf m.fieldOf (Term.const 1) M.envF ((M.dt : ℝ)) q := by
  intro base hb'
  obtain ⟨henv, hblo, hbhi⟩ := (sat_GdOf hq).mp hb'
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hglo0R : (0 : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hglo0
  set qR : ℝ := Real.sqrt ((1000000 * b : ℝ) / a) with hqdef
  have hargpos : (0 : ℝ) < (1000000 * b : ℝ) / a := by positivity
  have hqpos : 0 < qR := Real.sqrt_pos.mpr hargpos
  have hq2 : qR ^ 2 = (1000000 * b : ℝ) / a := Real.sq_sqrt hargpos.le
  set α : ℝ := (a : ℝ) / 1000000 * qR with hαdef
  have hαpos : 0 < α := by positivity
  have hbv0 : (0 : ℝ) ≤ base (Rv m.gcoord) := le_trans hglo0R hblo
  -- the equilibrium sits inside the band
  have hghi0 : (0 : ℝ) ≤ (m.ghi : ℝ) := le_trans hglo0R (by exact_mod_cast hord)
  have hqlR : (m.glo : ℝ) ≤ qR := by
    have h1 : ((m.glo : ℝ))^2 * (a : ℝ) ≤ 1000000 * (b : ℝ) := by exact_mod_cast hql
    have h2 : ((m.glo : ℝ))^2 ≤ qR^2 := by
      rw [hq2, le_div_iff₀ haR]
      exact h1
    calc (m.glo : ℝ) = Real.sqrt (((m.glo : ℝ))^2) := (Real.sqrt_sq hglo0R).symm
      _ ≤ Real.sqrt (qR^2) := Real.sqrt_le_sqrt h2
      _ = qR := Real.sqrt_sq hqpos.le
  have hqhR : qR ≤ (m.ghi : ℝ) := by
    have h1 : 1000000 * (b : ℝ) ≤ ((m.ghi : ℝ))^2 * (a : ℝ) := by exact_mod_cast hqh
    have h2 : qR^2 ≤ ((m.ghi : ℝ))^2 := by
      rw [hq2, div_le_iff₀ haR]
      exact h1
    calc qR = Real.sqrt (qR^2) := (Real.sqrt_sq hqpos.le).symm
      _ ≤ Real.sqrt (((m.ghi : ℝ))^2) := Real.sqrt_le_sqrt h2
      _ = (m.ghi : ℝ) := Real.sqrt_sq hghi0
  -- the denominator is positive for all t ≥ 0
  have hD : ∀ t, 0 ≤ t →
      0 < qR * Real.cosh (α * t) + base (Rv m.gcoord) * Real.sinh (α * t) := by
    intro t ht
    have hc := Real.one_le_cosh (α * t)
    have hs : 0 ≤ Real.sinh (α * t) := Real.sinh_nonneg_iff.mpr (by positivity)
    nlinarith
  -- hull bounds: the value sits between the base and the equilibrium
  have hband : ∀ t, 0 ≤ t →
      (m.glo : ℝ) ≤ riccVal qR α (base (Rv m.gcoord)) t
      ∧ riccVal qR α (base (Rv m.gcoord)) t ≤ (m.ghi : ℝ) := by
    intro t ht
    have hDpos := hD t ht
    have hs : 0 ≤ Real.sinh (α * t) := Real.sinh_nonneg_iff.mpr (by positivity)
    have hexp : Real.cosh (α * t) - Real.sinh (α * t) = Real.exp (-(α * t)) :=
      Real.cosh_sub_sinh (α * t)
    have hexppos : (0 : ℝ) < Real.exp (-(α * t)) := Real.exp_pos _
    have hnum1 : riccVal qR α (base (Rv m.gcoord)) t - qR
        = qR * (base (Rv m.gcoord) - qR) * Real.exp (-(α * t))
          / (qR * Real.cosh (α * t) + base (Rv m.gcoord) * Real.sinh (α * t)) := by
      unfold riccVal
      rw [← hexp]
      field_simp
      ring
    have hnum2 : riccVal qR α (base (Rv m.gcoord)) t - base (Rv m.gcoord)
        = (qR ^ 2 - base (Rv m.gcoord) ^ 2) * Real.sinh (α * t)
          / (qR * Real.cosh (α * t) + base (Rv m.gcoord) * Real.sinh (α * t)) := by
      unfold riccVal
      field_simp
      ring
    rcases le_total (base (Rv m.gcoord)) qR with hbq | hbq
    · -- v₀ ≤ q: the value rises from v₀ toward q
      have hle : riccVal qR α (base (Rv m.gcoord)) t - qR ≤ 0 := by
        rw [hnum1, div_nonpos_iff]
        right
        constructor
        · nlinarith [mul_nonneg (mul_nonneg hqpos.le (sub_nonneg.mpr hbq)) hexppos.le]
        · exact hDpos.le
      have hge : 0 ≤ riccVal qR α (base (Rv m.gcoord)) t - base (Rv m.gcoord) := by
        rw [hnum2]
        apply div_nonneg _ hDpos.le
        nlinarith [mul_nonneg (mul_nonneg (add_nonneg hqpos.le hbv0)
          (sub_nonneg.mpr hbq)) hs]
      constructor
      · linarith
      · linarith
    · -- q ≤ v₀: the value falls from v₀ toward q
      have hge : 0 ≤ riccVal qR α (base (Rv m.gcoord)) t - qR := by
        rw [hnum1]
        apply div_nonneg _ hDpos.le
        have : 0 ≤ base (Rv m.gcoord) - qR := by linarith
        positivity
      have hle : riccVal qR α (base (Rv m.gcoord)) t - base (Rv m.gcoord) ≤ 0 := by
        rw [hnum2, div_nonpos_iff]
        right
        constructor
        · nlinarith [mul_nonneg (mul_nonneg (add_nonneg hbv0 hqpos.le)
            (sub_nonneg.mpr hbq)) hs]
        · exact hDpos.le
      constructor
      · linarith
      · linarith
  -- staying in the envelope
  have hstayEnv : ∀ t, 0 ≤ t →
      Formula.sat M.envF (riccΦ m qR α base t) := by
    intro t ht
    rw [sat_envF]
    intro i
    rw [riccΦ_Rv]
    by_cases hig : i = m.gcoord
    · rw [if_pos hig, hig]
      obtain ⟨h1, h2⟩ := hband t ht
      unfold Band.memR
      constructor
      · cases hcase : (M.env m.gcoord).lo with
        | none => trivial
        | some l =>
            have hlG : (l : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hloIn l hcase
            linarith
      · cases hcase : (M.env m.gcoord).hi with
        | none => trivial
        | some h =>
            have hhG : (m.ghi : ℝ) ≤ (h : ℝ) := by exact_mod_cast hhiIn h hcase
            linarith
    · rw [if_neg hig]
      exact (sat_envF.mp henv) i
  refine ⟨riccΦ m qR α base, ?_, ?_, ?_, fun t ht => hstayEnv t ht.1,
    q, List.mem_cons_self .., ?_⟩
  · -- t = 0 recovers the base
    funext x
    obtain ⟨sd, ix⟩ := x
    cases sd with
    | R =>
        show riccΦ m qR α base 0 (Rv ix) = base (Rv ix)
        rw [riccΦ_Rv]
        by_cases hig : ix = m.gcoord
        · rw [if_pos hig, hig]
          unfold riccVal
          simp only [mul_zero, Real.cosh_zero, Real.sinh_zero, mul_one, add_zero, zero_add]
          rw [mul_comm qR, mul_div_assoc, div_self (ne_of_gt hqpos), mul_one]
        · rw [if_neg hig]
    | L => rfl
    | Aux => rfl
  · -- derivatives
    intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hig : i = m.gcoord
    · rw [hig]
      have hDpos := hD t ht.1
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf m.gcoord))
          (riccΦ m qR α base t)
          = (b : ℝ) - (a : ℝ) / 1000000 * (riccVal qR α (base (Rv m.gcoord)) t) ^ 2 := by
        simp only [SettlingMode.fieldOf, hsh, CoordShape.field, Term.eval, AOp.interp,
          riccΦ_Rv, eq_self_iff_true, if_true]
        ring
      rw [heval]
      have hcurve : (fun u => riccΦ m qR α base u (Rv m.gcoord))
          = fun u => riccVal qR α (base (Rv m.gcoord)) u := by
        funext u
        rw [riccΦ_Rv, if_pos rfl]
      rw [hcurve]
      -- N' = αD, D' = αN, quotient rule
      have hinner : ∀ u : ℝ, HasDerivAt (fun w : ℝ => α * w) α u := by
        intro u
        simpa using (hasDerivAt_id u).const_mul α
      have hcoshD : HasDerivAt (fun w : ℝ => Real.cosh (α * w))
          (Real.sinh (α * t) * α) t :=
        (Real.hasDerivAt_cosh (α * t)).comp t (hinner t)
      have hsinhD : HasDerivAt (fun w : ℝ => Real.sinh (α * w))
          (Real.cosh (α * t) * α) t :=
        (Real.hasDerivAt_sinh (α * t)).comp t (hinner t)
      have hN : HasDerivAt
          (fun w => qR * (base (Rv m.gcoord) * Real.cosh (α * w) + qR * Real.sinh (α * w)))
          (qR * (base (Rv m.gcoord) * (Real.sinh (α * t) * α)
            + qR * (Real.cosh (α * t) * α))) t :=
        ((hcoshD.const_mul (base (Rv m.gcoord))).add (hsinhD.const_mul qR)).const_mul qR
      have hDD : HasDerivAt
          (fun w => qR * Real.cosh (α * w) + base (Rv m.gcoord) * Real.sinh (α * w))
          (qR * (Real.sinh (α * t) * α)
            + base (Rv m.gcoord) * (Real.cosh (α * t) * α)) t :=
        (hcoshD.const_mul qR).add (hsinhD.const_mul (base (Rv m.gcoord)))
      have hdiv := hN.div hDD (ne_of_gt hDpos)
      have hb' : (a : ℝ) / 1000000 * qR ^ 2 = (b : ℝ) := by
        rw [hq2]
        field_simp
      have hDN : (qR * Real.cosh (α * t) + base (Rv m.gcoord) * Real.sinh (α * t)) ^ 2
          - (base (Rv m.gcoord) * Real.cosh (α * t) + qR * Real.sinh (α * t)) ^ 2
          = qR ^ 2 - base (Rv m.gcoord) ^ 2 := by
        linear_combination (qR ^ 2 - base (Rv m.gcoord) ^ 2)
          * Real.cosh_sq_sub_sinh_sq (α * t)
      have heq : (qR * (base (Rv m.gcoord) * (Real.sinh (α * t) * α)
            + qR * (Real.cosh (α * t) * α))
            * (qR * Real.cosh (α * t) + base (Rv m.gcoord) * Real.sinh (α * t))
          - qR * (base (Rv m.gcoord) * Real.cosh (α * t) + qR * Real.sinh (α * t))
            * (qR * (Real.sinh (α * t) * α)
              + base (Rv m.gcoord) * (Real.cosh (α * t) * α)))
          / (qR * Real.cosh (α * t) + base (Rv m.gcoord) * Real.sinh (α * t)) ^ 2
          = (b : ℝ) - (a : ℝ) / 1000000 * (riccVal qR α (base (Rv m.gcoord)) t) ^ 2 := by
        rw [show qR * (base (Rv m.gcoord) * (Real.sinh (α * t) * α)
              + qR * (Real.cosh (α * t) * α))
              * (qR * Real.cosh (α * t) + base (Rv m.gcoord) * Real.sinh (α * t))
            - qR * (base (Rv m.gcoord) * Real.cosh (α * t) + qR * Real.sinh (α * t))
              * (qR * (Real.sinh (α * t) * α)
                + base (Rv m.gcoord) * (Real.cosh (α * t) * α))
            = qR * α
              * ((qR * Real.cosh (α * t) + base (Rv m.gcoord) * Real.sinh (α * t)) ^ 2
                - (base (Rv m.gcoord) * Real.cosh (α * t)
                  + qR * Real.sinh (α * t)) ^ 2) from by ring, hDN]
        have hqα : qR * α = (a : ℝ) / 1000000 * qR ^ 2 := by
          rw [hαdef]
          ring
        have hDne : qR * Real.cosh (α * t) + base (Rv m.gcoord) * Real.sinh (α * t) ≠ 0 :=
          ne_of_gt hDpos
        have hrv2 : (riccVal qR α (base (Rv m.gcoord)) t) ^ 2
            = qR ^ 2 * (base (Rv m.gcoord) * Real.cosh (α * t) + qR * Real.sinh (α * t)) ^ 2
              / (qR * Real.cosh (α * t) + base (Rv m.gcoord) * Real.sinh (α * t)) ^ 2 := by
          unfold riccVal
          rw [div_pow, mul_pow]
        rw [hrv2]
        rw [show (b : ℝ) - (a : ℝ) / 1000000
              * (qR ^ 2
                * (base (Rv m.gcoord) * Real.cosh (α * t) + qR * Real.sinh (α * t)) ^ 2
                / (qR * Real.cosh (α * t) + base (Rv m.gcoord) * Real.sinh (α * t)) ^ 2)
            = ((b : ℝ)
                * (qR * Real.cosh (α * t) + base (Rv m.gcoord) * Real.sinh (α * t)) ^ 2
              - (a : ℝ) / 1000000 * qR ^ 2
                * (base (Rv m.gcoord) * Real.cosh (α * t) + qR * Real.sinh (α * t)) ^ 2)
              / (qR * Real.cosh (α * t) + base (Rv m.gcoord) * Real.sinh (α * t)) ^ 2
          from by field_simp]
        rw [div_eq_div_iff (pow_ne_zero 2 hDne) (pow_ne_zero 2 hDne)]
        linear_combination
          (-(((a : ℝ) / 1000000) * qR ^ 2)
            * (qR * Real.cosh (α * t) + base (Rv m.gcoord) * Real.sinh (α * t)) ^ 2) * hDN
          + ((qR ^ 2 - base (Rv m.gcoord) ^ 2)
            * (qR * Real.cosh (α * t) + base (Rv m.gcoord) * Real.sinh (α * t)) ^ 2) * hqα
          + ((qR * Real.cosh (α * t) + base (Rv m.gcoord) * Real.sinh (α * t)) ^ 4) * hb'
      rw [← heq]
      exact hdiv.hasDerivWithinAt
    · have hfz := hfr i hig
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
          (riccΦ m qR α base t) = 0 := by
        simp [SettlingMode.fieldOf, hfz, CoordShape.field, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => riccΦ m qR α base u (Rv i)) = fun _ => base (Rv i) := by
        funext u
        rw [riccΦ_Rv, if_neg hig]
      rw [hcurve]
      exact hasDerivWithinAt_const t _ _
  · -- mask
    intro t ht x hx
    refine riccΦ_nonR m qR α base t ?_
    intro i hxi
    exact hx (by
      rw [hxi]
      simp only [rightBlock, ODESystem.bound, List.map_map]
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  · -- self-landing
    rw [sat_GdOf hq]
    obtain ⟨h1, h2⟩ := hband (M.dt : ℝ) hdt
    exact ⟨hstayEnv _ hdt, by rw [riccΦ_Rv, if_pos rfl]; exact h1,
      by rw [riccΦ_Rv, if_pos rfl]; exact h2⟩

/-! ### Extraction: the checker's Bool facts as Props -/

theorem checkMode_true {M : SettlingModel n} {q : ℕ} {m : SettlingMode n}
    (h : checkMode M q m = true) :
    m.glo ≤ m.ghi ∧
    (∀ l', (M.env m.gcoord).lo = some l' → l' ≤ m.glo) ∧
    (∀ h', (M.env m.gcoord).hi = some h' → m.ghi ≤ h') ∧
    (∀ q' ∈ m.succs, q' < M.modes.length) ∧
    (match m.shapes m.gcoord with
     | CoordShape.frozen => ∀ i, i ≠ m.gcoord → m.shapes i = CoordShape.frozen
     | CoordShape.contract k c =>
         -- EXT 4/4b: inside and above run over the base flex grammar; below (transit down)
         -- runs over the EXTENDED grammar (contract others, contract-driven integrators)
         0 ≤ k ∧
         ((FlexOthers M m ∧ 0 ≤ m.glo ∧
            ((m.glo ≤ c ∧ c ≤ m.ghi) ∨
             (m.ghi < c ∧ (∀ h', (M.env m.gcoord).hi = some h' → c ≤ h') ∧
               (∃ q' ∈ m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
                 m'.glo ≤ m.ghi ∧ c ≤ m'.ghi)))) ∨
          (FlexOthersC M m ∧ 0 ≤ m.glo ∧
            c < m.glo ∧ 0 ≤ c ∧ (∀ l', (M.env m.gcoord).lo = some l' → l' ≤ c) ∧
            (∃ q' ∈ m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
              m.glo ≤ m'.ghi ∧ m'.glo ≤ c)))
     | CoordShape.contractQ kn kd c =>
         FlexOthers M m ∧ 0 ≤ m.glo ∧ 0 ≤ kn ∧ 0 < kd ∧
         ((m.glo ≤ c ∧ c ≤ m.ghi) ∨
          (m.ghi < c ∧ (∀ h', (M.env m.gcoord).hi = some h' → c ≤ h') ∧
            (∃ q' ∈ m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
              m'.glo ≤ m.ghi ∧ m.ghi * kd + (c - m.ghi) * (kn * M.dt) ≤ m'.ghi * kd)) ∨
          (c < m.glo ∧ 0 ≤ c ∧ (∀ l', (M.env m.gcoord).lo = some l' → l' ≤ c) ∧
            (∃ q' ∈ m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
              m.glo ≤ m'.ghi ∧ m'.glo * kd ≤ m.glo * kd - (m.glo - c) * (kn * M.dt))))
     | CoordShape.constRate c =>
         -- EXT 4: the landing is a single covering band OR (sign-matched) the union of the
         -- own band with one contiguous successor band
         ((0 ≤ c ∧ FlexOthers M m ∧ 0 ≤ m.glo ∧
             (∀ h', (M.env m.gcoord).hi = some h' → m.ghi + c * M.dt ≤ h') ∧
             ((∃ q' ∈ q :: m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
                 m'.glo ≤ m.glo + c * M.dt ∧ m.ghi + c * M.dt ≤ m'.ghi) ∨
              (∃ q' ∈ m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
                 m'.glo ≤ m.ghi ∧ m.ghi + c * M.dt ≤ m'.ghi))) ∨
          (c < 0 ∧ (∀ i, i ≠ m.gcoord → m.shapes i = CoordShape.frozen) ∧
             (∀ l', (M.env m.gcoord).lo = some l' → l' ≤ m.glo + c * M.dt) ∧
             ((∃ q' ∈ q :: m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
                 m'.glo ≤ m.glo + c * M.dt ∧ m.ghi + c * M.dt ≤ m'.ghi) ∨
              (∃ q' ∈ m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
                 m.glo ≤ m'.ghi ∧ m'.glo ≤ m.glo + c * M.dt))))
     | CoordShape.driven _ => False
     | CoordShape.drivenDamp _ _ => False
     | CoordShape.chase j k =>
         j ≠ m.gcoord ∧ 0 < k ∧ 0 ≤ m.glo ∧ FlexOthersC M m ∧
         ∃ c ulo uhi, m.shapes j = CoordShape.contract k c ∧
           (M.env j).lo = some ulo ∧ (M.env j).hi = some uhi ∧
           (∃ q1 ∈ q :: m.succs, ∃ m1, M.modes[q1]? = some m1 ∧ m1.gcoord = m.gcoord ∧
             m1.glo ≤ m.glo ∧ 0 ≤ m1.glo ∧ k * m1.glo ≤ c ∧
             (∀ l', (M.env m.gcoord).lo = some l' → l' ≤ m1.glo) ∧
             (k * m1.glo ≤ ulo ∨
               (ulo - k * m1.glo) ^ 2 ≤ 2 * (c - k * m1.glo) * (k * m.glo - k * m1.glo)) ∧
             ∃ q2 ∈ q :: m.succs, ∃ m2, M.modes[q2]? = some m2 ∧ m2.gcoord = m.gcoord ∧
               m2.glo ≤ m1.ghi ∧ m.glo ≤ m2.ghi) ∧
           (∃ q3 ∈ q :: m.succs, ∃ m3, M.modes[q3]? = some m3 ∧ m3.gcoord = m.gcoord ∧
             m.ghi ≤ m3.ghi ∧ c ≤ k * m3.ghi ∧
             (∀ h', (M.env m.gcoord).hi = some h' → m3.ghi ≤ h') ∧
             (uhi ≤ k * m3.ghi ∨
               (k * m3.ghi - uhi) ^ 2 ≤ 2 * (k * m3.ghi - c) * (k * m3.ghi - k * m.ghi)) ∧
             ∃ q4 ∈ q :: m.succs, ∃ m4, M.modes[q4]? = some m4 ∧ m4.gcoord = m.gcoord ∧
               m4.glo ≤ m.ghi ∧ m3.glo ≤ m4.ghi)
     | CoordShape.pairSym j c h =>
         j ≠ m.gcoord ∧ m.shapes j = CoordShape.pairSym m.gcoord c h ∧
         0 < h ∧ 3 * h ≤ 1000 ∧ 0 ≤ m.glo ∧
         ∃ plo phi qlo qhi,
           (M.env m.gcoord).lo = some plo ∧ (M.env m.gcoord).hi = some phi ∧
           (M.env j).lo = some qlo ∧ (M.env j).hi = some qhi ∧ 0 ≤ qlo ∧
           (∀ i, i ≠ m.gcoord → i ≠ j →
             m.shapes i = CoordShape.frozen ∨
             ((m.shapes i = CoordShape.driven m.gcoord ∨ m.shapes i = CoordShape.driven j) ∧
               (M.env i).lo = none ∧ (M.env i).hi = none) ∨
             (∃ kn kd cc, m.shapes i = CoordShape.contractQ kn kd cc ∧ 0 ≤ kn ∧ 0 < kd ∧
               (∀ l', (M.env i).lo = some l' → l' ≤ cc) ∧
               (∀ h', (M.env i).hi = some h' → cc ≤ h')) ∨
             (∃ j2, m.shapes i = CoordShape.driven j2 ∧ j2 ≠ m.gcoord ∧ j2 ≠ j ∧
               (∃ kn2 kd2 cc2, m.shapes j2 = CoordShape.contractQ kn2 kd2 cc2 ∧ 0 < kd2) ∧
               (M.env i).lo = none ∧ (M.env i).hi = none)) ∧
           (PairConds m.glo m.ghi plo phi qlo qhi c h m.ghi ∨
             ∃ q' ∈ m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
               m'.glo ≤ m.ghi ∧ PairConds m.glo m.ghi plo phi qlo qhi c h m'.ghi)
     | CoordShape.riccati b a =>
         (∀ i, i ≠ m.gcoord → m.shapes i = CoordShape.frozen) ∧
         0 < b ∧ 0 < a ∧ 0 ≤ m.glo ∧
         m.glo^2 * a ≤ 1000000 * b ∧ 1000000 * b ≤ m.ghi^2 * a) := by
  unfold checkMode at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hord, hinside⟩, hsucc⟩, hshape⟩ := h
  have hloIn : ∀ l', (M.env m.gcoord).lo = some l' → l' ≤ m.glo := by
    intro l' hl'
    unfold bandInside at hinside
    rw [Bool.and_eq_true] at hinside
    have := hinside.1
    rw [hl'] at this
    simpa using this
  have hhiIn : ∀ h', (M.env m.gcoord).hi = some h' → m.ghi ≤ h' := by
    intro h' hh'
    unfold bandInside at hinside
    rw [Bool.and_eq_true] at hinside
    have := hinside.2
    rw [hh'] at this
    simpa using this
  -- the two others-conditions, decoded once
  have decodeFrozen : ∀ (b : Bool), b = ((List.finRange n).all fun i =>
      decide (i = m.gcoord) || decide (m.shapes i = CoordShape.frozen)) → b = true →
      ∀ i, i ≠ m.gcoord → m.shapes i = CoordShape.frozen := by
    intro b hbdef hb i hi
    rw [hbdef, List.all_eq_true] at hb
    have := hb i (List.mem_finRange i)
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    rcases this with h1 | h2
    · exact absurd h1 hi
    · exact h2
  have decodeFlex : ∀ (b : Bool), b = (decide (0 ≤ m.glo) &&
      ((List.finRange n).all fun i =>
        decide (i = m.gcoord) || decide (m.shapes i = CoordShape.frozen) ||
        (decide (m.shapes i = CoordShape.driven m.gcoord) &&
          decide ((M.env i).hi = none)) ||
        (match m.shapes i with
         | CoordShape.driven j =>
             !decide (j = m.gcoord) && decide (m.shapes j = CoordShape.frozen) &&
             decide ((M.env i).lo = none) && decide ((M.env i).hi = none)
         | _ => false))) → b = true → 0 ≤ m.glo ∧ FlexOthers M m := by
    intro b hbdef hb
    rw [hbdef, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨hglo0, hall⟩ := hb
    rw [List.all_eq_true] at hall
    refine ⟨hglo0, ?_⟩
    intro i hi
    have := hall i (List.mem_finRange i)
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    rcases this with ((h1 | h2) | h3) | h4
    · exact absurd h1 hi
    · exact Or.inl h2
    · exact Or.inr (Or.inl h3)
    · rcases hshx : m.shapes i with _ | _ | _ | _ | j | _ | _ | _ | _
      all_goals rw [hshx] at h4
      · simp at h4
      · simp at h4
      · simp at h4
      · simp at h4
      · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
          decide_eq_false_iff_not] at h4
        exact Or.inr (Or.inr ⟨j, rfl, h4.1.1.1, h4.1.1.2, h4.1.2, h4.2⟩)
      · simp at h4
      · simp at h4
      · simp at h4
      · simp at h4
  have decodeFlexC : ∀ (b : Bool), b = (decide (0 ≤ m.glo) &&
      ((List.finRange n).all fun i =>
        decide (i = m.gcoord) || decide (m.shapes i = CoordShape.frozen) ||
        (decide (m.shapes i = CoordShape.driven m.gcoord) &&
          decide ((M.env i).hi = none)) ||
        (match m.shapes i with
         | CoordShape.driven j =>
             !decide (j = m.gcoord) && decide (m.shapes j = CoordShape.frozen) &&
             decide ((M.env i).lo = none) && decide ((M.env i).hi = none)
         | _ => false) ||
        (match m.shapes i with
         | CoordShape.contract k' c' =>
             decide (0 ≤ k') &&
             ((M.env i).lo.all fun lo => decide (lo ≤ c')) &&
             ((M.env i).hi.all fun hi => decide (c' ≤ hi))
         | _ => false) ||
        (match m.shapes i with
         | CoordShape.driven j =>
             !decide (j = m.gcoord) &&
             (match m.shapes j with
              | CoordShape.contract _ _ => true
              | _ => false) &&
             decide ((M.env i).lo = none) && decide ((M.env i).hi = none)
         | _ => false))) → b = true → 0 ≤ m.glo ∧ FlexOthersC M m := by
    intro b hbdef hb
    rw [hbdef, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨hglo0, hall2⟩ := hb
    rw [List.all_eq_true] at hall2
    refine ⟨hglo0, ?_⟩
    intro i hi
    have := hall2 i (List.mem_finRange i)
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    rcases this with ((((h1 | h2) | h3) | h4) | h5) | h6
    · exact absurd h1 hi
    · exact Or.inl h2
    · exact Or.inr (Or.inl h3)
    · rcases hshx : m.shapes i with _ | _ | _ | _ | j | _ | _ | _ | _
      all_goals rw [hshx] at h4
      · simp at h4
      · simp at h4
      · simp at h4
      · simp at h4
      · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
          decide_eq_false_iff_not] at h4
        exact Or.inr (Or.inr (Or.inl ⟨j, rfl, h4.1.1.1, h4.1.1.2, h4.1.2, h4.2⟩))
      · simp at h4
      · simp at h4
      · simp at h4
      · simp at h4
    · rcases hshx : m.shapes i with _ | _ | ⟨k', c'⟩ | _ | _ | _ | _ | _ | _
      all_goals rw [hshx] at h5
      · simp at h5
      · simp at h5
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h5
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨k', c', rfl, h5.1.1, ?_, ?_⟩)))
        · intro l' hl'
          have := h5.1.2
          rw [hl'] at this
          simpa using this
        · intro h' hh'
          have := h5.2
          rw [hh'] at this
          simpa using this
      · simp at h5
      · simp at h5
      · simp at h5
      · simp at h5
      · simp at h5
      · simp at h5
    · rcases hshx : m.shapes i with _ | _ | _ | _ | j | _ | _ | _ | _
      all_goals rw [hshx] at h6
      · simp at h6
      · simp at h6
      · simp at h6
      · simp at h6
      · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
          decide_eq_false_iff_not] at h6
        obtain ⟨⟨⟨hjne, hjc⟩, hlo⟩, hhi⟩ := h6
        rcases hshj : m.shapes j with _ | _ | ⟨kj, cj⟩ | _ | _ | _ | _ | _ | _
        all_goals rw [hshj] at hjc
        · simp at hjc
        · simp at hjc
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨j, kj, cj, rfl, hjne, hshj, hlo, hhi⟩)))
        · simp at hjc
        · simp at hjc
        · simp at hjc
        · simp at hjc
        · simp at hjc
        · simp at hjc
      · simp at h6
      · simp at h6
      · simp at h6
      · simp at h6
  refine ⟨hord, hloIn, hhiIn, hsucc, ?_⟩
  rcases hsh : m.shapes m.gcoord with _ | c | ⟨k, c⟩ | ⟨kn, kd, c⟩ | j | ⟨j, ds⟩ | ⟨b, a⟩
    | ⟨j, c, h⟩ | ⟨j, k⟩
  all_goals rw [hsh] at hshape
  · -- frozen
    exact decodeFrozen _ rfl hshape
  · -- constRate: signed split, single-or-union landing
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hshape
    obtain ⟨hbranch, hland⟩ := hshape
    -- the single-band option, decoded once (sign-independent)
    have decodeSingle : ((q :: m.succs).any fun q' =>
        match M.modes[q']? with
        | some m' =>
            decide (m'.gcoord = m.gcoord) &&
            decide (m'.glo ≤ m.glo + c * M.dt) && decide (m.ghi + c * M.dt ≤ m'.ghi)
        | none => false) = true →
        ∃ q' ∈ q :: m.succs, ∃ m', M.modes[q']? = some m' ∧ m'.gcoord = m.gcoord ∧
          m'.glo ≤ m.glo + c * M.dt ∧ m.ghi + c * M.dt ≤ m'.ghi := by
      intro hany
      rw [List.any_eq_true] at hany
      obtain ⟨q', hq'mem, hq'⟩ := hany
      rcases hm' : M.modes[q']? with _ | m'
      · rw [hm'] at hq'; simp at hq'
      · rw [hm'] at hq'
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
        exact ⟨q', hq'mem, m', hm', hq'.1.1, hq'.1.2, hq'.2⟩
    rcases hbranch with ⟨⟨hc, hflexB⟩, hmarB⟩ | ⟨⟨hcneg, hfrB⟩, hloB⟩
    · -- 0 ≤ c: the union option's `if` reduces to the upper-edge shape
      obtain ⟨hglo0, hflex⟩ := decodeFlex _ rfl (by
        rw [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hflexB.1, hflexB.2⟩)
      refine Or.inl ⟨hc, hflex, hglo0, ?_, ?_⟩
      · intro h' hh'
        rw [hh'] at hmarB
        simpa using hmarB
      · rcases hland with hsingle | hunion
        · exact Or.inl (decodeSingle hsingle)
        · rw [List.any_eq_true] at hunion
          obtain ⟨q', hq'mem, hq'⟩ := hunion
          rcases hm' : M.modes[q']? with _ | m'
          · rw [hm'] at hq'; simp at hq'
          · rw [hm'] at hq'
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
            rw [if_pos hc] at hq'
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
            exact Or.inr ⟨q', hq'mem, m', hm', hq'.1, hq'.2.1, hq'.2.2⟩
    · -- c < 0: the union option's `if` reduces to the lower-edge shape
      refine Or.inr ⟨hcneg, decodeFrozen _ rfl hfrB, ?_, ?_⟩
      · intro l' hl'
        rw [hl'] at hloB
        simpa using hloB
      · rcases hland with hsingle | hunion
        · exact Or.inl (decodeSingle hsingle)
        · rw [List.any_eq_true] at hunion
          obtain ⟨q', hq'mem, hq'⟩ := hunion
          rcases hm' : M.modes[q']? with _ | m'
          · rw [hm'] at hq'; simp at hq'
          · rw [hm'] at hq'
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
            rw [if_neg (not_le.mpr hcneg)] at hq'
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
            exact Or.inr ⟨q', hq'mem, m', hm', hq'.1, hq'.2.1, hq'.2.2⟩
  · -- contract: inside/above over the base grammar, below over the extended grammar
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hshape
    obtain ⟨hk, hdisj⟩ := hshape
    refine ⟨hk, ?_⟩
    rcases hdisj with ⟨hflexB, hio⟩ | ⟨hflexCB, ⟨⟨⟨hcl, hc0⟩, hloB⟩, hany⟩⟩
    · obtain ⟨hglo0, hflex⟩ := decodeFlex _ rfl (by
        rw [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hflexB.1, hflexB.2⟩)
      refine Or.inl ⟨hflex, hglo0, ?_⟩
      rcases hio with ⟨hcl, hch⟩ | ⟨⟨hch, hhiB⟩, hany⟩
      · exact Or.inl ⟨hcl, hch⟩
      · refine Or.inr ⟨hch, ?_, ?_⟩
        · intro h' hh'
          rw [hh'] at hhiB
          simpa using hhiB
        · rw [List.any_eq_true] at hany
          obtain ⟨q', hq'mem, hq'⟩ := hany
          rcases hm' : M.modes[q']? with _ | m'
          · rw [hm'] at hq'; simp at hq'
          · rw [hm'] at hq'
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
            exact ⟨q', hq'mem, m', hm', hq'.1.1, hq'.1.2, hq'.2⟩
    · obtain ⟨hglo0, hflexC⟩ := decodeFlexC _ rfl (by
        rw [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hflexCB.1, hflexCB.2⟩)
      refine Or.inr ⟨hflexC, hglo0, hcl, hc0, ?_, ?_⟩
      · intro l' hl'
        rw [hl'] at hloB
        simpa using hloB
      · rw [List.any_eq_true] at hany
        obtain ⟨q', hq'mem, hq'⟩ := hany
        rcases hm' : M.modes[q']? with _ | m'
        · rw [hm'] at hq'; simp at hq'
        · rw [hm'] at hq'
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
          exact ⟨q', hq'mem, m', hm', hq'.1.1, hq'.1.2, hq'.2⟩
  · -- contractQ: same 3-way landing, gains kn/kd, cross-multiplied covers
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hshape
    obtain ⟨⟨⟨hflexB, hkn⟩, hkd⟩, hdisj⟩ := hshape
    obtain ⟨hglo0, hflex⟩ := decodeFlex _ rfl (by
      rw [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hflexB.1, hflexB.2⟩)
    refine ⟨hflex, hglo0, hkn, hkd, ?_⟩
    rcases hdisj with (⟨hcl, hch⟩ | ⟨⟨hch, hhiB⟩, hany⟩) | ⟨⟨⟨hcl, hc0⟩, hloB⟩, hany⟩
    · exact Or.inl ⟨hcl, hch⟩
    · refine Or.inr (Or.inl ⟨hch, ?_, ?_⟩)
      · intro h' hh'
        rw [hh'] at hhiB
        simpa using hhiB
      · rw [List.any_eq_true] at hany
        obtain ⟨q', hq'mem, hq'⟩ := hany
        rcases hm' : M.modes[q']? with _ | m'
        · rw [hm'] at hq'; simp at hq'
        · rw [hm'] at hq'
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
          exact ⟨q', hq'mem, m', hm', hq'.1.1, hq'.1.2, hq'.2⟩
    · refine Or.inr (Or.inr ⟨hcl, hc0, ?_, ?_⟩)
      · intro l' hl'
        rw [hl'] at hloB
        simpa using hloB
      · rw [List.any_eq_true] at hany
        obtain ⟨q', hq'mem, hq'⟩ := hany
        rcases hm' : M.modes[q']? with _ | m'
        · rw [hm'] at hq'; simp at hq'
        · rw [hm'] at hq'
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
          exact ⟨q', hq'mem, m', hm', hq'.1.1, hq'.1.2, hq'.2⟩
  · simp at hshape
  · simp at hshape
  · -- riccati
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hshape
    obtain ⟨⟨⟨⟨⟨hfrB, hb⟩, ha⟩, hglo0⟩, hql⟩, hqh⟩ := hshape
    exact ⟨decodeFrozen _ rfl hfrB, hb, ha, hglo0, hql, hqh⟩
  · -- pairSym (EXT P)
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not] at hshape
    obtain ⟨⟨⟨⟨⟨hjne, hjsh⟩, hh0⟩, hh3⟩, hglo0⟩, henvm⟩ := hshape
    rcases hplo : (M.env m.gcoord).lo with _ | plo <;>
      rcases hphi : (M.env m.gcoord).hi with _ | phi <;>
      rcases hqloE : (M.env j).lo with _ | qlo <;>
      rcases hqhiE : (M.env j).hi with _ | qhi
    all_goals rw [hplo, hphi, hqloE, hqhiE] at henvm
    case _ => simp at henvm
    case _ => simp at henvm
    case _ => simp at henvm
    case _ => simp at henvm
    case _ => simp at henvm
    case _ => simp at henvm
    case _ => simp at henvm
    case _ => simp at henvm
    case _ => simp at henvm
    case _ => simp at henvm
    case _ => simp at henvm
    case _ => simp at henvm
    case _ => simp at henvm
    case _ => simp at henvm
    case _ => simp at henvm
    · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
        List.all_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at henvm
      obtain ⟨⟨⟨hqlo0, hothB⟩, -⟩, hcovB⟩ := henvm
      refine ⟨hjne, hjsh, hh0, hh3, hglo0, plo, phi, qlo, qhi, rfl, rfl, hqloE, hqhiE,
        hqlo0, ?_, ?_⟩
      · intro i hig hij
        have hthis := hothB i (List.mem_finRange i)
        rcases hthis with (((h1 | h1) | h2) | h3) | h4
        · exact absurd h1 hig
        · exact absurd h1 hij
        · exact Or.inl h2
        · exact Or.inr (Or.inl ⟨h3.1.1, h3.1.2, h3.2⟩)
        · rcases hshx : m.shapes i with _ | _ | _ | ⟨kn, kd, cc⟩ | j2 | _ | _ | _ | _
          all_goals rw [hshx] at h4
          · simp at h4
          · simp at h4
          · simp at h4
          · simp only [Bool.and_eq_true, decide_eq_true_eq] at h4
            refine Or.inr (Or.inr (Or.inl ⟨kn, kd, cc, rfl, h4.1.1.1, h4.1.1.2, ?_, ?_⟩))
            · intro l' hl'
              have := h4.1.2
              rw [hl'] at this
              simpa using this
            · intro h' hh'
              have := h4.2
              rw [hh'] at this
              simpa using this
          · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
              decide_eq_false_iff_not] at h4
            obtain ⟨⟨⟨⟨hj2g, hj2j⟩, hj2cqB⟩, hloN⟩, hhiN⟩ := h4
            rcases hshj2 : m.shapes j2 with _ | _ | _ | ⟨kn2, kd2, cc2⟩ | _ | _ | _ | _ | _
            all_goals rw [hshj2] at hj2cqB
            · simp at hj2cqB
            · simp at hj2cqB
            · simp at hj2cqB
            · refine Or.inr (Or.inr (Or.inr ⟨j2, rfl, hj2g, hj2j,
                ⟨kn2, kd2, cc2, hshj2, by simpa using hj2cqB⟩, hloN, hhiN⟩))
            · simp at hj2cqB
            · simp at hj2cqB
            · simp at hj2cqB
            · simp at hj2cqB
            · simp at hj2cqB
          · simp at h4
          · simp at h4
          · simp at h4
          · simp at h4
      · rcases hcovB with hself | hsucc
        · exact Or.inl (pairCondsB_true hself)
        · rw [List.any_eq_true] at hsucc
          obtain ⟨q', hq'mem, hq'⟩ := hsucc
          rcases hm' : M.modes[q']? with _ | m'
          · rw [hm'] at hq'; simp at hq'
          · rw [hm'] at hq'
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
            exact Or.inr ⟨q', hq'mem, m', hm', hq'.1.1, hq'.1.2,
              pairCondsB_true hq'.2⟩
  · -- chase (EXT G)
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not] at hshape
    obtain ⟨⟨⟨hjne, hkpos⟩, hflexCB⟩, hmatch⟩ := hshape
    obtain ⟨hglo0C, hflexC⟩ := decodeFlexC _ rfl (by
      rw [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hflexCB.1, hflexCB.2⟩)
    rcases hjs : m.shapes j with _ | _ | ⟨k2, c⟩ | _ | _ | _ | _ | _ | _
    all_goals rw [hjs] at hmatch
    · simp at hmatch
    · simp at hmatch
    · rcases hulo : (M.env j).lo with _ | ulo <;> rcases huhi : (M.env j).hi with _ | uhi
      all_goals rw [hulo, huhi] at hmatch
      · simp at hmatch
      · simp at hmatch
      · simp at hmatch
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hmatch
        obtain ⟨⟨hk2, hanyLo⟩, hanyHi⟩ := hmatch
        subst hk2
        refine ⟨hjne, hkpos, hglo0C, hflexC, c, ulo, uhi, hjs, hulo, huhi, ?_, ?_⟩
        · rw [List.any_eq_true] at hanyLo
          obtain ⟨q1, hq1mem, hq1⟩ := hanyLo
          rcases hm1 : M.modes[q1]? with _ | m1
          · rw [hm1] at hq1; simp at hq1
          · rw [hm1] at hq1
            simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hq1
            obtain ⟨⟨⟨⟨⟨⟨hgc1, h1glo⟩, h1nn⟩, h1kc⟩, hloB⟩, hbr⟩, hany2⟩ := hq1
            refine ⟨q1, hq1mem, m1, hm1, hgc1, h1glo, h1nn, h1kc, ?_, hbr, ?_⟩
            · intro l' hl'
              rw [hl'] at hloB
              simpa using hloB
            · rw [List.any_eq_true] at hany2
              obtain ⟨q2, hq2mem, hq2⟩ := hany2
              rcases hm2 : M.modes[q2]? with _ | m2
              · rw [hm2] at hq2; simp at hq2
              · rw [hm2] at hq2
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hq2
                exact ⟨q2, hq2mem, m2, hm2, hq2.1.1, hq2.1.2, hq2.2⟩
        · rw [List.any_eq_true] at hanyHi
          obtain ⟨q3, hq3mem, hq3⟩ := hanyHi
          rcases hm3 : M.modes[q3]? with _ | m3
          · rw [hm3] at hq3; simp at hq3
          · rw [hm3] at hq3
            simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hq3
            obtain ⟨⟨⟨⟨⟨hgc3, h3ghi⟩, h3kc⟩, hhiB⟩, hbr⟩, hany4⟩ := hq3
            refine ⟨q3, hq3mem, m3, hm3, hgc3, h3ghi, h3kc, ?_, hbr, ?_⟩
            · intro h' hh'
              rw [hh'] at hhiB
              simpa using hhiB
            · rw [List.any_eq_true] at hany4
              obtain ⟨q4, hq4mem, hq4⟩ := hany4
              rcases hm4 : M.modes[q4]? with _ | m4
              · rw [hm4] at hq4; simp at hq4
              · rw [hm4] at hq4
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hq4
                exact ⟨q4, hq4mem, m4, hm4, hq4.1.1, hq4.1.2, hq4.2⟩
    · simp at hmatch
    · simp at hmatch
    · simp at hmatch
    · simp at hmatch
    · simp at hmatch
    · simp at hmatch

/-! ### The assembly: `wellformed_sound` -/

/-- **The checker is sound**: passing `decideWellFormed`, plus the freshness side-conditions
and the per-run certificates, yields the settling hypothesis — hence
`theorem3_faithful_settling` applies to the transcribed model. -/
theorem wellformed_sound (M : SettlingModel n) (mv tg : Var n) (g : Term (Var n))
    (fL : Fin n → Term (Var n)) : WellFormedSound M mv tg g fL := by
  intro hwf hdt hg hmvclk hmvtg hmvGd htgGd hfrzGd
  unfold decideWellFormed at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hwf
  obtain ⟨⟨-, -⟩, hall⟩ := hwf
  have hcheck : ∀ q (m : SettlingMode n), M.modes[q]? = some m → checkMode M q m = true := by
    intro q m hqm
    have hqlt : q < M.modes.length := (List.getElem?_eq_some_iff.mp hqm).1
    have := hall q (List.mem_range.mpr hqlt)
    rw [hqm] at this
    exact this
  refine ⟨hdt, hg, hmvclk, hmvtg, hmvGd, htgGd, hfrzGd, ?_⟩
  intro q m' hm'
  rw [graph_modeAt] at hm'
  obtain ⟨SM, hSM, rfl⟩ := Option.map_eq_some_iff.mp hm'
  obtain ⟨hord, hloIn, hhiIn, hsucclen, hshape⟩ := checkMode_true (hcheck q SM hSM)
  have hqlt : q < M.modes.length := (List.getElem?_eq_some_iff.mp hSM).1
  have hlen : M.graph.modes.length = M.modes.length := by
    unfold SettlingModel.graph; simp
  have hmodeAt : M.graph.modeAt q = some (SM.toRMode M) := by
    rw [graph_modeAt, hSM]; rfl
  refine ⟨SM.fieldOf, rfl, rfl, by rw [hlen]; exact hqlt, ?_, ?_, ?_, ?_⟩
  · -- GuardSettlingB, by shape
    rcases hsh : SM.shapes SM.gcoord with _ | c | ⟨k, c⟩ | ⟨kn, kd, c⟩ | j | ⟨j, ds⟩ | ⟨b, a⟩
      | ⟨j, c, h⟩ | ⟨j, k⟩
    all_goals rw [hsh] at hshape
    · exact settling_frozen M hSM hsh hshape hdt
    · rcases hshape with ⟨hc, hflex, hglo0, hmar, hland⟩ | ⟨hcneg, hfr, hlomar, hland⟩
      · exact settling_const_driven M hSM hsh hflex hglo0 hc hloIn hmar hland hdt
      · exact settling_const_neg M hSM hsh hfr hcneg hlomar hhiIn hland hdt
    · obtain ⟨hk, hdisj⟩ := hshape
      rcases hdisj with ⟨hflex, hglo0, hio⟩ | ⟨hflexC, hglo0, hcl, hc0, hEnvLo, hcover⟩
      · rcases hio with ⟨hcl, hch⟩ | ⟨hch, hEnvHi, hcover⟩
        · exact settling_contract_driven M hSM hsh hflex hglo0 hk hcl hch hloIn hhiIn hdt
        · exact settling_contract_above M hSM hsh hflex hglo0 hk hch hloIn hEnvHi hcover hdt
      · exact settling_contract_below_flex M hSM hsh hflexC hglo0 hk hcl hc0 hEnvLo hhiIn
          hcover hdt
    · obtain ⟨hflex, hglo0, hkn, hkd, hdisj⟩ := hshape
      rcases hdisj with ⟨hcl, hch⟩ | ⟨hch, hEnvHi, hcover⟩ | ⟨hcl, hc0, hEnvLo, hcover⟩
      · exact settling_contractQ_driven M hSM hsh hflex hglo0 hkn hkd hcl hch hloIn hhiIn hdt
      · exact settling_contractQ_above M hSM hsh hflex hglo0 hkn hkd hch hloIn hEnvHi hcover hdt
      · exact settling_contractQ_below M hSM hsh hflex hglo0 hkn hkd hcl hc0 hEnvLo hhiIn
          hcover hdt
    · exact absurd hshape not_false
    · exact absurd hshape not_false
    · obtain ⟨hfr, hb, ha, hglo0, hql, hqh⟩ := hshape
      exact settling_riccati M hSM hsh hfr hb ha hglo0 hord hql hqh hloIn hhiIn hdt
    · obtain ⟨hjne, hjsh, hh0, hh3, hglo0, plo, phi, qlo, qhi, hplo, hphi, hqloE, hqhiE,
        hqlo0, hOth, hcov⟩ := hshape
      exact settling_pair M hSM hsh hjne hjsh hh0 hh3 hglo0 hplo hphi hqloE hqhiE hqlo0
        hOth hcov hdt
    · obtain ⟨hjne, hkpos, -, hflexC, c, ulo, uhi, hjshC, hjlo, hjhi, hcovLo, hcovHi⟩ := hshape
      exact settling_chaseG M hSM hsh hjne hjshC hkpos hflexC hjlo hjhi hcovLo hcovHi hdt
  · exact ⟨_, self_edge_mem M hSM, rfl, rfl⟩
  · exact retainedSucc_edges M hSM hsucclen
  · intro q' _ hq'
    exact graph_modeAll M q' hq'

/-- The relational `g`-preservation obligation (quarantined shape, see `GBoxAll`) threaded
from the per-mode `BoxLe` certificates. Kept as a separate helper so the single-system H
stays clean; the paper-faithful replacement is task H's per-piece certificates. -/
theorem wellformed_gbox (M : SettlingModel n) (g : Term (Var n))
    (hcert : ∀ q m, M.graph.modeAt q = some m → ∀ ν, Formula.sat (M.GdOf q) ν →
        BoxLe (Program.ode m.sys M.envF) (fun ω => Term.eval g ω) ν) :
    GBoxAll M.graph M.GdOf g (Term.const 1) M.envF := by
  intro q m hmode fR hsys ν hν
  have := hcert q m hmode ν hν
  rwa [hsys] at this

/-! ### A concrete instance — watertank's settling model, checker-accepted by `decide`

`x' = 3(cᵢ − 0.12 x)`-style tanks normalize to the contract shape `k(c − x)`; the three modes
below use the equilibria/bands of the (normalized) watertank right side. The point is the
DECIDABILITY: `decideWellFormed` evaluates by `decide` — kernel-checked integer arithmetic,
no `native_decide` — so a benchmark's well-formedness certificate is one `rfl`-class fact,
and `wellformed_sound` turns it plus the per-run Z3 certificates into `GuardSettlingH`. -/

/-- Watertank-shaped settling model (1 coordinate, 3 contract modes, bands inside `[-1, 30]`). -/
def watertankM : SettlingModel 1 :=
  { modes :=
      [ { shapes := fun _ => CoordShape.contract 3 12, gcoord := 0,
          glo := 0, ghi := 13, succs := [1] }
      , { shapes := fun _ => CoordShape.contract 3 20, gcoord := 0,
          glo := 13, ghi := 20, succs := [2] }
      , { shapes := fun _ => CoordShape.contract 3 3, gcoord := 0,
          glo := 3, ghi := 28, succs := [0] } ]
    env := fun _ => { lo := some (-1), hi := some 30 }
    dtQ := 1 }

/-- The checker accepts it — by kernel computation. -/
example : decideWellFormed watertankM = true := rfl

end RelCertifier
