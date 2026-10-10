/-
# EXT 3 — the terrain checker: box guards over a driven position coordinate

**Status.** Part of the settling / `Faithful` route (per-benchmark settling, terrain and
affine models of the legacy suite, kernel-certified against the parsed IR). Its
per-benchmark batteries (`SettlingInstances`, `TerrainInstances`, `AffineInstances`,
`FaithfulCerts`, `RealInstances`) were retired with the legacy suite (git history); the
suite_v2 theorems use the modal chain instead. The generic definitions and lemmas stay
compiled as part of the soundness development.

The s-guarded terrain class: each mode's guard constrains TWO coordinates — the active
velocity `v` (contract toward the cap, with `ghi = c` exactly: the cap-at-equilibrium
discipline from Arc 3) and a position `s` DRIVEN by it (`s' = v`), banded into terrain
segments `[slo, shi]` with the terminal segment unbounded (`shi = none` — the terminal-band
fix). Non-guarded coordinates are frozen or contract to an equilibrium inside their envelope
band (the attitude-decay coordinates `ψ' = −ψ`).

DESIGN: a `TerrainModel` WRAPS a `SettlingModel` (`core`) and adds the per-mode s-bands, so
the whole transcription stack — `envF`, the graph, and every graph lemma — is reused verbatim
from `WellFormedChecker`; only the guard map `TerrainModel.GdOf` (the box: core band ∧ s-band)
and the discharge are new. `GuardSettlingH` takes the guard map as a parameter, so
`theorem3_faithful_settling` consumes `wellformed_sound_terrain`'s conclusion unchanged.

THE SETTLING GEOMETRY (why the checker's conditions suffice):
* `v(t) = c + (v₀ − c)e^{−kt}` stays in `[v₀, c] ⊆ [glo, ghi]` (since `ghi = c`), so the
  v-half of EVERY box (own, or a successor's with `glo' ≤ glo ∧ c ≤ ghi'`) is automatic;
* `s(t) = s₀ + c·t + (v₀ − c)·expInt k t` is monotone (`v ≥ v₀ ≥ glo ≥ 0`) and bounded above
  by `s₀ + c·t` (`expInt ≥ 0`, `v₀ ≤ c`), so the one-step image sits in `[s₀, s₀ + c·dt]`;
* landing is an endpoint case-split at `shi`: at or below → the own box; above → the declared
  successor whose segment starts at or below `shi` and ends beyond the image
  (`shi + c·dt ≤ shi'`, or `shi' = none` for the terminal segment);
* a contract-shaped other coordinate stays in the hull of its base and its equilibrium, and
  the checker requires the equilibrium inside the coordinate's envelope band — interval
  convexity does the rest.

TRUST: definitions + decidable functions; no `native_decide`; the discharge lemma and the
assembly are axioms-clean (`propext, Classical.choice, Quot.sound`).
-/
import RelCertifier.Checker.WellFormedChecker

namespace RelCertifier
open DL Function Set

variable {n : ℕ}

/-! ## The terrain model: a settling core plus per-mode position bands -/

/-- One mode's position band: the driven coordinate and its terrain segment `[slo, shi]`
(`shi = none` = the unbounded terminal segment). -/
structure SBand (n : ℕ) where
  sc  : Fin n
  slo : ℤ
  shi : Option ℤ
  deriving Repr, DecidableEq

/-- A terrain model: the settling core (modes, envelope, budget) plus the s-bands, indexed
in step with `core.modes`. -/
structure TerrainModel (n : ℕ) where
  core   : SettlingModel n
  sbands : List (SBand n)

/-- The terrain guard map: the core guard box (envelope ∧ v-band) intersected with the
s-band. -/
noncomputable def TerrainModel.GdOf (T : TerrainModel n) : ℕ → Formula (Var n) :=
  fun q => match T.sbands[q]? with
    | some sb =>
        Formula.and (T.core.GdOf q) (Formula.and
          (Formula.cmp CompOp.le (Term.const (sb.slo : ℝ)) (Term.var (Rv sb.sc)))
          (match sb.shi with
           | some sh => Formula.cmp CompOp.le (Term.var (Rv sb.sc)) (Term.const (sh : ℝ))
           | none => Formula.tt))
    | none => Formula.tt

/-- **Reflection**: terrain guard satisfaction = core box ∧ s-band membership. -/
theorem sat_GdOfT {T : TerrainModel n} {q : ℕ} {m : SettlingMode n} {sb : SBand n}
    (hq : T.core.modes[q]? = some m) (hsb : T.sbands[q]? = some sb) {μ : State (Var n)} :
    Formula.sat (T.GdOf q) μ ↔
      (Formula.sat T.core.envF μ ∧ (m.glo : ℝ) ≤ μ (Rv m.gcoord)
        ∧ μ (Rv m.gcoord) ≤ (m.ghi : ℝ))
      ∧ (sb.slo : ℝ) ≤ μ (Rv sb.sc)
      ∧ (∀ sh, sb.shi = some sh → μ (Rv sb.sc) ≤ (sh : ℝ)) := by
  unfold TerrainModel.GdOf
  rw [hsb]
  cases hshi : sb.shi with
  | none =>
      simp only [Formula.sat, CompOp.interp, Term.eval, hshi]
      rw [sat_GdOf hq]
      simp
  | some sh =>
      simp only [Formula.sat, CompOp.interp, Term.eval, hshi]
      rw [sat_GdOf hq]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, fun sh' hsh' => by cases hsh'; exact h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, h3 sh rfl⟩

/-! ## The checker (computable, ℤ arithmetic) -/

/-- One terrain mode's check (see the header for the geometry each conjunct backs). -/
def checkModeT (M : SettlingModel n) (sbands : List (SBand n)) (m : SettlingMode n)
    (sb : SBand n) : Bool :=
  let dt := M.dt
  match m.shapes m.gcoord with
  | CoordShape.contract k c =>
      decide (0 ≤ k) && decide (m.glo ≤ c) && decide (c ≤ m.ghi) && decide (0 ≤ m.glo) &&
      decide (m.glo ≤ m.ghi) && bandInside m.glo m.ghi (M.env m.gcoord) &&
      !decide (sb.sc = m.gcoord) &&
      -- the position is driven plain (`s' = v`) or damped (EXT 3b: `s' = v(1 − Σ a ψ²)`,
      -- each damper contract-to-0 with its equilibrium inside its envelope band and the
      -- per-damper budget `a·B²·L ≤ 1`)
      (decide (m.shapes sb.sc = CoordShape.driven m.gcoord) ||
       (match m.shapes sb.sc with
        | CoordShape.drivenDamp j dampers =>
            decide (j = m.gcoord) &&
            (dampers.all (fun d =>
              !decide (d.1 = m.gcoord) && !decide (d.1 = sb.sc) &&
              decide (0 ≤ d.2.1) && decide (0 < d.2.2) &&
              (match m.shapes d.1 with
               | CoordShape.contract kp cp => decide (0 ≤ kp) && decide (cp = 0)
               | _ => false) &&
              (match (M.env d.1).lo, (M.env d.1).hi with
               | some lo, some hi =>
                   decide (lo ≤ 0) && decide (0 ≤ hi) &&
                   decide (d.2.1 * (max (-lo) hi)^2 * (dampers.length : ℤ) ≤ d.2.2)
               | _, _ => false)) ||
             -- cascade dampers (EXT 4c): each damper is a chase coordinate; its band
             -- conditions give the pointwise |ψ(u)| ≤ B for the same budget geometry
             dampers.all (fun d =>
              !decide (d.1 = m.gcoord) && !decide (d.1 = sb.sc) &&
              decide (0 ≤ d.2.1) && decide (0 < d.2.2) &&
              (match m.shapes d.1 with
               | CoordShape.chase jd kd =>
                   decide (0 < kd) &&
                   (match (M.env d.1).lo, (M.env d.1).hi,
                          (M.env jd).lo, (M.env jd).hi with
                    | some lo, some hi, some loj, some hij =>
                        decide (lo ≤ 0) && decide (0 ≤ hi) &&
                        decide (hij ≤ kd * hi) && decide (kd * lo ≤ loj) &&
                        decide (d.2.1 * (max (-lo) hi)^2 * (dampers.length : ℤ) ≤ d.2.2)
                    | _, _, _, _ => false)
               | _ => false)))
        | _ => false)) &&
      ((M.env sb.sc).lo.all fun lo => decide (lo ≤ sb.slo)) &&
      decide ((M.env sb.sc).hi = none) &&
      ((List.finRange n).all fun i =>
        decide (i = m.gcoord) || decide (i = sb.sc) ||
        decide (m.shapes i = CoordShape.frozen) ||
        (match m.shapes i with
         | CoordShape.contract k' c' =>
             decide (0 ≤ k') &&
             ((M.env i).lo.all fun lo => decide (lo ≤ c')) &&
             ((M.env i).hi.all fun hi => decide (c' ≤ hi))
         | CoordShape.chase j2 k2 =>
             -- cascade angle (EXT 4c): chases its resonant driver j2 (contract-to-0 at the
             -- same rate); the box is forward-invariant iff the driver's band sits inside
             -- k2 times the angle's band (`polyExp_le`, linear-dominance branch)
             !decide (j2 = m.gcoord) && !decide (j2 = sb.sc) &&
             decide (m.shapes j2 = CoordShape.contract k2 0) && decide (0 < k2) &&
             (match (M.env i).lo, (M.env i).hi, (M.env j2).lo, (M.env j2).hi with
              | some loi, some hii, some loj, some hij =>
                  decide (loi ≤ 0) && decide (0 ≤ hii) &&
                  decide (hij ≤ k2 * hii) && decide (k2 * loi ≤ loj)
              | _, _, _, _ => false)
         | _ => false)) &&
      m.succs.all (fun q' => decide (q' < M.modes.length)) &&
      (match sb.shi with
       | none => true
       | some sh =>
           m.succs.any fun q' =>
             match M.modes[q']?, sbands[q']? with
             | some m', some sb' =>
                 decide (sb'.sc = sb.sc) && decide (m'.gcoord = m.gcoord) &&
                 decide (m'.glo ≤ m.glo) && decide (m.ghi ≤ m'.ghi) &&
                 decide (sb'.slo ≤ sh) &&
                 (match sb'.shi with
                  | none => true
                  | some sh' => decide (sh + m.ghi * dt ≤ sh'))
             | _, _ => false)
  | _ => false

/-- **The terrain well-formedness checker.** Decidable; no Z3, no ODE reasoning. -/
def decideWellFormedT (T : TerrainModel n) : Bool :=
  decide (0 ≤ T.core.dtQ) &&
  ((List.finRange n).all fun i => bandOrdered (T.core.env i)) &&
  (List.range T.core.modes.length).all (fun q =>
    match T.core.modes[q]?, T.sbands[q]? with
    | some m, some sb => checkModeT T.core T.sbands m sb
    | _, _ => false)

/-! ## The witness flow: contract v, integrated s, decaying others -/

/-- Per-coordinate value of the terrain witness. -/
noncomputable def terrainVal (m : SettlingMode n) (sc : Fin n) (kR cR : ℝ)
    (base : State (Var n)) (t : ℝ) (i : Fin n) : ℝ :=
  if i = m.gcoord then cR + (base (Rv i) - cR) * Real.exp (-(kR * t))
  else if i = sc then base (Rv i) + cR * t + (base (Rv m.gcoord) - cR) * expInt kR t
  else match m.shapes i with
    | CoordShape.contract k' c' =>
        (c' : ℝ) + (base (Rv i) - (c' : ℝ)) * Real.exp (-((k' : ℝ) * t))
    | CoordShape.chase j2 k2 =>
        (base (Rv i) + base (Rv j2) * t) * Real.exp (-((k2 : ℝ) * t))
    | _ => base (Rv i)

/-- The terrain witness flow. -/
noncomputable def terrainΦ (m : SettlingMode n) (sc : Fin n) (kR cR : ℝ)
    (base : State (Var n)) (t : ℝ) : State (Var n) :=
  fun x => match x with
    | (Side.R, i) => terrainVal m sc kR cR base t i
    | _ => base x

@[simp] theorem terrainΦ_Rv (m : SettlingMode n) (sc : Fin n) (kR cR : ℝ)
    (base : State (Var n)) (t : ℝ) (i : Fin n) :
    terrainΦ m sc kR cR base t (Rv i) = terrainVal m sc kR cR base t i := rfl

theorem terrainΦ_nonR (m : SettlingMode n) (sc : Fin n) (kR cR : ℝ) (base : State (Var n))
    (t : ℝ) {x : Var n} (hx : ∀ i : Fin n, x ≠ Rv i) :
    terrainΦ m sc kR cR base t x = base x := by
  obtain ⟨sd, ix⟩ := x
  cases sd with
  | R => exact absurd rfl (hx ix)
  | L => rfl
  | Aux => rfl

theorem terrainVal_g {m : SettlingMode n} {sc : Fin n} {kR cR : ℝ} {base : State (Var n)}
    {t : ℝ} :
    terrainVal m sc kR cR base t m.gcoord
      = cR + (base (Rv m.gcoord) - cR) * Real.exp (-(kR * t)) := by
  simp [terrainVal]

theorem terrainVal_s {m : SettlingMode n} {sc : Fin n} {kR cR : ℝ} {base : State (Var n)}
    {t : ℝ} (hsc : sc ≠ m.gcoord) :
    terrainVal m sc kR cR base t sc
      = base (Rv sc) + cR * t + (base (Rv m.gcoord) - cR) * expInt kR t := by
  simp [terrainVal, hsc]

theorem terrainVal_contract {m : SettlingMode n} {sc : Fin n} {kR cR : ℝ}
    {base : State (Var n)} {t : ℝ} {i : Fin n} {k' c' : ℤ}
    (hig : i ≠ m.gcoord) (his : i ≠ sc) (hsh : m.shapes i = CoordShape.contract k' c') :
    terrainVal m sc kR cR base t i
      = (c' : ℝ) + (base (Rv i) - (c' : ℝ)) * Real.exp (-((k' : ℝ) * t)) := by
  simp [terrainVal, hig, his, hsh]

theorem terrainVal_frozen {m : SettlingMode n} {sc : Fin n} {kR cR : ℝ}
    {base : State (Var n)} {t : ℝ} {i : Fin n}
    (hig : i ≠ m.gcoord) (his : i ≠ sc) (hfz : m.shapes i = CoordShape.frozen) :
    terrainVal m sc kR cR base t i = base (Rv i) := by
  simp [terrainVal, hig, his, hfz]

theorem terrainVal_chase {m : SettlingMode n} {sc : Fin n} {kR cR : ℝ}
    {base : State (Var n)} {t : ℝ} {i j2 : Fin n} {k2 : ℤ}
    (hig : i ≠ m.gcoord) (his : i ≠ sc) (hsh : m.shapes i = CoordShape.chase j2 k2) :
    terrainVal m sc kR cR base t i
      = (base (Rv i) + base (Rv j2) * t) * Real.exp (-((k2 : ℝ) * t)) := by
  simp [terrainVal, hig, his, hsh]

/-- The cascade angle stays in its envelope box: both sides are `polyExp_le` on the
resonant value `(x₀ + x_j₀·t)e^{−k₂t}`, via the linear-dominance branch from the
driver-band-inside-`k₂`-times-angle-band conditions. -/
theorem chase_band {m : SettlingMode n} {sc : Fin n} {kR cR : ℝ} {base : State (Var n)}
    {i j2 : Fin n} {k2 : ℤ} (hig : i ≠ m.gcoord) (his : i ≠ sc)
    (hsh : m.shapes i = CoordShape.chase j2 k2) (hk2 : 0 < k2)
    {loi hii loj hij : ℤ}
    (hloi0 : loi ≤ 0) (hhii0 : 0 ≤ hii) (hijle : hij ≤ k2 * hii) (hlojge : k2 * loi ≤ loj)
    (hbl : (loi : ℝ) ≤ base (Rv i)) (hbh : base (Rv i) ≤ (hii : ℝ))
    (hbjl : (loj : ℝ) ≤ base (Rv j2)) (hbjh : base (Rv j2) ≤ (hij : ℝ))
    {t : ℝ} (ht : 0 ≤ t) :
    (loi : ℝ) ≤ terrainVal m sc kR cR base t i
    ∧ terrainVal m sc kR cR base t i ≤ (hii : ℝ) := by
  rw [terrainVal_chase hig his hsh]
  have hk2R : (0 : ℝ) < (k2 : ℝ) := by exact_mod_cast hk2
  have hloi0R : (loi : ℝ) ≤ 0 := by exact_mod_cast hloi0
  have hhii0R : (0 : ℝ) ≤ (hii : ℝ) := by exact_mod_cast hhii0
  have hijleR : (hij : ℝ) ≤ (k2 : ℝ) * (hii : ℝ) := by exact_mod_cast hijle
  have hlojgeR : (k2 : ℝ) * (loi : ℝ) ≤ (loj : ℝ) := by exact_mod_cast hlojge
  constructor
  · have hup := polyExp_le (-(base (Rv i))) (-(base (Rv j2))) (k2 : ℝ) (-(loi : ℝ)) t
      hk2R ht (by linarith) (by linarith) (Or.inl (by nlinarith))
    have hre : (-(base (Rv i)) + -(base (Rv j2)) * t) * Real.exp (-((k2 : ℝ) * t))
        = -((base (Rv i) + base (Rv j2) * t) * Real.exp (-((k2 : ℝ) * t))) := by ring
    rw [hre] at hup
    linarith
  · exact polyExp_le (base (Rv i)) (base (Rv j2)) (k2 : ℝ) (hii : ℝ) t hk2R ht hhii0R hbh
      (Or.inl (by nlinarith))


/-- The raw cascade value `(p + w·t)e^{−gt}` stays in `[lo, hi]` — the all-real core of
`chase_band`, reusable for the damper's pointwise bound. -/
theorem chase_val_band {p w g lo hi loj hij : ℝ} (hg : 0 < g) (hlo0 : lo ≤ 0)
    (hhi0 : 0 ≤ hi) (hijle : hij ≤ g * hi) (hlojge : g * lo ≤ loj)
    (hbl : lo ≤ p) (hbh : p ≤ hi) (hjl : loj ≤ w) (hjh : w ≤ hij)
    {t : ℝ} (ht : 0 ≤ t) :
    lo ≤ (p + w * t) * Real.exp (-(g * t)) ∧ (p + w * t) * Real.exp (-(g * t)) ≤ hi := by
  constructor
  · have hup := polyExp_le (-p) (-w) g (-lo) t hg ht (by linarith) (by linarith)
      (Or.inl (by nlinarith))
    have hre : (-p + -w * t) * Real.exp (-(g * t))
        = -((p + w * t) * Real.exp (-(g * t))) := by ring
    rw [hre] at hup
    linarith
  · exact polyExp_le p w g hi t hg ht hhi0 hbh (Or.inl (by nlinarith))

/-! ## EXT 3b — the damped integrator (`drivenDamp` position, the nonlinear-s' family)

`s' = v · (1 − Σ_d a_d·ψ_d²)` with each damper `ψ_d` contracting to 0: since `v` and every
`ψ_d` are explicit exponentials, `s` integrates in closed form into `expInt` terms — no ODE
existence machinery. The damping factor stays in `[0, 1]` (each `ψ_d(t)² ≤ ψ_d(0)² ≤ B_d²`
and the checker requires `a_d·B_d²·L ≤ 1` per damper, `L` the damper count), so the
integrand sits in `[0, v] ⊆ [0, c]` and the terrain segment-chain landing runs unchanged on
the same `[s₀, s₀ + c·dt]` image bound — proven here by monotonicity from the derivative
bounds rather than by algebra on the six-exponential closed form. -/

/-- The stored gain of a damper coordinate (its contract rate; 0 on a non-contract shape —
never hit under the checker's conditions). -/
noncomputable def dampGain (m : SettlingMode n) (d : Fin n × ℤ × ℤ) : ℝ :=
  match m.shapes d.1 with
  | CoordShape.contract kp _ => (kp : ℝ)
  | _ => 0

/-- The closed-form increment of the damped position:
`∫₀ᵗ v(u)·(1 − Σ_d a_d ψ_d(u)²) du`, all `expInt` terms. -/
noncomputable def dampVal (m : SettlingMode n) (kR cR : ℝ) (base : State (Var n))
    (dampers : List (Fin n × ℤ × ℤ)) (t : ℝ) : ℝ :=
  cR * t + (base (Rv m.gcoord) - cR) * expInt kR t
  - ((dampers.map (fun d =>
      ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1))^2 *
        (cR * expInt (2 * dampGain m d) t
          + (base (Rv m.gcoord) - cR) * expInt (kR + 2 * dampGain m d) t))).sum)

/-- Per-coordinate value of the damped terrain witness: the position takes `dampVal`,
everything else is the plain terrain witness. -/
noncomputable def terrainValD (m : SettlingMode n) (sc : Fin n) (kR cR : ℝ)
    (base : State (Var n)) (dampers : List (Fin n × ℤ × ℤ)) (t : ℝ) (i : Fin n) : ℝ :=
  if i = sc then base (Rv i) + dampVal m kR cR base dampers t
  else terrainVal m sc kR cR base t i

/-- The damped terrain witness flow. -/
noncomputable def terrainΦD (m : SettlingMode n) (sc : Fin n) (kR cR : ℝ)
    (base : State (Var n)) (dampers : List (Fin n × ℤ × ℤ)) (t : ℝ) : State (Var n) :=
  fun x => match x with
    | (Side.R, i) => terrainValD m sc kR cR base dampers t i
    | _ => base x

@[simp] theorem terrainΦD_Rv (m : SettlingMode n) (sc : Fin n) (kR cR : ℝ)
    (base : State (Var n)) (dampers : List (Fin n × ℤ × ℤ)) (t : ℝ) (i : Fin n) :
    terrainΦD m sc kR cR base dampers t (Rv i) = terrainValD m sc kR cR base dampers t i :=
  rfl

theorem terrainΦD_nonR (m : SettlingMode n) (sc : Fin n) (kR cR : ℝ)
    (base : State (Var n)) (dampers : List (Fin n × ℤ × ℤ)) (t : ℝ) {x : Var n}
    (hx : ∀ i : Fin n, x ≠ Rv i) : terrainΦD m sc kR cR base dampers t x = base x := by
  obtain ⟨sd, ix⟩ := x
  cases sd with
  | R => exact absurd rfl (hx ix)
  | L => rfl
  | Aux => rfl

theorem terrainValD_s {m : SettlingMode n} {sc : Fin n} {kR cR : ℝ} {base : State (Var n)}
    {dampers : List (Fin n × ℤ × ℤ)} {t : ℝ} :
    terrainValD m sc kR cR base dampers t sc
      = base (Rv sc) + dampVal m kR cR base dampers t := by
  simp [terrainValD]

theorem terrainValD_ne {m : SettlingMode n} {sc : Fin n} {kR cR : ℝ} {base : State (Var n)}
    {dampers : List (Fin n × ℤ × ℤ)} {t : ℝ} {i : Fin n} (his : i ≠ sc) :
    terrainValD m sc kR cR base dampers t i = terrainVal m sc kR cR base t i := by
  simp [terrainValD, his]

theorem terrainValD_g {m : SettlingMode n} {sc : Fin n} {kR cR : ℝ} {base : State (Var n)}
    {dampers : List (Fin n × ℤ × ℤ)} {t : ℝ} (hgs : sc ≠ m.gcoord) :
    terrainValD m sc kR cR base dampers t m.gcoord
      = cR + (base (Rv m.gcoord) - cR) * Real.exp (-(kR * t)) := by
  rw [terrainValD_ne (fun h => hgs h.symm), terrainVal_g]

theorem terrainValD_contract {m : SettlingMode n} {sc : Fin n} {kR cR : ℝ}
    {base : State (Var n)} {dampers : List (Fin n × ℤ × ℤ)} {t : ℝ} {i : Fin n} {k' c' : ℤ}
    (hig : i ≠ m.gcoord) (his : i ≠ sc) (hsh : m.shapes i = CoordShape.contract k' c') :
    terrainValD m sc kR cR base dampers t i
      = (c' : ℝ) + (base (Rv i) - (c' : ℝ)) * Real.exp (-((k' : ℝ) * t)) := by
  rw [terrainValD_ne his, terrainVal_contract hig his hsh]

theorem terrainValD_frozen {m : SettlingMode n} {sc : Fin n} {kR cR : ℝ}
    {base : State (Var n)} {dampers : List (Fin n × ℤ × ℤ)} {t : ℝ} {i : Fin n}
    (hig : i ≠ m.gcoord) (his : i ≠ sc) (hfz : m.shapes i = CoordShape.frozen) :
    terrainValD m sc kR cR base dampers t i = base (Rv i) := by
  rw [terrainValD_ne his, terrainVal_frozen hig his hfz]

theorem terrainValD_chase {m : SettlingMode n} {sc : Fin n} {kR cR : ℝ}
    {base : State (Var n)} {dampers : List (Fin n × ℤ × ℤ)} {t : ℝ} {i j2 : Fin n} {k2 : ℤ}
    (hig : i ≠ m.gcoord) (his : i ≠ sc) (hsh : m.shapes i = CoordShape.chase j2 k2) :
    terrainValD m sc kR cR base dampers t i
      = (base (Rv i) + base (Rv j2) * t) * Real.exp (-((k2 : ℝ) * t)) := by
  rw [terrainValD_ne his, terrainVal_chase hig his hsh]

/-! ## EXT 4c dampers — the cascade-damped integrator

Same geometry as EXT 3b, but each damper is a `chase` coordinate: `ψ_d(u) =
(p_d + w_d·u)e^{−g_d·u}` with `p_d` the damper base, `w_d` its driver's base, `g_d` its
chase rate. The square expands into `uⁱe^{−2gu}` / `uⁱe^{−(k+2g)u}` terms
(`polyExpInt₁/₂`), the damping factor stays in `[0, 1]` by the pointwise band
`|ψ_d(u)| ≤ B_d` (`chase_val_band`) and the same per-damper budget, and the position
runs the unchanged monotonicity argument. -/

/-- A cascade damper's chase rate (from its shape; 0 on non-chase — never hit). -/
noncomputable def chaseGain (m : SettlingMode n) (d : Fin n × ℤ × ℤ) : ℝ :=
  match m.shapes d.1 with
  | CoordShape.chase _ kp => (kp : ℝ)
  | _ => 0

/-- A cascade damper's driver value at the base state (0 on non-chase — never hit). -/
noncomputable def chaseDrv (m : SettlingMode n) (base : State (Var n))
    (d : Fin n × ℤ × ℤ) : ℝ :=
  match m.shapes d.1 with
  | CoordShape.chase j _ => base (Rv j)
  | _ => 0

/-- The closed-form increment of the cascade-damped position:
`∫₀ᵗ v(u)·(1 − Σ_d a_d ψ_d(u)²) du` with `ψ_d(u) = (p_d + w_d·u)e^{−g_d·u}`. -/
noncomputable def dampValC (m : SettlingMode n) (kR cR : ℝ) (base : State (Var n))
    (dampers : List (Fin n × ℤ × ℤ)) (t : ℝ) : ℝ :=
  cR * t + (base (Rv m.gcoord) - cR) * expInt kR t
  - ((dampers.map (fun d =>
      ((d.2.1 : ℝ) / (d.2.2 : ℝ)) *
        (cR * ((base (Rv d.1)) ^ 2 * expInt (2 * chaseGain m d) t
            + 2 * base (Rv d.1) * chaseDrv m base d * polyExpInt₁ (2 * chaseGain m d) t
            + (chaseDrv m base d) ^ 2 * polyExpInt₂ (2 * chaseGain m d) t)
         + (base (Rv m.gcoord) - cR) *
            ((base (Rv d.1)) ^ 2 * expInt (kR + 2 * chaseGain m d) t
            + 2 * base (Rv d.1) * chaseDrv m base d * polyExpInt₁ (kR + 2 * chaseGain m d) t
            + (chaseDrv m base d) ^ 2 * polyExpInt₂ (kR + 2 * chaseGain m d) t)))).sum)

/-- Per-coordinate value of the cascade-damped terrain witness. -/
noncomputable def terrainValDC (m : SettlingMode n) (sc : Fin n) (kR cR : ℝ)
    (base : State (Var n)) (dampers : List (Fin n × ℤ × ℤ)) (t : ℝ) (i : Fin n) : ℝ :=
  if i = sc then base (Rv i) + dampValC m kR cR base dampers t
  else terrainVal m sc kR cR base t i

/-- The cascade-damped terrain witness flow. -/
noncomputable def terrainΦDC (m : SettlingMode n) (sc : Fin n) (kR cR : ℝ)
    (base : State (Var n)) (dampers : List (Fin n × ℤ × ℤ)) (t : ℝ) : State (Var n) :=
  fun x => match x with
    | (Side.R, i) => terrainValDC m sc kR cR base dampers t i
    | _ => base x

@[simp] theorem terrainΦDC_Rv (m : SettlingMode n) (sc : Fin n) (kR cR : ℝ)
    (base : State (Var n)) (dampers : List (Fin n × ℤ × ℤ)) (t : ℝ) (i : Fin n) :
    terrainΦDC m sc kR cR base dampers t (Rv i)
      = terrainValDC m sc kR cR base dampers t i := rfl

theorem terrainΦDC_nonR (m : SettlingMode n) (sc : Fin n) (kR cR : ℝ)
    (base : State (Var n)) (dampers : List (Fin n × ℤ × ℤ)) (t : ℝ) {x : Var n}
    (hx : ∀ i : Fin n, x ≠ Rv i) : terrainΦDC m sc kR cR base dampers t x = base x := by
  obtain ⟨sd, ix⟩ := x
  cases sd with
  | R => exact absurd rfl (hx ix)
  | L => rfl
  | Aux => rfl

theorem terrainValDC_s {m : SettlingMode n} {sc : Fin n} {kR cR : ℝ} {base : State (Var n)}
    {dampers : List (Fin n × ℤ × ℤ)} {t : ℝ} :
    terrainValDC m sc kR cR base dampers t sc
      = base (Rv sc) + dampValC m kR cR base dampers t := by
  simp [terrainValDC]

theorem terrainValDC_ne {m : SettlingMode n} {sc : Fin n} {kR cR : ℝ}
    {base : State (Var n)} {dampers : List (Fin n × ℤ × ℤ)} {t : ℝ} {i : Fin n}
    (his : i ≠ sc) :
    terrainValDC m sc kR cR base dampers t i = terrainVal m sc kR cR base t i := by
  simp [terrainValDC, his]

theorem terrainValDC_g {m : SettlingMode n} {sc : Fin n} {kR cR : ℝ} {base : State (Var n)}
    {dampers : List (Fin n × ℤ × ℤ)} {t : ℝ} (hgs : sc ≠ m.gcoord) :
    terrainValDC m sc kR cR base dampers t m.gcoord
      = cR + (base (Rv m.gcoord) - cR) * Real.exp (-(kR * t)) := by
  rw [terrainValDC_ne (fun h => hgs h.symm), terrainVal_g]

theorem terrainValDC_contract {m : SettlingMode n} {sc : Fin n} {kR cR : ℝ}
    {base : State (Var n)} {dampers : List (Fin n × ℤ × ℤ)} {t : ℝ} {i : Fin n} {k' c' : ℤ}
    (hig : i ≠ m.gcoord) (his : i ≠ sc) (hsh : m.shapes i = CoordShape.contract k' c') :
    terrainValDC m sc kR cR base dampers t i
      = (c' : ℝ) + (base (Rv i) - (c' : ℝ)) * Real.exp (-((k' : ℝ) * t)) := by
  rw [terrainValDC_ne his, terrainVal_contract hig his hsh]

theorem terrainValDC_frozen {m : SettlingMode n} {sc : Fin n} {kR cR : ℝ}
    {base : State (Var n)} {dampers : List (Fin n × ℤ × ℤ)} {t : ℝ} {i : Fin n}
    (hig : i ≠ m.gcoord) (his : i ≠ sc) (hfz : m.shapes i = CoordShape.frozen) :
    terrainValDC m sc kR cR base dampers t i = base (Rv i) := by
  rw [terrainValDC_ne his, terrainVal_frozen hig his hfz]

theorem terrainValDC_chase {m : SettlingMode n} {sc : Fin n} {kR cR : ℝ}
    {base : State (Var n)} {dampers : List (Fin n × ℤ × ℤ)} {t : ℝ} {i j2 : Fin n} {k2 : ℤ}
    (hig : i ≠ m.gcoord) (his : i ≠ sc) (hsh : m.shapes i = CoordShape.chase j2 k2) :
    terrainValDC m sc kR cR base dampers t i
      = (base (Rv i) + base (Rv j2) * t) * Real.exp (-((k2 : ℝ) * t)) := by
  rw [terrainValDC_ne his, terrainVal_chase hig his hsh]

/-- Derivative of a list-indexed sum of real functions. -/
theorem hasDerivAt_list_sum {α : Type} (l : List α) (f : α → ℝ → ℝ) (f' : α → ℝ) (t : ℝ)
    (h : ∀ a ∈ l, HasDerivAt (f a) (f' a) t) :
    HasDerivAt (fun u => (l.map (fun a => f a u)).sum) ((l.map f').sum) t := by
  induction l with
  | nil => simpa using hasDerivAt_const t (0 : ℝ)
  | cons a tl ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (h a (List.mem_cons_self ..)).add
        (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

/-- Eval of the damping foldr term. -/
theorem eval_dampFold (dampers : List (Fin n × ℤ × ℤ)) (μ : State (Var n)) :
    Term.eval (dampers.foldr (fun d acc =>
        Term.binop AOp.sub acc
          (Term.binop AOp.mul (Term.const ((d.2.1 : ℝ) / (d.2.2 : ℝ)))
            (Term.binop AOp.mul (Term.var (Rv d.1)) (Term.var (Rv d.1)))))
      (Term.const 1)) μ
    = 1 - ((dampers.map (fun d =>
        ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (μ (Rv d.1))^2)).sum) := by
  induction dampers with
  | nil => simp [Term.eval]
  | cons d tl ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons, Term.eval, AOp.interp]
      rw [ih]
      ring

/-- The eval of the `drivenDamp` field term is the damped product. -/
theorem eval_drivenDamp_field {m : SettlingMode n} {i j : Fin n}
    {dampers : List (Fin n × ℤ × ℤ)}
    (hsh : m.shapes i = CoordShape.drivenDamp j dampers) (μ : State (Var n)) :
    Term.eval (m.fieldOf i) μ
      = μ (Rv j) * (1 - ((dampers.map (fun d =>
          ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (μ (Rv d.1))^2)).sum)) := by
  unfold SettlingMode.fieldOf
  rw [hsh]
  show Term.eval (Term.binop AOp.mul (Term.var (Rv j)) _) μ = _
  simp only [Term.eval, AOp.interp]
  rw [eval_dampFold]

/-! ## The per-mode discharge -/

/-- TERRAIN mode: contract `v` (cap at the equilibrium), integrated `s` over the terrain
segment, decaying/frozen others — stays, and lands in the own box or the declared successor
segment, by an endpoint case-split at `shi`. -/
theorem settling_terrain (T : TerrainModel n) {q : ℕ} {m : SettlingMode n} {sb : SBand n}
    (hq : T.core.modes[q]? = some m) (hsb : T.sbands[q]? = some sb) {k c : ℤ}
    (hsh : m.shapes m.gcoord = CoordShape.contract k c)
    (hk : 0 ≤ k) (hcl : m.glo ≤ c) (hch : c ≤ m.ghi) (hglo0 : 0 ≤ m.glo)
    (hvLo : ∀ l', (T.core.env m.gcoord).lo = some l' → l' ≤ m.glo)
    (hvHi : ∀ h', (T.core.env m.gcoord).hi = some h' → m.ghi ≤ h')
    (hsc : sb.sc ≠ m.gcoord)
    (hscd : m.shapes sb.sc = CoordShape.driven m.gcoord)
    (hsloIn : ∀ l', (T.core.env sb.sc).lo = some l' → l' ≤ sb.slo)
    (hsHiNone : (T.core.env sb.sc).hi = none)
    (hOth : ∀ i, i ≠ m.gcoord → i ≠ sb.sc →
        m.shapes i = CoordShape.frozen ∨
        (∃ k' c', m.shapes i = CoordShape.contract k' c' ∧ 0 ≤ k' ∧
          (∀ l', (T.core.env i).lo = some l' → l' ≤ c') ∧
          (∀ h', (T.core.env i).hi = some h' → c' ≤ h')) ∨
        (∃ j2 k2 loi hii loj hij, m.shapes i = CoordShape.chase j2 k2 ∧
          j2 ≠ m.gcoord ∧ j2 ≠ sb.sc ∧ m.shapes j2 = CoordShape.contract k2 0 ∧ 0 < k2 ∧
          (T.core.env i).lo = some loi ∧ (T.core.env i).hi = some hii ∧
          (T.core.env j2).lo = some loj ∧ (T.core.env j2).hi = some hij ∧
          loi ≤ 0 ∧ 0 ≤ hii ∧ hij ≤ k2 * hii ∧ k2 * loi ≤ loj))
    (hland : ∀ sh, sb.shi = some sh →
        ∃ q' ∈ m.succs, ∃ m' sb', T.core.modes[q']? = some m' ∧ T.sbands[q']? = some sb' ∧
          sb'.sc = sb.sc ∧ m'.gcoord = m.gcoord ∧ m'.glo ≤ m.glo ∧ m.ghi ≤ m'.ghi ∧
          sb'.slo ≤ sh ∧ (∀ sh', sb'.shi = some sh' → sh + m.ghi * T.core.dt ≤ sh'))
    (hdt : (0 : ℝ) ≤ (T.core.dt : ℝ)) :
    GuardSettlingB T.core.graph T.GdOf m.fieldOf (Term.const 1) T.core.envF
      ((T.core.dt : ℝ)) q := by
  intro base hb
  obtain ⟨⟨henv, hblo, hbhi⟩, hbslo, hbshi⟩ := (sat_GdOfT hq hsb).mp hb
  have hkR0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hglo0R : (0 : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hglo0
  have hclR : (m.glo : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcl
  have hchR : (c : ℝ) ≤ (m.ghi : ℝ) := by exact_mod_cast hch
  have hbv0 : (0 : ℝ) ≤ base (Rv m.gcoord) := le_trans hglo0R hblo
  -- the active value stays in the guard band: the hull of v₀ and c sits inside [glo, ghi]
  have hbandV : ∀ t, 0 ≤ t →
      (m.glo : ℝ) ≤ terrainVal m sb.sc (k : ℝ) (c : ℝ) base t m.gcoord
      ∧ terrainVal m sb.sc (k : ℝ) (c : ℝ) base t m.gcoord ≤ (m.ghi : ℝ) := by
    intro t ht
    have hθpos : 0 < Real.exp (-((k : ℝ) * t)) := Real.exp_pos _
    have hθle : Real.exp (-((k : ℝ) * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    rw [terrainVal_g]
    rcases le_total (base (Rv m.gcoord)) (c : ℝ) with hbc | hbc
    · constructor
      · nlinarith
      · nlinarith
    · constructor
      · nlinarith
      · nlinarith
  -- the position's band: [s₀, s₀ + ghi·t] for all t ≥ 0 (the guard band caps the rate)
  have hbandS : ∀ t, 0 ≤ t →
      base (Rv sb.sc) ≤ terrainVal m sb.sc (k : ℝ) (c : ℝ) base t sb.sc
      ∧ terrainVal m sb.sc (k : ℝ) (c : ℝ) base t sb.sc
          ≤ base (Rv sb.sc) + (m.ghi : ℝ) * t := by
    intro t ht
    have hEI0 : 0 ≤ expInt (k : ℝ) t := expInt_nonneg hkR0 ht
    have hEIt : expInt (k : ℝ) t ≤ t := expInt_le hkR0 ht
    rw [terrainVal_s hsc]
    rcases le_total (base (Rv m.gcoord)) (c : ℝ) with hbc | hbc
    · constructor
      · nlinarith
      · nlinarith
    · constructor
      · nlinarith
      · nlinarith
  -- a contract other stays in the hull of its base and its equilibrium
  have hbandO : ∀ (i : Fin n) (k' c' : ℤ), i ≠ m.gcoord → i ≠ sb.sc → 0 ≤ k' →
      m.shapes i = CoordShape.contract k' c' → ∀ t, 0 ≤ t →
      min (base (Rv i)) (c' : ℝ) ≤ terrainVal m sb.sc (k : ℝ) (c : ℝ) base t i
      ∧ terrainVal m sb.sc (k : ℝ) (c : ℝ) base t i ≤ max (base (Rv i)) (c' : ℝ) := by
    intro i k' c' hig his hk' hshi t ht
    have hk'R : (0 : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hk'
    have hθpos : 0 < Real.exp (-((k' : ℝ) * t)) := Real.exp_pos _
    have hθle : Real.exp (-((k' : ℝ) * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    rw [terrainVal_contract hig his hshi]
    rcases le_total (base (Rv i)) (c' : ℝ) with hbc' | hbc'
    · rw [min_eq_left hbc', max_eq_right hbc']
      constructor
      · nlinarith
      · nlinarith
    · rw [min_eq_right hbc', max_eq_left hbc']
      constructor
      · nlinarith
      · nlinarith
  -- staying in the envelope
  have hstayEnv : ∀ t, 0 ≤ t →
      Formula.sat T.core.envF (terrainΦ m sb.sc (k : ℝ) (c : ℝ) base t) := by
    intro t ht
    rw [sat_envF]
    intro i
    rw [terrainΦ_Rv]
    by_cases hig : i = m.gcoord
    · rw [hig]
      obtain ⟨h1, h2⟩ := hbandV t ht
      have hbe := (sat_envF.mp henv) m.gcoord
      unfold Band.memR at hbe ⊢
      rcases hbe with ⟨hbl, hbh⟩
      constructor
      · cases hcase : (T.core.env m.gcoord).lo with
        | none => trivial
        | some l =>
            have hlG : (l : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hvLo l hcase
            linarith
      · cases hcase : (T.core.env m.gcoord).hi with
        | none => trivial
        | some h =>
            have hgh : (m.ghi : ℝ) ≤ (h : ℝ) := by exact_mod_cast hvHi h hcase
            linarith
    · by_cases his : i = sb.sc
      · rw [his]
        obtain ⟨h1, h2⟩ := hbandS t ht
        unfold Band.memR
        constructor
        · cases hcase : (T.core.env sb.sc).lo with
          | none => trivial
          | some l =>
              have hlG : (l : ℝ) ≤ (sb.slo : ℝ) := by exact_mod_cast hsloIn l hcase
              linarith
        · rw [hsHiNone]; trivial
      · rcases hOth i hig his with hfz | ⟨k', c', hshi, hk', hloO, hhiO⟩ | hchase
        · rw [terrainVal_frozen hig his hfz]
          exact (sat_envF.mp henv) i
        · obtain ⟨h1, h2⟩ := hbandO i k' c' hig his hk' hshi t ht
          have hbe := (sat_envF.mp henv) i
          unfold Band.memR at hbe ⊢
          rcases hbe with ⟨hbl, hbh⟩
          constructor
          · cases hcase : (T.core.env i).lo with
            | none => trivial
            | some l =>
                rw [hcase] at hbl
                have hlc : (l : ℝ) ≤ (c' : ℝ) := by exact_mod_cast hloO l hcase
                have hmin : (l : ℝ) ≤ min (base (Rv i)) (c' : ℝ) := le_min hbl hlc
                linarith
          · cases hcase : (T.core.env i).hi with
            | none => trivial
            | some h =>
                rw [hcase] at hbh
                have hhc : (c' : ℝ) ≤ (h : ℝ) := by exact_mod_cast hhiO h hcase
                have hmax : max (base (Rv i)) (c' : ℝ) ≤ (h : ℝ) := max_le hbh hhc
                linarith
        · obtain ⟨j2, k2, loi, hii, loj, hij, hshi, hj2g, hj2s, hj2c, hk2, hloi, hhii,
            hloj, hhij, hloi0, hhii0, hijle, hlojge⟩ := hchase
          have hbi := (sat_envF.mp henv) i
          have hbj := (sat_envF.mp henv) j2
          unfold Band.memR at hbi hbj ⊢
          rw [hloi, hhii] at hbi ⊢
          rw [hloj, hhij] at hbj
          obtain ⟨hbl, hbh⟩ := hbi
          obtain ⟨hbjl, hbjh⟩ := hbj
          exact chase_band hig his hshi hk2 hloi0 hhii0 hijle hlojge hbl hbh hbjl hbjh ht
  -- landing: the own box below `shi`, the declared successor above
  have hpick : ∃ q2 ∈ q :: T.core.graph.retainedSucc q,
      Formula.sat (T.GdOf q2) (terrainΦ m sb.sc (k : ℝ) (c : ℝ) base (T.core.dt : ℝ)) := by
    obtain ⟨hv1, hv2⟩ := hbandV (T.core.dt : ℝ) hdt
    obtain ⟨hs1, hs2⟩ := hbandS (T.core.dt : ℝ) hdt
    have hself_v : (m.glo : ℝ) ≤ terrainVal m sb.sc (k : ℝ) (c : ℝ) base (T.core.dt : ℝ)
        m.gcoord ∧ terrainVal m sb.sc (k : ℝ) (c : ℝ) base (T.core.dt : ℝ) m.gcoord
          ≤ (m.ghi : ℝ) := ⟨hv1, hv2⟩
    cases hshi : sb.shi with
    | none =>
        refine ⟨q, List.mem_cons_self .., ?_⟩
        rw [sat_GdOfT hq hsb]
        refine ⟨⟨hstayEnv _ hdt, by rw [terrainΦ_Rv]; exact hself_v.1,
          by rw [terrainΦ_Rv]; exact hself_v.2⟩,
          by rw [terrainΦ_Rv]; linarith, ?_⟩
        intro sh' hsh'
        rw [hshi] at hsh'
        exact absurd hsh' (by simp)
    | some sh =>
        obtain ⟨q', hq'mem, m', sb', hm', hsb', hsc', hgc', hglo', hghi', hslo', hshi'⟩ :=
          hland sh hshi
        have hbs_sh : base (Rv sb.sc) ≤ (sh : ℝ) := hbshi sh hshi
        rcases le_or_gt (terrainVal m sb.sc (k : ℝ) (c : ℝ) base (T.core.dt : ℝ) sb.sc)
          ((sh : ℝ)) with he | he
        · -- self
          refine ⟨q, List.mem_cons_self .., ?_⟩
          rw [sat_GdOfT hq hsb]
          refine ⟨⟨hstayEnv _ hdt, by rw [terrainΦ_Rv]; exact hself_v.1,
            by rw [terrainΦ_Rv]; exact hself_v.2⟩,
            by rw [terrainΦ_Rv]; linarith, ?_⟩
          intro sh' hsh'
          rw [hshi] at hsh'
          cases hsh'
          rw [terrainΦ_Rv]
          exact he
        · -- successor
          have hglo'R : (m'.glo : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hglo'
          have hghi'R : (m.ghi : ℝ) ≤ (m'.ghi : ℝ) := by exact_mod_cast hghi'
          have hslo'R : (sb'.slo : ℝ) ≤ (sh : ℝ) := by exact_mod_cast hslo'
          refine ⟨q', List.mem_cons_of_mem _ (succ_mem_retained T.core hq hq'mem), ?_⟩
          rw [sat_GdOfT hm' hsb']
          refine ⟨⟨hstayEnv _ hdt, ?_, ?_⟩, ?_, ?_⟩
          · rw [hgc', terrainΦ_Rv]; linarith
          · rw [hgc', terrainΦ_Rv]; linarith
          · rw [hsc', terrainΦ_Rv]; linarith
          · intro sh' hsh'
            have hcov : (sh : ℝ) + (m.ghi : ℝ) * (T.core.dt : ℝ) ≤ (sh' : ℝ) := by
              exact_mod_cast hshi' sh' hsh'
            rw [hsc', terrainΦ_Rv]
            linarith
  obtain ⟨q2, hq2ret, hq2sat⟩ := hpick
  refine ⟨terrainΦ m sb.sc (k : ℝ) (c : ℝ) base, ?_, ?_, ?_,
    fun t ht => hstayEnv t ht.1, q2, hq2ret, hq2sat⟩
  · -- t = 0 recovers the base
    funext x
    obtain ⟨sd, ix⟩ := x
    cases sd with
    | R =>
        show terrainVal m sb.sc (k : ℝ) (c : ℝ) base 0 ix = base (Rv ix)
        unfold terrainVal
        by_cases hig : ix = m.gcoord
        · rw [if_pos hig]; subst hig; simp
        · rw [if_neg hig]
          by_cases his : ix = sb.sc
          · rw [if_pos his]; subst his; simp [expInt]
          · rw [if_neg his]
            rcases hshx : m.shapes ix with _ | _ | _ | _ | _ <;> simp
    | L => rfl
    | Aux => rfl
  · -- derivatives
    intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hig : i = m.gcoord
    · rw [hig]
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf m.gcoord))
          (terrainΦ m sb.sc (k : ℝ) (c : ℝ) base t)
          = (k : ℝ) * ((c : ℝ) - terrainVal m sb.sc (k : ℝ) (c : ℝ) base t m.gcoord) := by
        simp [SettlingMode.fieldOf, hsh, CoordShape.field, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => terrainΦ m sb.sc (k : ℝ) (c : ℝ) base u (Rv m.gcoord))
          = fun u => (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)) := by
        funext u; rw [terrainΦ_Rv, terrainVal_g]
      rw [hcurve]
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
          = (k : ℝ) * ((c : ℝ) - terrainVal m sb.sc (k : ℝ) (c : ℝ) base t m.gcoord) := by
        rw [terrainVal_g]; ring
      rw [← heq]
      exact h1.hasDerivWithinAt
    · by_cases his : i = sb.sc
      · rw [his]
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf sb.sc))
            (terrainΦ m sb.sc (k : ℝ) (c : ℝ) base t)
            = (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * t)) := by
          simp [SettlingMode.fieldOf, hscd, CoordShape.field, Term.eval, AOp.interp,
            terrainΦ_Rv, terrainVal_g]
        rw [heval]
        have hcurve : (fun u => terrainΦ m sb.sc (k : ℝ) (c : ℝ) base u (Rv sb.sc))
            = fun u => base (Rv sb.sc) + (c : ℝ) * u
                + (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) u := by
          funext u; rw [terrainΦ_Rv, terrainVal_s hsc]
        rw [hcurve]
        have h1 : HasDerivAt (fun u : ℝ => base (Rv sb.sc) + (c : ℝ) * u) (c : ℝ) t := by
          have h := ((hasDerivAt_id t).const_mul (c : ℝ)).const_add (base (Rv sb.sc))
          simpa using h
        have h2 : HasDerivAt
            (fun u : ℝ => (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) u)
            ((base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * t))) t :=
          (expInt_hasDeriv (k : ℝ) t).const_mul (base (Rv m.gcoord) - (c : ℝ))
        have h := h1.add h2
        exact h.hasDerivWithinAt
      · rcases hOth i hig his with hfz | ⟨k', c', hshi, -, -, -⟩ | hchase
        · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
              (terrainΦ m sb.sc (k : ℝ) (c : ℝ) base t) = 0 := by
            simp [SettlingMode.fieldOf, hfz, CoordShape.field, Term.eval, AOp.interp]
          rw [heval]
          have hcurve : (fun u => terrainΦ m sb.sc (k : ℝ) (c : ℝ) base u (Rv i))
              = fun _ => base (Rv i) := by
            funext u; rw [terrainΦ_Rv, terrainVal_frozen hig his hfz]
          rw [hcurve]
          exact hasDerivWithinAt_const t _ _
        · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
              (terrainΦ m sb.sc (k : ℝ) (c : ℝ) base t)
              = (k' : ℝ) * ((c' : ℝ) - terrainVal m sb.sc (k : ℝ) (c : ℝ) base t i) := by
            simp [SettlingMode.fieldOf, hshi, CoordShape.field, Term.eval, AOp.interp]
          rw [heval]
          have hcurve : (fun u => terrainΦ m sb.sc (k : ℝ) (c : ℝ) base u (Rv i))
              = fun u => (c' : ℝ) + (base (Rv i) - (c' : ℝ)) * Real.exp (-((k' : ℝ) * u)) := by
            funext u; rw [terrainΦ_Rv, terrainVal_contract hig his hshi]
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
              = (k' : ℝ) * ((c' : ℝ) - terrainVal m sb.sc (k : ℝ) (c : ℝ) base t i) := by
            rw [terrainVal_contract hig his hshi]; ring
          rw [← heq]
          exact h1.hasDerivWithinAt
        · obtain ⟨j2, k2, loi, hii, loj, hij, hshi, hj2g, hj2s, hj2c, hk2, -, -, -, -,
            -, -, -, -⟩ := hchase
          have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
              (terrainΦ m sb.sc (k : ℝ) (c : ℝ) base t)
              = terrainVal m sb.sc (k : ℝ) (c : ℝ) base t j2
                - (k2 : ℝ) * terrainVal m sb.sc (k : ℝ) (c : ℝ) base t i := by
            simp [SettlingMode.fieldOf, hshi, CoordShape.field, Term.eval, AOp.interp]
          rw [heval]
          have hcurve : (fun u => terrainΦ m sb.sc (k : ℝ) (c : ℝ) base u (Rv i))
              = fun u => (base (Rv i) + base (Rv j2) * u) * Real.exp (-((k2 : ℝ) * u)) := by
            funext u; rw [terrainΦ_Rv, terrainVal_chase hig his hshi]
          rw [hcurve]
          have hlin : HasDerivAt (fun u : ℝ => base (Rv i) + base (Rv j2) * u)
              (base (Rv j2)) t := by
            simpa using ((hasDerivAt_id t).const_mul (base (Rv j2))).const_add (base (Rv i))
          have hexp : HasDerivAt (fun u : ℝ => Real.exp (-((k2 : ℝ) * u)))
              (-(k2 : ℝ) * Real.exp (-((k2 : ℝ) * t))) t := by
            have hinner : HasDerivAt (fun u : ℝ => -((k2 : ℝ) * u)) (-(k2 : ℝ)) t := by
              have h := (hasDerivAt_id t).const_mul (-(k2 : ℝ))
              simp only [id, mul_one, neg_mul] at h
              exact h
            have h := (Real.hasDerivAt_exp (-((k2 : ℝ) * t))).comp t hinner
            simp only [Function.comp_def] at h
            rw [mul_comm (Real.exp (-((k2 : ℝ) * t))) (-(k2 : ℝ))] at h
            exact h
          have h1 := hlin.mul hexp
          have heq : base (Rv j2) * Real.exp (-((k2 : ℝ) * t))
              + (base (Rv i) + base (Rv j2) * t) * (-(k2 : ℝ) * Real.exp (-((k2 : ℝ) * t)))
              = terrainVal m sb.sc (k : ℝ) (c : ℝ) base t j2
                - (k2 : ℝ) * terrainVal m sb.sc (k : ℝ) (c : ℝ) base t i := by
            rw [terrainVal_chase hig his hshi, terrainVal_contract hj2g hj2s hj2c]
            push_cast
            ring
          rw [← heq]
          exact h1.hasDerivWithinAt
  · -- mask
    intro t ht x hx
    refine terrainΦ_nonR m sb.sc (k : ℝ) (c : ℝ) base t ?_
    intro i hxi
    exact hx (by
      rw [hxi]
      simp only [rightBlock, ODESystem.bound, List.map_map]
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

/-- Distributing `v(u)` over the damping sum (per-term `e^{−ku}·e^{−2gu} = e^{−(k+2g)u}`). -/
theorem dampProd_sum {α : Type} (kR A cR u : ℝ) (l : List α) (w g : α → ℝ) :
    (l.map (fun d => w d * (cR * Real.exp (-(2 * g d * u))
        + A * Real.exp (-((kR + 2 * g d) * u))))).sum
    = (l.map (fun d => w d * Real.exp (-(2 * g d * u)))).sum
        * (cR + A * Real.exp (-(kR * u))) := by
  induction l with
  | nil => simp
  | cons d tl ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      have hexp : Real.exp (-((kR + 2 * g d) * u))
          = Real.exp (-(2 * g d * u)) * Real.exp (-(kR * u)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring

/-- TERRAIN mode: contract `v` (cap at the equilibrium), integrated `s` over the terrain
segment, decaying/frozen others — stays, and lands in the own box or the declared successor
segment, by an endpoint case-split at `shi`. -/
theorem settling_terrain_damp (T : TerrainModel n) {q : ℕ} {m : SettlingMode n} {sb : SBand n}
    (hq : T.core.modes[q]? = some m) (hsb : T.sbands[q]? = some sb) {k c : ℤ}
    (hsh : m.shapes m.gcoord = CoordShape.contract k c)
    (hk : 0 ≤ k) (hcl : m.glo ≤ c) (hch : c ≤ m.ghi) (hglo0 : 0 ≤ m.glo)
    (hvLo : ∀ l', (T.core.env m.gcoord).lo = some l' → l' ≤ m.glo)
    (hvHi : ∀ h', (T.core.env m.gcoord).hi = some h' → m.ghi ≤ h')
    (hsc : sb.sc ≠ m.gcoord)
    {dampers : List (Fin n × ℤ × ℤ)}
    (hscd : m.shapes sb.sc = CoordShape.drivenDamp m.gcoord dampers)
    (hdamp : ∀ d ∈ dampers, d.1 ≠ m.gcoord ∧ d.1 ≠ sb.sc ∧ 0 ≤ d.2.1 ∧ 0 < d.2.2 ∧
        (∃ kp, m.shapes d.1 = CoordShape.contract kp 0 ∧ 0 ≤ kp) ∧
        (∃ lo hi, (T.core.env d.1).lo = some lo ∧ (T.core.env d.1).hi = some hi ∧
          lo ≤ 0 ∧ 0 ≤ hi ∧
          d.2.1 * (max (-lo) hi)^2 * (dampers.length : ℤ) ≤ d.2.2))
    (hsloIn : ∀ l', (T.core.env sb.sc).lo = some l' → l' ≤ sb.slo)
    (hsHiNone : (T.core.env sb.sc).hi = none)
    (hOth : ∀ i, i ≠ m.gcoord → i ≠ sb.sc →
        m.shapes i = CoordShape.frozen ∨
        (∃ k' c', m.shapes i = CoordShape.contract k' c' ∧ 0 ≤ k' ∧
          (∀ l', (T.core.env i).lo = some l' → l' ≤ c') ∧
          (∀ h', (T.core.env i).hi = some h' → c' ≤ h')) ∨
        (∃ j2 k2 loi hii loj hij, m.shapes i = CoordShape.chase j2 k2 ∧
          j2 ≠ m.gcoord ∧ j2 ≠ sb.sc ∧ m.shapes j2 = CoordShape.contract k2 0 ∧ 0 < k2 ∧
          (T.core.env i).lo = some loi ∧ (T.core.env i).hi = some hii ∧
          (T.core.env j2).lo = some loj ∧ (T.core.env j2).hi = some hij ∧
          loi ≤ 0 ∧ 0 ≤ hii ∧ hij ≤ k2 * hii ∧ k2 * loi ≤ loj))
    (hland : ∀ sh, sb.shi = some sh →
        ∃ q' ∈ m.succs, ∃ m' sb', T.core.modes[q']? = some m' ∧ T.sbands[q']? = some sb' ∧
          sb'.sc = sb.sc ∧ m'.gcoord = m.gcoord ∧ m'.glo ≤ m.glo ∧ m.ghi ≤ m'.ghi ∧
          sb'.slo ≤ sh ∧ (∀ sh', sb'.shi = some sh' → sh + m.ghi * T.core.dt ≤ sh'))
    (hdt : (0 : ℝ) ≤ (T.core.dt : ℝ)) :
    GuardSettlingB T.core.graph T.GdOf m.fieldOf (Term.const 1) T.core.envF
      ((T.core.dt : ℝ)) q := by
  intro base hb
  obtain ⟨⟨henv, hblo, hbhi⟩, hbslo, hbshi⟩ := (sat_GdOfT hq hsb).mp hb
  have hkR0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hglo0R : (0 : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hglo0
  have hclR : (m.glo : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcl
  have hchR : (c : ℝ) ≤ (m.ghi : ℝ) := by exact_mod_cast hch
  have hbv0 : (0 : ℝ) ≤ base (Rv m.gcoord) := le_trans hglo0R hblo
  -- the active value stays in the guard band: the hull of v₀ and c sits inside [glo, ghi]
  have hbandV : ∀ t, 0 ≤ t →
      (m.glo : ℝ) ≤ terrainValD m sb.sc (k : ℝ) (c : ℝ) base dampers t m.gcoord
      ∧ terrainValD m sb.sc (k : ℝ) (c : ℝ) base dampers t m.gcoord ≤ (m.ghi : ℝ) := by
    intro t ht
    have hθpos : 0 < Real.exp (-((k : ℝ) * t)) := Real.exp_pos _
    have hθle : Real.exp (-((k : ℝ) * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    rw [terrainValD_g hsc]
    rcases le_total (base (Rv m.gcoord)) (c : ℝ) with hbc | hbc
    · constructor
      · nlinarith
      · nlinarith
    · constructor
      · nlinarith
      · nlinarith
  -- the damped increment: its derivative is the integrand v(u)·(1 − Σ a_d ψ_d(u)²)
  have hF' : ∀ u : ℝ, HasDerivAt (fun w => dampVal m (k : ℝ) (c : ℝ) base dampers w)
      (((c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)))
        * (1 - ((dampers.map (fun d =>
            ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1))^2
              * Real.exp (-(2 * dampGain m d * u)))).sum))) u := by
    intro u
    have h1 : HasDerivAt (fun w : ℝ => (c : ℝ) * w) (c : ℝ) u := by
      simpa using (hasDerivAt_id u).const_mul (c : ℝ)
    have h2 : HasDerivAt (fun w => (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) w)
        ((base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u))) u :=
      (expInt_hasDeriv (k : ℝ) u).const_mul _
    have h3 : HasDerivAt (fun w => ((dampers.map (fun d =>
        ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1))^2 *
          ((c : ℝ) * expInt (2 * dampGain m d) w
            + (base (Rv m.gcoord) - (c : ℝ)) * expInt ((k : ℝ) + 2 * dampGain m d) w))).sum))
        ((dampers.map (fun d =>
          ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1))^2 *
            ((c : ℝ) * Real.exp (-(2 * dampGain m d * u))
              + (base (Rv m.gcoord) - (c : ℝ))
                * Real.exp (-(((k : ℝ) + 2 * dampGain m d) * u))))).sum) u := by
      refine hasDerivAt_list_sum dampers _ _ u ?_
      intro d _
      have ha : HasDerivAt (fun w => (c : ℝ) * expInt (2 * dampGain m d) w)
          ((c : ℝ) * Real.exp (-(2 * dampGain m d * u))) u :=
        (expInt_hasDeriv _ u).const_mul _
      have hb : HasDerivAt
          (fun w => (base (Rv m.gcoord) - (c : ℝ)) * expInt ((k : ℝ) + 2 * dampGain m d) w)
          ((base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-(((k : ℝ) + 2 * dampGain m d) * u))) u :=
        (expInt_hasDeriv _ u).const_mul _
      exact (ha.add hb).const_mul _
    have h := (h1.add h2).sub h3
    have heq : (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u))
        - ((dampers.map (fun d =>
          ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1))^2 *
            ((c : ℝ) * Real.exp (-(2 * dampGain m d * u))
              + (base (Rv m.gcoord) - (c : ℝ))
                * Real.exp (-(((k : ℝ) + 2 * dampGain m d) * u))))).sum)
        = ((c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)))
            * (1 - ((dampers.map (fun d =>
              ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1))^2
                * Real.exp (-(2 * dampGain m d * u)))).sum)) := by
      have hlist := dampProd_sum (k : ℝ) (base (Rv m.gcoord) - (c : ℝ)) (c : ℝ) u dampers
        (fun d => ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1))^2)
        (fun d => dampGain m d)
      rw [hlist]
      ring
    unfold dampVal
    rw [← heq]
    exact h
  -- pointwise integrand bounds on [0, ∞): 0 ≤ F' ≤ c
  have hF'bounds : ∀ u : ℝ, 0 ≤ u →
      0 ≤ (((c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)))
        * (1 - ((dampers.map (fun d =>
            ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1))^2
              * Real.exp (-(2 * dampGain m d * u)))).sum)))
      ∧ (((c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)))
        * (1 - ((dampers.map (fun d =>
            ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1))^2
              * Real.exp (-(2 * dampGain m d * u)))).sum))) ≤ (m.ghi : ℝ) := by
    intro u hu
    -- v(u) ∈ [v₀, c] ⊆ [0, c]
    have hθpos : 0 < Real.exp (-((k : ℝ) * u)) := Real.exp_pos _
    have hθle : Real.exp (-((k : ℝ) * u)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have hv0 : 0 ≤ (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)) := by
      rcases le_total (base (Rv m.gcoord)) (c : ℝ) with hbc | hbc
      · nlinarith
      · nlinarith
    have hvc : (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u))
        ≤ (m.ghi : ℝ) := by
      rcases le_total (base (Rv m.gcoord)) (c : ℝ) with hbc | hbc
      · nlinarith
      · nlinarith
    -- each damping term sits in [0, 1/L]
    have hterm : ∀ d ∈ dampers,
        0 ≤ ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1))^2
            * Real.exp (-(2 * dampGain m d * u))
        ∧ ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1))^2
            * Real.exp (-(2 * dampGain m d * u))
          ≤ 1 / (dampers.length : ℝ) := by
      intro d hd
      obtain ⟨-, -, han, had, ⟨kp, hkp, hkp0⟩, lo, hi, hlo, hhi, hlo0, hhi0, hbd⟩ :=
        hdamp d hd
      have hanR : (0 : ℝ) ≤ (d.2.1 : ℝ) := by exact_mod_cast han
      have hadR : (0 : ℝ) < (d.2.2 : ℝ) := by exact_mod_cast had
      have haR : 0 ≤ (d.2.1 : ℝ) / (d.2.2 : ℝ) := div_nonneg hanR hadR.le
      have hgd : (0 : ℝ) ≤ dampGain m d := by
        rw [show dampGain m d = (kp : ℝ) by simp [dampGain, hkp]]
        exact_mod_cast hkp0
      have hθd : Real.exp (-(2 * dampGain m d * u)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith
      have hθdpos : 0 < Real.exp (-(2 * dampGain m d * u)) := Real.exp_pos _
      constructor
      · positivity
      · -- a·b²·θ ≤ a·B² ≤ 1/L, from the base's envelope membership
        have hbe := (sat_envF.mp henv) d.1
        unfold Band.memR at hbe
        rw [hlo, hhi] at hbe
        obtain ⟨hbl, hbh⟩ := hbe
        have hB : (base (Rv d.1))^2 ≤ ((max (-(lo : ℝ)) (hi : ℝ)))^2 := by
          have h1 : -(max (-(lo : ℝ)) (hi : ℝ)) ≤ base (Rv d.1) := by
            have : -(max (-(lo : ℝ)) (hi : ℝ)) ≤ (lo : ℝ) := by
              have := le_max_left (-(lo : ℝ)) (hi : ℝ)
              linarith
            linarith
          have h2 : base (Rv d.1) ≤ max (-(lo : ℝ)) (hi : ℝ) :=
            le_trans hbh (le_max_right _ _)
          exact sq_le_sq' h1 h2
        have hLpos : (0 : ℝ) < (dampers.length : ℝ) := by
          have : dampers.length ≠ 0 := by
            intro h0
            rw [List.length_eq_zero_iff] at h0
            subst h0
            exact absurd hd (List.not_mem_nil)
          exact_mod_cast Nat.pos_of_ne_zero this
        have hbdR : (d.2.1 : ℝ) * ((max (-(lo : ℝ)) (hi : ℝ)))^2 * (dampers.length : ℝ)
            ≤ (d.2.2 : ℝ) := by exact_mod_cast hbd
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ hadR hLpos]
        calc (d.2.1 : ℝ) * (base (Rv d.1))^2 * Real.exp (-(2 * dampGain m d * u))
              * (dampers.length : ℝ)
            ≤ (d.2.1 : ℝ) * ((max (-(lo : ℝ)) (hi : ℝ)))^2 * 1 * (dampers.length : ℝ) := by
              have hsq0 : (0 : ℝ) ≤ (base (Rv d.1))^2 := sq_nonneg _
              have s1 : (d.2.1 : ℝ) * (base (Rv d.1))^2 * Real.exp (-(2 * dampGain m d * u))
                  ≤ (d.2.1 : ℝ) * (base (Rv d.1))^2 * 1 :=
                mul_le_mul_of_nonneg_left hθd (mul_nonneg hanR hsq0)
              have s2 : (d.2.1 : ℝ) * (base (Rv d.1))^2
                  ≤ (d.2.1 : ℝ) * ((max (-(lo : ℝ)) (hi : ℝ)))^2 :=
                mul_le_mul_of_nonneg_left hB hanR
              have s1L := mul_le_mul_of_nonneg_right s1 hLpos.le
              have s2L := mul_le_mul_of_nonneg_right s2 hLpos.le
              nlinarith [s1L, s2L]
          _ = (d.2.1 : ℝ) * ((max (-(lo : ℝ)) (hi : ℝ)))^2 * (dampers.length : ℝ) := by ring
          _ ≤ (d.2.2 : ℝ) := hbdR
          _ = 1 * (d.2.2 : ℝ) := by ring
    -- so the sum sits in [0, 1]
    have hsum0 : 0 ≤ (dampers.map (fun d =>
        ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1))^2
          * Real.exp (-(2 * dampGain m d * u)))).sum := by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
      exact (hterm d hd).1
    have hsum1 : (dampers.map (fun d =>
        ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1))^2
          * Real.exp (-(2 * dampGain m d * u)))).sum ≤ 1 := by
      by_cases hnil : dampers = []
      · subst hnil; simp
      · have hLpos : (0 : ℝ) < (dampers.length : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero
            (fun h0 => hnil (List.length_eq_zero_iff.mp h0))
        calc (dampers.map (fun d =>
              ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1))^2
                * Real.exp (-(2 * dampGain m d * u)))).sum
            ≤ (dampers.map (fun d =>
                ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1))^2
                  * Real.exp (-(2 * dampGain m d * u)))).length
                • (1 / (dampers.length : ℝ)) := by
              apply List.sum_le_card_nsmul
              intro x hx
              obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
              exact (hterm d hd).2
          _ = (dampers.length : ℝ) * (1 / (dampers.length : ℝ)) := by
              rw [List.length_map, nsmul_eq_mul]
          _ = 1 := by field_simp
    constructor
    · nlinarith
    · nlinarith
  -- the position's band: [s₀, s₀ + ghi·t] for all t ≥ 0, by monotonicity from the bounds
  have hbandS : ∀ t, 0 ≤ t →
      base (Rv sb.sc) ≤ terrainValD m sb.sc (k : ℝ) (c : ℝ) base dampers t sb.sc
      ∧ terrainValD m sb.sc (k : ℝ) (c : ℝ) base dampers t sb.sc
          ≤ base (Rv sb.sc) + (m.ghi : ℝ) * t := by
    intro t ht
    have hF0 : dampVal m (k : ℝ) (c : ℝ) base dampers 0 = 0 := by
      unfold dampVal
      simp [expInt]
    have hmono : MonotoneOn (fun w => dampVal m (k : ℝ) (c : ℝ) base dampers w)
        (Icc 0 t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
      · exact fun u _ => ((hF' u).continuousAt).continuousWithinAt
      · intro u _
        exact ((hF' u).differentiableAt).differentiableWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        rw [(hF' u).deriv]
        exact (hF'bounds u (le_of_lt hu.1)).1
    have hmono2 : MonotoneOn
        (fun w => (m.ghi : ℝ) * w - dampVal m (k : ℝ) (c : ℝ) base dampers w)
        (Icc 0 t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
      · intro u _
        exact (((hasDerivAt_id u).const_mul (m.ghi : ℝ)).sub
          (hF' u)).continuousAt.continuousWithinAt
      · intro u _
        have h1 : HasDerivAt (fun w : ℝ => (m.ghi : ℝ) * w) (m.ghi : ℝ) u := by
          simpa using (hasDerivAt_id u).const_mul (m.ghi : ℝ)
        exact ((h1.sub (hF' u)).differentiableAt).differentiableWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        have h1 : HasDerivAt (fun w : ℝ => (m.ghi : ℝ) * w) (m.ghi : ℝ) u := by
          simpa using (hasDerivAt_id u).const_mul (m.ghi : ℝ)
        have hd : HasDerivAt
            (fun w => (m.ghi : ℝ) * w - dampVal m (k : ℝ) (c : ℝ) base dampers w)
            ((m.ghi : ℝ) - (((c : ℝ) + (base (Rv m.gcoord) - (c : ℝ))
                * Real.exp (-((k : ℝ) * u)))
              * (1 - ((dampers.map (fun d =>
                  ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1))^2
                    * Real.exp (-(2 * dampGain m d * u)))).sum)))) u := h1.sub (hF' u)
        rw [hd.deriv]
        have := (hF'bounds u (le_of_lt hu.1)).2
        linarith
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_refl _, ht⟩
    have htmem : t ∈ Icc (0 : ℝ) t := ⟨ht, le_refl _⟩
    have hlow := hmono h0mem htmem ht
    have hhigh := hmono2 h0mem htmem ht
    simp only [] at hlow hhigh
    rw [hF0] at hlow hhigh
    rw [terrainValD_s]
    simp only [mul_zero, sub_zero, zero_sub, neg_nonpos] at hlow hhigh
    constructor
    · linarith
    · have : (m.ghi : ℝ) * t - dampVal m (k : ℝ) (c : ℝ) base dampers t ≥ 0 := by
        simpa using hhigh
      linarith
  -- a contract other stays in the hull of its base and its equilibrium
  have hbandO : ∀ (i : Fin n) (k' c' : ℤ), i ≠ m.gcoord → i ≠ sb.sc → 0 ≤ k' →
      m.shapes i = CoordShape.contract k' c' → ∀ t, 0 ≤ t →
      min (base (Rv i)) (c' : ℝ) ≤ terrainValD m sb.sc (k : ℝ) (c : ℝ) base dampers t i
      ∧ terrainValD m sb.sc (k : ℝ) (c : ℝ) base dampers t i ≤ max (base (Rv i)) (c' : ℝ) := by
    intro i k' c' hig his hk' hshi t ht
    have hk'R : (0 : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hk'
    have hθpos : 0 < Real.exp (-((k' : ℝ) * t)) := Real.exp_pos _
    have hθle : Real.exp (-((k' : ℝ) * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    rw [terrainValD_contract hig his hshi]
    rcases le_total (base (Rv i)) (c' : ℝ) with hbc' | hbc'
    · rw [min_eq_left hbc', max_eq_right hbc']
      constructor
      · nlinarith
      · nlinarith
    · rw [min_eq_right hbc', max_eq_left hbc']
      constructor
      · nlinarith
      · nlinarith
  -- staying in the envelope
  have hstayEnv : ∀ t, 0 ≤ t →
      Formula.sat T.core.envF (terrainΦD m sb.sc (k : ℝ) (c : ℝ) base dampers t) := by
    intro t ht
    rw [sat_envF]
    intro i
    rw [terrainΦD_Rv]
    by_cases hig : i = m.gcoord
    · rw [hig]
      obtain ⟨h1, h2⟩ := hbandV t ht
      have hbe := (sat_envF.mp henv) m.gcoord
      unfold Band.memR at hbe ⊢
      rcases hbe with ⟨hbl, hbh⟩
      constructor
      · cases hcase : (T.core.env m.gcoord).lo with
        | none => trivial
        | some l =>
            have hlG : (l : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hvLo l hcase
            linarith
      · cases hcase : (T.core.env m.gcoord).hi with
        | none => trivial
        | some h =>
            have hgh : (m.ghi : ℝ) ≤ (h : ℝ) := by exact_mod_cast hvHi h hcase
            linarith
    · by_cases his : i = sb.sc
      · rw [his]
        obtain ⟨h1, h2⟩ := hbandS t ht
        unfold Band.memR
        constructor
        · cases hcase : (T.core.env sb.sc).lo with
          | none => trivial
          | some l =>
              have hlG : (l : ℝ) ≤ (sb.slo : ℝ) := by exact_mod_cast hsloIn l hcase
              linarith
        · rw [hsHiNone]; trivial
      · rcases hOth i hig his with hfz | ⟨k', c', hshi, hk', hloO, hhiO⟩ | hchase
        · rw [terrainValD_frozen hig his hfz]
          exact (sat_envF.mp henv) i
        · obtain ⟨h1, h2⟩ := hbandO i k' c' hig his hk' hshi t ht
          have hbe := (sat_envF.mp henv) i
          unfold Band.memR at hbe ⊢
          rcases hbe with ⟨hbl, hbh⟩
          constructor
          · cases hcase : (T.core.env i).lo with
            | none => trivial
            | some l =>
                rw [hcase] at hbl
                have hlc : (l : ℝ) ≤ (c' : ℝ) := by exact_mod_cast hloO l hcase
                have hmin : (l : ℝ) ≤ min (base (Rv i)) (c' : ℝ) := le_min hbl hlc
                linarith
          · cases hcase : (T.core.env i).hi with
            | none => trivial
            | some h =>
                rw [hcase] at hbh
                have hhc : (c' : ℝ) ≤ (h : ℝ) := by exact_mod_cast hhiO h hcase
                have hmax : max (base (Rv i)) (c' : ℝ) ≤ (h : ℝ) := max_le hbh hhc
                linarith
        · obtain ⟨j2, k2, loi, hii, loj, hij, hshi, hj2g, hj2s, hj2c, hk2, hloi, hhii,
            hloj, hhij, hloi0, hhii0, hijle, hlojge⟩ := hchase
          have hbi := (sat_envF.mp henv) i
          have hbj := (sat_envF.mp henv) j2
          unfold Band.memR at hbi hbj ⊢
          rw [hloi, hhii] at hbi ⊢
          rw [hloj, hhij] at hbj
          obtain ⟨hbl, hbh⟩ := hbi
          obtain ⟨hbjl, hbjh⟩ := hbj
          have hband := chase_band (kR := (k : ℝ)) (cR := (c : ℝ)) hig his hshi hk2
            hloi0 hhii0 hijle hlojge hbl hbh hbjl hbjh ht
          rw [← terrainValD_ne (dampers := dampers) his] at hband
          exact hband
  -- landing: the own box below `shi`, the declared successor above
  have hpick : ∃ q2 ∈ q :: T.core.graph.retainedSucc q,
      Formula.sat (T.GdOf q2) (terrainΦD m sb.sc (k : ℝ) (c : ℝ) base dampers (T.core.dt : ℝ)) := by
    obtain ⟨hv1, hv2⟩ := hbandV (T.core.dt : ℝ) hdt
    obtain ⟨hs1, hs2⟩ := hbandS (T.core.dt : ℝ) hdt
    have hself_v : (m.glo : ℝ) ≤ terrainValD m sb.sc (k : ℝ) (c : ℝ) base dampers (T.core.dt : ℝ)
        m.gcoord ∧ terrainValD m sb.sc (k : ℝ) (c : ℝ) base dampers (T.core.dt : ℝ) m.gcoord
          ≤ (m.ghi : ℝ) := ⟨hv1, hv2⟩
    cases hshi : sb.shi with
    | none =>
        refine ⟨q, List.mem_cons_self .., ?_⟩
        rw [sat_GdOfT hq hsb]
        refine ⟨⟨hstayEnv _ hdt, by rw [terrainΦD_Rv]; exact hself_v.1,
          by rw [terrainΦD_Rv]; exact hself_v.2⟩,
          by rw [terrainΦD_Rv]; linarith, ?_⟩
        intro sh' hsh'
        rw [hshi] at hsh'
        exact absurd hsh' (by simp)
    | some sh =>
        obtain ⟨q', hq'mem, m', sb', hm', hsb', hsc', hgc', hglo', hghi', hslo', hshi'⟩ :=
          hland sh hshi
        have hbs_sh : base (Rv sb.sc) ≤ (sh : ℝ) := hbshi sh hshi
        rcases le_or_gt (terrainValD m sb.sc (k : ℝ) (c : ℝ) base dampers (T.core.dt : ℝ) sb.sc)
          ((sh : ℝ)) with he | he
        · -- self
          refine ⟨q, List.mem_cons_self .., ?_⟩
          rw [sat_GdOfT hq hsb]
          refine ⟨⟨hstayEnv _ hdt, by rw [terrainΦD_Rv]; exact hself_v.1,
            by rw [terrainΦD_Rv]; exact hself_v.2⟩,
            by rw [terrainΦD_Rv]; linarith, ?_⟩
          intro sh' hsh'
          rw [hshi] at hsh'
          cases hsh'
          rw [terrainΦD_Rv]
          exact he
        · -- successor
          have hglo'R : (m'.glo : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hglo'
          have hghi'R : (m.ghi : ℝ) ≤ (m'.ghi : ℝ) := by exact_mod_cast hghi'
          have hslo'R : (sb'.slo : ℝ) ≤ (sh : ℝ) := by exact_mod_cast hslo'
          refine ⟨q', List.mem_cons_of_mem _ (succ_mem_retained T.core hq hq'mem), ?_⟩
          rw [sat_GdOfT hm' hsb']
          refine ⟨⟨hstayEnv _ hdt, ?_, ?_⟩, ?_, ?_⟩
          · rw [hgc', terrainΦD_Rv]; linarith
          · rw [hgc', terrainΦD_Rv]; linarith
          · rw [hsc', terrainΦD_Rv]; linarith
          · intro sh' hsh'
            have hcov : (sh : ℝ) + (m.ghi : ℝ) * (T.core.dt : ℝ) ≤ (sh' : ℝ) := by
              exact_mod_cast hshi' sh' hsh'
            rw [hsc', terrainΦD_Rv]
            linarith
  obtain ⟨q2, hq2ret, hq2sat⟩ := hpick
  refine ⟨terrainΦD m sb.sc (k : ℝ) (c : ℝ) base dampers, ?_, ?_, ?_,
    fun t ht => hstayEnv t ht.1, q2, hq2ret, hq2sat⟩
  · -- t = 0 recovers the base
    funext x
    obtain ⟨sd, ix⟩ := x
    cases sd with
    | R =>
        show terrainValD m sb.sc (k : ℝ) (c : ℝ) base dampers 0 ix = base (Rv ix)
        by_cases his : ix = sb.sc
        · rw [his, terrainValD_s]
          have h0 : dampVal m (k : ℝ) (c : ℝ) base dampers 0 = 0 := by
            unfold dampVal
            simp [expInt]
          rw [h0, add_zero]
        · rw [terrainValD_ne his]
          unfold terrainVal
          by_cases hig : ix = m.gcoord
          · rw [if_pos hig]; subst hig; simp
          · rw [if_neg hig, if_neg his]
            rcases hshx : m.shapes ix with _ | _ | _ | _ | _ | _ <;> simp
    | L => rfl
    | Aux => rfl
  · -- derivatives
    intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hig : i = m.gcoord
    · rw [hig]
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf m.gcoord))
          (terrainΦD m sb.sc (k : ℝ) (c : ℝ) base dampers t)
          = (k : ℝ) * ((c : ℝ) - terrainValD m sb.sc (k : ℝ) (c : ℝ) base dampers t m.gcoord) := by
        simp [SettlingMode.fieldOf, hsh, CoordShape.field, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => terrainΦD m sb.sc (k : ℝ) (c : ℝ) base dampers u (Rv m.gcoord))
          = fun u => (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)) := by
        funext u; rw [terrainΦD_Rv, terrainValD_g hsc]
      rw [hcurve]
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
          = (k : ℝ) * ((c : ℝ) - terrainValD m sb.sc (k : ℝ) (c : ℝ) base dampers t m.gcoord) := by
        rw [terrainValD_g hsc]; ring
      rw [← heq]
      exact h1.hasDerivWithinAt
    · by_cases his : i = sb.sc
      · rw [his]
        -- the field eval at the witness: v(t) times the damping factor at the damper values
        have hdampval : ∀ d ∈ dampers,
            terrainValD m sb.sc (k : ℝ) (c : ℝ) base dampers t d.1
              = base (Rv d.1) * Real.exp (-(dampGain m d * t)) := by
          intro d hd
          obtain ⟨hdg, hds, -, -, ⟨kp, hkp, -⟩, -⟩ := hdamp d hd
          rw [terrainValD_contract hdg hds hkp]
          unfold dampGain
          rw [hkp]
          simp
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf sb.sc))
            (terrainΦD m sb.sc (k : ℝ) (c : ℝ) base dampers t)
            = (((c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * t)))
              * (1 - ((dampers.map (fun d =>
                  ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1))^2
                    * Real.exp (-(2 * dampGain m d * t)))).sum))) := by
          have hbase := eval_drivenDamp_field hscd
            (terrainΦD m sb.sc (k : ℝ) (c : ℝ) base dampers t)
          have h1eval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf sb.sc))
              (terrainΦD m sb.sc (k : ℝ) (c : ℝ) base dampers t)
              = Term.eval (m.fieldOf sb.sc)
                  (terrainΦD m sb.sc (k : ℝ) (c : ℝ) base dampers t) := by
            simp [Term.eval, AOp.interp]
          rw [h1eval, hbase]
          rw [terrainΦD_Rv, terrainValD_g hsc]
          congr 2
          refine congrArg List.sum (List.map_congr_left ?_)
          intro d hd
          rw [terrainΦD_Rv, hdampval d hd]
          have hsq : (base (Rv d.1) * Real.exp (-(dampGain m d * t)))^2
              = (base (Rv d.1))^2 * Real.exp (-(2 * dampGain m d * t)) := by
            rw [mul_pow]
            congr 1
            rw [show (-(2 * dampGain m d * t)) = ((2 : ℕ) : ℝ) * (-(dampGain m d * t)) by
              push_cast; ring, Real.exp_nat_mul]
          rw [hsq]
          ring
        rw [heval]
        have hcurve : (fun u => terrainΦD m sb.sc (k : ℝ) (c : ℝ) base dampers u (Rv sb.sc))
            = fun u => base (Rv sb.sc) + dampVal m (k : ℝ) (c : ℝ) base dampers u := by
          funext u
          rw [terrainΦD_Rv, terrainValD_s]
        rw [hcurve]
        exact ((hF' t).const_add (base (Rv sb.sc))).hasDerivWithinAt
      · rcases hOth i hig his with hfz | ⟨k', c', hshi, -, -, -⟩ | hchase
        · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
              (terrainΦD m sb.sc (k : ℝ) (c : ℝ) base dampers t) = 0 := by
            simp [SettlingMode.fieldOf, hfz, CoordShape.field, Term.eval, AOp.interp]
          rw [heval]
          have hcurve : (fun u => terrainΦD m sb.sc (k : ℝ) (c : ℝ) base dampers u (Rv i))
              = fun _ => base (Rv i) := by
            funext u; rw [terrainΦD_Rv, terrainValD_frozen hig his hfz]
          rw [hcurve]
          exact hasDerivWithinAt_const t _ _
        · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
              (terrainΦD m sb.sc (k : ℝ) (c : ℝ) base dampers t)
              = (k' : ℝ) * ((c' : ℝ) - terrainValD m sb.sc (k : ℝ) (c : ℝ) base dampers t i) := by
            simp [SettlingMode.fieldOf, hshi, CoordShape.field, Term.eval, AOp.interp]
          rw [heval]
          have hcurve : (fun u => terrainΦD m sb.sc (k : ℝ) (c : ℝ) base dampers u (Rv i))
              = fun u => (c' : ℝ) + (base (Rv i) - (c' : ℝ)) * Real.exp (-((k' : ℝ) * u)) := by
            funext u; rw [terrainΦD_Rv, terrainValD_contract hig his hshi]
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
              = (k' : ℝ) * ((c' : ℝ) - terrainValD m sb.sc (k : ℝ) (c : ℝ) base dampers t i) := by
            rw [terrainValD_contract hig his hshi]; ring
          rw [← heq]
          exact h1.hasDerivWithinAt
        · obtain ⟨j2, k2, loi, hii, loj, hij, hshi, hj2g, hj2s, hj2c, hk2, -, -, -, -,
            -, -, -, -⟩ := hchase
          have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
              (terrainΦD m sb.sc (k : ℝ) (c : ℝ) base dampers t)
              = terrainValD m sb.sc (k : ℝ) (c : ℝ) base dampers t j2
                - (k2 : ℝ) * terrainValD m sb.sc (k : ℝ) (c : ℝ) base dampers t i := by
            simp [SettlingMode.fieldOf, hshi, CoordShape.field, Term.eval, AOp.interp]
          rw [heval]
          have hcurve : (fun u => terrainΦD m sb.sc (k : ℝ) (c : ℝ) base dampers u (Rv i))
              = fun u => (base (Rv i) + base (Rv j2) * u) * Real.exp (-((k2 : ℝ) * u)) := by
            funext u; rw [terrainΦD_Rv, terrainValD_chase hig his hshi]
          rw [hcurve]
          have hlin : HasDerivAt (fun u : ℝ => base (Rv i) + base (Rv j2) * u)
              (base (Rv j2)) t := by
            simpa using ((hasDerivAt_id t).const_mul (base (Rv j2))).const_add (base (Rv i))
          have hexp : HasDerivAt (fun u : ℝ => Real.exp (-((k2 : ℝ) * u)))
              (-(k2 : ℝ) * Real.exp (-((k2 : ℝ) * t))) t := by
            have hinner : HasDerivAt (fun u : ℝ => -((k2 : ℝ) * u)) (-(k2 : ℝ)) t := by
              have h := (hasDerivAt_id t).const_mul (-(k2 : ℝ))
              simp only [id, mul_one, neg_mul] at h
              exact h
            have h := (Real.hasDerivAt_exp (-((k2 : ℝ) * t))).comp t hinner
            simp only [Function.comp_def] at h
            rw [mul_comm (Real.exp (-((k2 : ℝ) * t))) (-(k2 : ℝ))] at h
            exact h
          have h1 := hlin.mul hexp
          have heq : base (Rv j2) * Real.exp (-((k2 : ℝ) * t))
              + (base (Rv i) + base (Rv j2) * t) * (-(k2 : ℝ) * Real.exp (-((k2 : ℝ) * t)))
              = terrainValD m sb.sc (k : ℝ) (c : ℝ) base dampers t j2
                - (k2 : ℝ) * terrainValD m sb.sc (k : ℝ) (c : ℝ) base dampers t i := by
            rw [terrainValD_chase hig his hshi, terrainValD_contract hj2g hj2s hj2c]
            push_cast
            ring
          rw [← heq]
          exact h1.hasDerivWithinAt
  · -- mask
    intro t ht x hx
    refine terrainΦD_nonR m sb.sc (k : ℝ) (c : ℝ) base dampers t ?_
    intro i hxi
    exact hx (by
      rw [hxi]
      simp only [rightBlock, ODESystem.bound, List.map_map]
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)


/-- TERRAIN mode, cascade dampers (EXT 4c): like `settling_terrain_damp`, but each damper
is a `chase` coordinate `ψ_d(u) = (p_d + w_d·u)e^{−g_d·u}`; the damping factor stays in
`[0, 1]` by the pointwise band `|ψ_d(u)| ≤ B_d` (`chase_val_band`) and the per-damper
budget, and the position integrates in closed form through `polyExpInt₁/₂`. -/
theorem settling_terrain_dampC (T : TerrainModel n) {q : ℕ} {m : SettlingMode n} {sb : SBand n}
    (hq : T.core.modes[q]? = some m) (hsb : T.sbands[q]? = some sb) {k c : ℤ}
    (hsh : m.shapes m.gcoord = CoordShape.contract k c)
    (hk : 0 ≤ k) (hcl : m.glo ≤ c) (hch : c ≤ m.ghi) (hglo0 : 0 ≤ m.glo)
    (hvLo : ∀ l', (T.core.env m.gcoord).lo = some l' → l' ≤ m.glo)
    (hvHi : ∀ h', (T.core.env m.gcoord).hi = some h' → m.ghi ≤ h')
    (hsc : sb.sc ≠ m.gcoord)
    {dampers : List (Fin n × ℤ × ℤ)}
    (hscd : m.shapes sb.sc = CoordShape.drivenDamp m.gcoord dampers)
    (hdamp : ∀ d ∈ dampers, d.1 ≠ m.gcoord ∧ d.1 ≠ sb.sc ∧ 0 ≤ d.2.1 ∧ 0 < d.2.2 ∧
        ∃ jd kd, m.shapes d.1 = CoordShape.chase jd kd ∧ 0 < kd ∧
          ∃ lo hi loj hij, (T.core.env d.1).lo = some lo ∧ (T.core.env d.1).hi = some hi ∧
            (T.core.env jd).lo = some loj ∧ (T.core.env jd).hi = some hij ∧
            lo ≤ 0 ∧ 0 ≤ hi ∧ hij ≤ kd * hi ∧ kd * lo ≤ loj ∧
            d.2.1 * (max (-lo) hi) ^ 2 * (dampers.length : ℤ) ≤ d.2.2)
    (hsloIn : ∀ l', (T.core.env sb.sc).lo = some l' → l' ≤ sb.slo)
    (hsHiNone : (T.core.env sb.sc).hi = none)
    (hOth : ∀ i, i ≠ m.gcoord → i ≠ sb.sc →
        m.shapes i = CoordShape.frozen ∨
        (∃ k' c', m.shapes i = CoordShape.contract k' c' ∧ 0 ≤ k' ∧
          (∀ l', (T.core.env i).lo = some l' → l' ≤ c') ∧
          (∀ h', (T.core.env i).hi = some h' → c' ≤ h')) ∨
        (∃ j2 k2 loi hii loj hij, m.shapes i = CoordShape.chase j2 k2 ∧
          j2 ≠ m.gcoord ∧ j2 ≠ sb.sc ∧ m.shapes j2 = CoordShape.contract k2 0 ∧ 0 < k2 ∧
          (T.core.env i).lo = some loi ∧ (T.core.env i).hi = some hii ∧
          (T.core.env j2).lo = some loj ∧ (T.core.env j2).hi = some hij ∧
          loi ≤ 0 ∧ 0 ≤ hii ∧ hij ≤ k2 * hii ∧ k2 * loi ≤ loj))
    (hland : ∀ sh, sb.shi = some sh →
        ∃ q' ∈ m.succs, ∃ m' sb', T.core.modes[q']? = some m' ∧ T.sbands[q']? = some sb' ∧
          sb'.sc = sb.sc ∧ m'.gcoord = m.gcoord ∧ m'.glo ≤ m.glo ∧ m.ghi ≤ m'.ghi ∧
          sb'.slo ≤ sh ∧ (∀ sh', sb'.shi = some sh' → sh + m.ghi * T.core.dt ≤ sh'))
    (hdt : (0 : ℝ) ≤ (T.core.dt : ℝ)) :
    GuardSettlingB T.core.graph T.GdOf m.fieldOf (Term.const 1) T.core.envF
      ((T.core.dt : ℝ)) q := by
  intro base hb
  obtain ⟨⟨henv, hblo, hbhi⟩, hbslo, hbshi⟩ := (sat_GdOfT hq hsb).mp hb
  have hkR0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hglo0R : (0 : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hglo0
  have hclR : (m.glo : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcl
  have hchR : (c : ℝ) ≤ (m.ghi : ℝ) := by exact_mod_cast hch
  have hbv0 : (0 : ℝ) ≤ base (Rv m.gcoord) := le_trans hglo0R hblo
  -- the active value stays in the guard band
  have hbandV : ∀ t, 0 ≤ t →
      (m.glo : ℝ) ≤ terrainValDC m sb.sc (k : ℝ) (c : ℝ) base dampers t m.gcoord
      ∧ terrainValDC m sb.sc (k : ℝ) (c : ℝ) base dampers t m.gcoord ≤ (m.ghi : ℝ) := by
    intro t ht
    have hθpos : 0 < Real.exp (-((k : ℝ) * t)) := Real.exp_pos _
    have hθle : Real.exp (-((k : ℝ) * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    rw [terrainValDC_g hsc]
    rcases le_total (base (Rv m.gcoord)) (c : ℝ) with hbc | hbc
    · constructor
      · nlinarith
      · nlinarith
    · constructor
      · nlinarith
      · nlinarith
  -- the damped increment's derivative: the integrand v(u)·(1 − Σ a_d ψ_d(u)²)
  have hF' : ∀ u : ℝ, HasDerivAt (fun w => dampValC m (k : ℝ) (c : ℝ) base dampers w)
      (((c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)))
        * (1 - ((dampers.map (fun d =>
            ((d.2.1 : ℝ) / (d.2.2 : ℝ))
              * (base (Rv d.1) + chaseDrv m base d * u) ^ 2
              * Real.exp (-(2 * chaseGain m d * u)))).sum))) u := by
    intro u
    have h1 : HasDerivAt (fun w : ℝ => (c : ℝ) * w) (c : ℝ) u := by
      simpa using (hasDerivAt_id u).const_mul (c : ℝ)
    have h2 : HasDerivAt (fun w => (base (Rv m.gcoord) - (c : ℝ)) * expInt (k : ℝ) w)
        ((base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u))) u :=
      (expInt_hasDeriv (k : ℝ) u).const_mul _
    have h3 : HasDerivAt (fun w => ((dampers.map (fun d =>
        ((d.2.1 : ℝ) / (d.2.2 : ℝ)) *
          ((c : ℝ) * ((base (Rv d.1)) ^ 2 * expInt (2 * chaseGain m d) w
              + 2 * base (Rv d.1) * chaseDrv m base d * polyExpInt₁ (2 * chaseGain m d) w
              + (chaseDrv m base d) ^ 2 * polyExpInt₂ (2 * chaseGain m d) w)
           + (base (Rv m.gcoord) - (c : ℝ)) *
              ((base (Rv d.1)) ^ 2 * expInt ((k : ℝ) + 2 * chaseGain m d) w
              + 2 * base (Rv d.1) * chaseDrv m base d
                  * polyExpInt₁ ((k : ℝ) + 2 * chaseGain m d) w
              + (chaseDrv m base d) ^ 2
                  * polyExpInt₂ ((k : ℝ) + 2 * chaseGain m d) w)))).sum))
        ((dampers.map (fun d =>
          ((d.2.1 : ℝ) / (d.2.2 : ℝ)) *
            ((c : ℝ) * ((base (Rv d.1)) ^ 2 * Real.exp (-(2 * chaseGain m d * u))
                + 2 * base (Rv d.1) * chaseDrv m base d
                    * (u * Real.exp (-(2 * chaseGain m d * u)))
                + (chaseDrv m base d) ^ 2
                    * (u ^ 2 * Real.exp (-(2 * chaseGain m d * u))))
             + (base (Rv m.gcoord) - (c : ℝ)) *
                ((base (Rv d.1)) ^ 2 * Real.exp (-(((k : ℝ) + 2 * chaseGain m d) * u))
                + 2 * base (Rv d.1) * chaseDrv m base d
                    * (u * Real.exp (-(((k : ℝ) + 2 * chaseGain m d) * u)))
                + (chaseDrv m base d) ^ 2
                    * (u ^ 2 * Real.exp (-(((k : ℝ) + 2 * chaseGain m d) * u))))))).sum) u := by
      refine hasDerivAt_list_sum dampers _ _ u ?_
      intro d hd
      obtain ⟨-, -, -, -, jd, kd, hkp, hkd, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
        hdamp d hd
      have hgd : (0 : ℝ) < chaseGain m d := by
        rw [show chaseGain m d = (kd : ℝ) by simp [chaseGain, hkp]]
        exact_mod_cast hkd
      have hm1 : 2 * chaseGain m d ≠ 0 := ne_of_gt (by linarith)
      have hm2 : (k : ℝ) + 2 * chaseGain m d ≠ 0 := ne_of_gt (by linarith)
      have hA1 : HasDerivAt (fun w => (base (Rv d.1)) ^ 2 * expInt (2 * chaseGain m d) w)
          ((base (Rv d.1)) ^ 2 * Real.exp (-(2 * chaseGain m d * u))) u :=
        (expInt_hasDeriv _ u).const_mul _
      have hA2 : HasDerivAt (fun w => 2 * base (Rv d.1) * chaseDrv m base d
            * polyExpInt₁ (2 * chaseGain m d) w)
          (2 * base (Rv d.1) * chaseDrv m base d
            * (u * Real.exp (-(2 * chaseGain m d * u)))) u :=
        (polyExpInt₁_hasDeriv hm1 u).const_mul _
      have hA3 : HasDerivAt (fun w => (chaseDrv m base d) ^ 2
            * polyExpInt₂ (2 * chaseGain m d) w)
          ((chaseDrv m base d) ^ 2 * (u ^ 2 * Real.exp (-(2 * chaseGain m d * u)))) u :=
        (polyExpInt₂_hasDeriv hm1 u).const_mul _
      have hB1 : HasDerivAt (fun w => (base (Rv d.1)) ^ 2
            * expInt ((k : ℝ) + 2 * chaseGain m d) w)
          ((base (Rv d.1)) ^ 2 * Real.exp (-(((k : ℝ) + 2 * chaseGain m d) * u))) u :=
        (expInt_hasDeriv _ u).const_mul _
      have hB2 : HasDerivAt (fun w => 2 * base (Rv d.1) * chaseDrv m base d
            * polyExpInt₁ ((k : ℝ) + 2 * chaseGain m d) w)
          (2 * base (Rv d.1) * chaseDrv m base d
            * (u * Real.exp (-(((k : ℝ) + 2 * chaseGain m d) * u)))) u :=
        (polyExpInt₁_hasDeriv hm2 u).const_mul _
      have hB3 : HasDerivAt (fun w => (chaseDrv m base d) ^ 2
            * polyExpInt₂ ((k : ℝ) + 2 * chaseGain m d) w)
          ((chaseDrv m base d) ^ 2
            * (u ^ 2 * Real.exp (-(((k : ℝ) + 2 * chaseGain m d) * u)))) u :=
        (polyExpInt₂_hasDeriv hm2 u).const_mul _
      exact ((((hA1.add hA2).add hA3).const_mul (c : ℝ)).add
        ((((hB1.add hB2).add hB3).const_mul (base (Rv m.gcoord) - (c : ℝ))))).const_mul _
    have h := (h1.add h2).sub h3
    have hcong : dampers.map (fun d =>
          ((d.2.1 : ℝ) / (d.2.2 : ℝ)) *
            ((c : ℝ) * ((base (Rv d.1)) ^ 2 * Real.exp (-(2 * chaseGain m d * u))
                + 2 * base (Rv d.1) * chaseDrv m base d
                    * (u * Real.exp (-(2 * chaseGain m d * u)))
                + (chaseDrv m base d) ^ 2
                    * (u ^ 2 * Real.exp (-(2 * chaseGain m d * u))))
             + (base (Rv m.gcoord) - (c : ℝ)) *
                ((base (Rv d.1)) ^ 2 * Real.exp (-(((k : ℝ) + 2 * chaseGain m d) * u))
                + 2 * base (Rv d.1) * chaseDrv m base d
                    * (u * Real.exp (-(((k : ℝ) + 2 * chaseGain m d) * u)))
                + (chaseDrv m base d) ^ 2
                    * (u ^ 2 * Real.exp (-(((k : ℝ) + 2 * chaseGain m d) * u))))))
        = dampers.map (fun d =>
            (((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1) + chaseDrv m base d * u) ^ 2)
              * ((c : ℝ) * Real.exp (-(2 * chaseGain m d * u))
                 + (base (Rv m.gcoord) - (c : ℝ))
                     * Real.exp (-(((k : ℝ) + 2 * chaseGain m d) * u)))) := by
      refine List.map_congr_left ?_
      intro d _
      ring
    have heq : (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u))
        - ((dampers.map (fun d =>
          ((d.2.1 : ℝ) / (d.2.2 : ℝ)) *
            ((c : ℝ) * ((base (Rv d.1)) ^ 2 * Real.exp (-(2 * chaseGain m d * u))
                + 2 * base (Rv d.1) * chaseDrv m base d
                    * (u * Real.exp (-(2 * chaseGain m d * u)))
                + (chaseDrv m base d) ^ 2
                    * (u ^ 2 * Real.exp (-(2 * chaseGain m d * u))))
             + (base (Rv m.gcoord) - (c : ℝ)) *
                ((base (Rv d.1)) ^ 2 * Real.exp (-(((k : ℝ) + 2 * chaseGain m d) * u))
                + 2 * base (Rv d.1) * chaseDrv m base d
                    * (u * Real.exp (-(((k : ℝ) + 2 * chaseGain m d) * u)))
                + (chaseDrv m base d) ^ 2
                    * (u ^ 2 * Real.exp (-(((k : ℝ) + 2 * chaseGain m d) * u))))))).sum)
        = ((c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)))
            * (1 - ((dampers.map (fun d =>
                ((d.2.1 : ℝ) / (d.2.2 : ℝ))
                  * (base (Rv d.1) + chaseDrv m base d * u) ^ 2
                  * Real.exp (-(2 * chaseGain m d * u)))).sum)) := by
      rw [hcong]
      have hlist := dampProd_sum (k : ℝ) (base (Rv m.gcoord) - (c : ℝ)) (c : ℝ) u dampers
        (fun d => ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1) + chaseDrv m base d * u) ^ 2)
        (fun d => chaseGain m d)
      rw [hlist]
      have hcong2 : dampers.map (fun d =>
            ((d.2.1 : ℝ) / (d.2.2 : ℝ))
              * (base (Rv d.1) + chaseDrv m base d * u) ^ 2
              * Real.exp (-(2 * chaseGain m d * u)))
          = dampers.map (fun d =>
              (((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1) + chaseDrv m base d * u) ^ 2)
                * Real.exp (-(2 * chaseGain m d * u))) := by
        refine List.map_congr_left ?_
        intro d _
        ring
      rw [hcong2]
      ring
    unfold dampValC
    rw [← heq]
    exact h
  -- pointwise integrand bounds on [0, ∞): 0 ≤ F' ≤ ghi
  have hF'bounds : ∀ u : ℝ, 0 ≤ u →
      0 ≤ (((c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)))
        * (1 - ((dampers.map (fun d =>
            ((d.2.1 : ℝ) / (d.2.2 : ℝ))
              * (base (Rv d.1) + chaseDrv m base d * u) ^ 2
              * Real.exp (-(2 * chaseGain m d * u)))).sum)))
      ∧ (((c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)))
        * (1 - ((dampers.map (fun d =>
            ((d.2.1 : ℝ) / (d.2.2 : ℝ))
              * (base (Rv d.1) + chaseDrv m base d * u) ^ 2
              * Real.exp (-(2 * chaseGain m d * u)))).sum))) ≤ (m.ghi : ℝ) := by
    intro u hu
    have hθpos : 0 < Real.exp (-((k : ℝ) * u)) := Real.exp_pos _
    have hθle : Real.exp (-((k : ℝ) * u)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have hv0 : 0 ≤ (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)) := by
      rcases le_total (base (Rv m.gcoord)) (c : ℝ) with hbc | hbc
      · nlinarith
      · nlinarith
    have hvc : (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u))
        ≤ (m.ghi : ℝ) := by
      rcases le_total (base (Rv m.gcoord)) (c : ℝ) with hbc | hbc
      · nlinarith
      · nlinarith
    -- each damping term sits in [0, 1/L]: pointwise |ψ_d(u)| ≤ B_d, then the budget
    have hterm : ∀ d ∈ dampers,
        0 ≤ ((d.2.1 : ℝ) / (d.2.2 : ℝ))
            * (base (Rv d.1) + chaseDrv m base d * u) ^ 2
            * Real.exp (-(2 * chaseGain m d * u))
        ∧ ((d.2.1 : ℝ) / (d.2.2 : ℝ))
            * (base (Rv d.1) + chaseDrv m base d * u) ^ 2
            * Real.exp (-(2 * chaseGain m d * u))
          ≤ 1 / (dampers.length : ℝ) := by
      intro d hd
      obtain ⟨-, -, han, had, jd, kd, hkp, hkd, lo, hi, loj, hij, hlo, hhi, hloj, hhij,
        hlo0, hhi0, hijle, hlojge, hbd⟩ := hdamp d hd
      have hanR : (0 : ℝ) ≤ (d.2.1 : ℝ) := by exact_mod_cast han
      have hadR : (0 : ℝ) < (d.2.2 : ℝ) := by exact_mod_cast had
      have hdrv : chaseDrv m base d = base (Rv jd) := by simp [chaseDrv, hkp]
      have hgain : chaseGain m d = (kd : ℝ) := by simp [chaseGain, hkp]
      rw [hdrv, hgain]
      have hkdR : (0 : ℝ) < (kd : ℝ) := by exact_mod_cast hkd
      -- the base's envelope memberships
      have hbe := (sat_envF.mp henv) d.1
      have hbej := (sat_envF.mp henv) jd
      unfold Band.memR at hbe hbej
      rw [hlo, hhi] at hbe
      rw [hloj, hhij] at hbej
      obtain ⟨hbl, hbh⟩ := hbe
      obtain ⟨hjl, hjh⟩ := hbej
      have hloR : (lo : ℝ) ≤ 0 := by exact_mod_cast hlo0
      have hhiR : (0 : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hhi0
      have hijR : (hij : ℝ) ≤ (kd : ℝ) * (hi : ℝ) := by exact_mod_cast hijle
      have hlojR : (kd : ℝ) * (lo : ℝ) ≤ (loj : ℝ) := by exact_mod_cast hlojge
      have hband := chase_val_band hkdR hloR hhiR hijR hlojR hbl hbh hjl hjh hu
      have hsqid : ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1) + base (Rv jd) * u) ^ 2
            * Real.exp (-(2 * (kd : ℝ) * u))
          = ((d.2.1 : ℝ) / (d.2.2 : ℝ))
              * ((base (Rv d.1) + base (Rv jd) * u) * Real.exp (-((kd : ℝ) * u))) ^ 2 := by
        have hexp2 : Real.exp (-(2 * (kd : ℝ) * u)) = Real.exp (-((kd : ℝ) * u)) ^ 2 := by
          rw [show (-(2 * (kd : ℝ) * u)) = ((2 : ℕ) : ℝ) * (-((kd : ℝ) * u)) by
            push_cast; ring, Real.exp_nat_mul]
        rw [hexp2]
        ring
      rw [hsqid]
      constructor
      · positivity
      · -- ψ(u)² ≤ B², then a·B²·L ≤ a_d
        have hB : ((base (Rv d.1) + base (Rv jd) * u) * Real.exp (-((kd : ℝ) * u))) ^ 2
            ≤ ((max (-(lo : ℝ)) (hi : ℝ))) ^ 2 := by
          have hml : -(max (-(lo : ℝ)) (hi : ℝ)) ≤ (lo : ℝ) := by
            have := le_max_left (-(lo : ℝ)) (hi : ℝ)
            linarith
          have h1 : -(max (-(lo : ℝ)) (hi : ℝ))
              ≤ (base (Rv d.1) + base (Rv jd) * u) * Real.exp (-((kd : ℝ) * u)) := by
            linarith [hband.1]
          have h2 : (base (Rv d.1) + base (Rv jd) * u) * Real.exp (-((kd : ℝ) * u))
              ≤ max (-(lo : ℝ)) (hi : ℝ) :=
            le_trans hband.2 (le_max_right _ _)
          exact sq_le_sq' h1 h2
        have hLpos : (0 : ℝ) < (dampers.length : ℝ) := by
          have : dampers.length ≠ 0 := by
            intro h0
            rw [List.length_eq_zero_iff] at h0
            subst h0
            exact absurd hd (List.not_mem_nil)
          exact_mod_cast Nat.pos_of_ne_zero this
        have hbdR : (d.2.1 : ℝ) * ((max (-(lo : ℝ)) (hi : ℝ))) ^ 2 * (dampers.length : ℝ)
            ≤ (d.2.2 : ℝ) := by exact_mod_cast hbd
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hadR hLpos]
        calc (d.2.1 : ℝ)
              * ((base (Rv d.1) + base (Rv jd) * u) * Real.exp (-((kd : ℝ) * u))) ^ 2
              * (dampers.length : ℝ)
            ≤ (d.2.1 : ℝ) * ((max (-(lo : ℝ)) (hi : ℝ))) ^ 2 * (dampers.length : ℝ) := by
              have := mul_le_mul_of_nonneg_left hB hanR
              nlinarith [hLpos]
          _ ≤ (d.2.2 : ℝ) := hbdR
          _ = 1 * (d.2.2 : ℝ) := by ring
    -- so the sum sits in [0, 1]
    have hsum0 : 0 ≤ (dampers.map (fun d =>
        ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1) + chaseDrv m base d * u) ^ 2
          * Real.exp (-(2 * chaseGain m d * u)))).sum := by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
      exact (hterm d hd).1
    have hsum1 : (dampers.map (fun d =>
        ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1) + chaseDrv m base d * u) ^ 2
          * Real.exp (-(2 * chaseGain m d * u)))).sum ≤ 1 := by
      by_cases hnil : dampers = []
      · subst hnil; simp
      · have hLpos : (0 : ℝ) < (dampers.length : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero
            (fun h0 => hnil (List.length_eq_zero_iff.mp h0))
        calc (dampers.map (fun d =>
              ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1) + chaseDrv m base d * u) ^ 2
                * Real.exp (-(2 * chaseGain m d * u)))).sum
            ≤ (dampers.map (fun d =>
                ((d.2.1 : ℝ) / (d.2.2 : ℝ)) * (base (Rv d.1) + chaseDrv m base d * u) ^ 2
                  * Real.exp (-(2 * chaseGain m d * u)))).length
                • (1 / (dampers.length : ℝ)) := by
              apply List.sum_le_card_nsmul
              intro x hx
              obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
              exact (hterm d hd).2
          _ = (dampers.length : ℝ) * (1 / (dampers.length : ℝ)) := by
              rw [List.length_map, nsmul_eq_mul]
          _ = 1 := by field_simp
    constructor
    · nlinarith
    · nlinarith
  -- the position's band: [s₀, s₀ + ghi·t], by monotonicity from the bounds
  have hbandS : ∀ t, 0 ≤ t →
      base (Rv sb.sc) ≤ terrainValDC m sb.sc (k : ℝ) (c : ℝ) base dampers t sb.sc
      ∧ terrainValDC m sb.sc (k : ℝ) (c : ℝ) base dampers t sb.sc
          ≤ base (Rv sb.sc) + (m.ghi : ℝ) * t := by
    intro t ht
    have hF0 : dampValC m (k : ℝ) (c : ℝ) base dampers 0 = 0 := by
      unfold dampValC
      simp [expInt]
    have hmono : MonotoneOn (fun w => dampValC m (k : ℝ) (c : ℝ) base dampers w)
        (Icc 0 t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
      · exact fun u _ => ((hF' u).continuousAt).continuousWithinAt
      · intro u _
        exact ((hF' u).differentiableAt).differentiableWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        rw [(hF' u).deriv]
        exact (hF'bounds u (le_of_lt hu.1)).1
    have hmono2 : MonotoneOn
        (fun w => (m.ghi : ℝ) * w - dampValC m (k : ℝ) (c : ℝ) base dampers w)
        (Icc 0 t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
      · intro u _
        exact (((hasDerivAt_id u).const_mul (m.ghi : ℝ)).sub
          (hF' u)).continuousAt.continuousWithinAt
      · intro u _
        have h1 : HasDerivAt (fun w : ℝ => (m.ghi : ℝ) * w) (m.ghi : ℝ) u := by
          simpa using (hasDerivAt_id u).const_mul (m.ghi : ℝ)
        exact ((h1.sub (hF' u)).differentiableAt).differentiableWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        have h1 : HasDerivAt (fun w : ℝ => (m.ghi : ℝ) * w) (m.ghi : ℝ) u := by
          simpa using (hasDerivAt_id u).const_mul (m.ghi : ℝ)
        have hd : HasDerivAt
            (fun w => (m.ghi : ℝ) * w - dampValC m (k : ℝ) (c : ℝ) base dampers w)
            ((m.ghi : ℝ) - (((c : ℝ) + (base (Rv m.gcoord) - (c : ℝ))
                * Real.exp (-((k : ℝ) * u)))
              * (1 - ((dampers.map (fun d =>
                  ((d.2.1 : ℝ) / (d.2.2 : ℝ))
                    * (base (Rv d.1) + chaseDrv m base d * u) ^ 2
                    * Real.exp (-(2 * chaseGain m d * u)))).sum)))) u := h1.sub (hF' u)
        rw [hd.deriv]
        have := (hF'bounds u (le_of_lt hu.1)).2
        linarith
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_refl _, ht⟩
    have htmem : t ∈ Icc (0 : ℝ) t := ⟨ht, le_refl _⟩
    have hlow := hmono h0mem htmem ht
    have hhigh := hmono2 h0mem htmem ht
    simp only [] at hlow hhigh
    rw [hF0] at hlow hhigh
    rw [terrainValDC_s]
    simp only [mul_zero, sub_zero, zero_sub, neg_nonpos] at hlow hhigh
    constructor
    · linarith
    · have : (m.ghi : ℝ) * t - dampValC m (k : ℝ) (c : ℝ) base dampers t ≥ 0 := by
        simpa using hhigh
      linarith
  -- a contract other stays in the hull of its base and its equilibrium
  have hbandO : ∀ (i : Fin n) (k' c' : ℤ), i ≠ m.gcoord → i ≠ sb.sc → 0 ≤ k' →
      m.shapes i = CoordShape.contract k' c' → ∀ t, 0 ≤ t →
      min (base (Rv i)) (c' : ℝ) ≤ terrainValDC m sb.sc (k : ℝ) (c : ℝ) base dampers t i
      ∧ terrainValDC m sb.sc (k : ℝ) (c : ℝ) base dampers t i
          ≤ max (base (Rv i)) (c' : ℝ) := by
    intro i k' c' hig his hk' hshi t ht
    have hk'R : (0 : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hk'
    have hθpos : 0 < Real.exp (-((k' : ℝ) * t)) := Real.exp_pos _
    have hθle : Real.exp (-((k' : ℝ) * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    rw [terrainValDC_contract hig his hshi]
    rcases le_total (base (Rv i)) (c' : ℝ) with hbc' | hbc'
    · rw [min_eq_left hbc', max_eq_right hbc']
      constructor
      · nlinarith
      · nlinarith
    · rw [min_eq_right hbc', max_eq_left hbc']
      constructor
      · nlinarith
      · nlinarith
  -- staying in the envelope
  have hstayEnv : ∀ t, 0 ≤ t →
      Formula.sat T.core.envF (terrainΦDC m sb.sc (k : ℝ) (c : ℝ) base dampers t) := by
    intro t ht
    rw [sat_envF]
    intro i
    rw [terrainΦDC_Rv]
    by_cases hig : i = m.gcoord
    · rw [hig]
      obtain ⟨h1, h2⟩ := hbandV t ht
      have hbe := (sat_envF.mp henv) m.gcoord
      unfold Band.memR at hbe ⊢
      rcases hbe with ⟨hbl, hbh⟩
      constructor
      · cases hcase : (T.core.env m.gcoord).lo with
        | none => trivial
        | some l =>
            have hlG : (l : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hvLo l hcase
            linarith
      · cases hcase : (T.core.env m.gcoord).hi with
        | none => trivial
        | some h =>
            have hgh : (m.ghi : ℝ) ≤ (h : ℝ) := by exact_mod_cast hvHi h hcase
            linarith
    · by_cases his : i = sb.sc
      · rw [his]
        obtain ⟨h1, h2⟩ := hbandS t ht
        unfold Band.memR
        constructor
        · cases hcase : (T.core.env sb.sc).lo with
          | none => trivial
          | some l =>
              have hlG : (l : ℝ) ≤ (sb.slo : ℝ) := by exact_mod_cast hsloIn l hcase
              linarith
        · rw [hsHiNone]; trivial
      · rcases hOth i hig his with hfz | ⟨k', c', hshi, hk', hloO, hhiO⟩ | hchase
        · rw [terrainValDC_frozen hig his hfz]
          exact (sat_envF.mp henv) i
        · obtain ⟨h1, h2⟩ := hbandO i k' c' hig his hk' hshi t ht
          have hbe := (sat_envF.mp henv) i
          unfold Band.memR at hbe ⊢
          rcases hbe with ⟨hbl, hbh⟩
          constructor
          · cases hcase : (T.core.env i).lo with
            | none => trivial
            | some l =>
                rw [hcase] at hbl
                have hlc : (l : ℝ) ≤ (c' : ℝ) := by exact_mod_cast hloO l hcase
                have hmin : (l : ℝ) ≤ min (base (Rv i)) (c' : ℝ) := le_min hbl hlc
                linarith
          · cases hcase : (T.core.env i).hi with
            | none => trivial
            | some h =>
                rw [hcase] at hbh
                have hhc : (c' : ℝ) ≤ (h : ℝ) := by exact_mod_cast hhiO h hcase
                have hmax : max (base (Rv i)) (c' : ℝ) ≤ (h : ℝ) := max_le hbh hhc
                linarith
        · obtain ⟨j2, k2, loi, hii, loj, hij, hshi, hj2g, hj2s, hj2c, hk2, hloi, hhii,
            hloj, hhij, hloi0, hhii0, hijle, hlojge⟩ := hchase
          have hbi := (sat_envF.mp henv) i
          have hbj := (sat_envF.mp henv) j2
          unfold Band.memR at hbi hbj ⊢
          rw [hloi, hhii] at hbi ⊢
          rw [hloj, hhij] at hbj
          obtain ⟨hbl, hbh⟩ := hbi
          obtain ⟨hbjl, hbjh⟩ := hbj
          have hband := chase_band (kR := (k : ℝ)) (cR := (c : ℝ)) hig his hshi hk2
            hloi0 hhii0 hijle hlojge hbl hbh hbjl hbjh ht
          rw [← terrainValDC_ne (dampers := dampers) his] at hband
          exact hband
  -- landing: the own box below `shi`, the declared successor above
  have hpick : ∃ q2 ∈ q :: T.core.graph.retainedSucc q,
      Formula.sat (T.GdOf q2)
        (terrainΦDC m sb.sc (k : ℝ) (c : ℝ) base dampers (T.core.dt : ℝ)) := by
    obtain ⟨hv1, hv2⟩ := hbandV (T.core.dt : ℝ) hdt
    obtain ⟨hs1, hs2⟩ := hbandS (T.core.dt : ℝ) hdt
    have hself_v : (m.glo : ℝ)
        ≤ terrainValDC m sb.sc (k : ℝ) (c : ℝ) base dampers (T.core.dt : ℝ) m.gcoord
        ∧ terrainValDC m sb.sc (k : ℝ) (c : ℝ) base dampers (T.core.dt : ℝ) m.gcoord
          ≤ (m.ghi : ℝ) := ⟨hv1, hv2⟩
    cases hshi : sb.shi with
    | none =>
        refine ⟨q, List.mem_cons_self .., ?_⟩
        rw [sat_GdOfT hq hsb]
        refine ⟨⟨hstayEnv _ hdt, by rw [terrainΦDC_Rv]; exact hself_v.1,
          by rw [terrainΦDC_Rv]; exact hself_v.2⟩,
          by rw [terrainΦDC_Rv]; linarith, ?_⟩
        intro sh' hsh'
        rw [hshi] at hsh'
        exact absurd hsh' (by simp)
    | some sh =>
        obtain ⟨q', hq'mem, m', sb', hm', hsb', hsc', hgc', hglo', hghi', hslo', hshi'⟩ :=
          hland sh hshi
        have hbs_sh : base (Rv sb.sc) ≤ (sh : ℝ) := hbshi sh hshi
        rcases le_or_gt
          (terrainValDC m sb.sc (k : ℝ) (c : ℝ) base dampers (T.core.dt : ℝ) sb.sc)
          ((sh : ℝ)) with he | he
        · -- self
          refine ⟨q, List.mem_cons_self .., ?_⟩
          rw [sat_GdOfT hq hsb]
          refine ⟨⟨hstayEnv _ hdt, by rw [terrainΦDC_Rv]; exact hself_v.1,
            by rw [terrainΦDC_Rv]; exact hself_v.2⟩,
            by rw [terrainΦDC_Rv]; linarith, ?_⟩
          intro sh' hsh'
          rw [hshi] at hsh'
          cases hsh'
          rw [terrainΦDC_Rv]
          exact he
        · -- successor
          have hglo'R : (m'.glo : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hglo'
          have hghi'R : (m.ghi : ℝ) ≤ (m'.ghi : ℝ) := by exact_mod_cast hghi'
          have hslo'R : (sb'.slo : ℝ) ≤ (sh : ℝ) := by exact_mod_cast hslo'
          refine ⟨q', List.mem_cons_of_mem _ (succ_mem_retained T.core hq hq'mem), ?_⟩
          rw [sat_GdOfT hm' hsb']
          refine ⟨⟨hstayEnv _ hdt, ?_, ?_⟩, ?_, ?_⟩
          · rw [hgc', terrainΦDC_Rv]; linarith
          · rw [hgc', terrainΦDC_Rv]; linarith
          · rw [hsc', terrainΦDC_Rv]; linarith
          · intro sh' hsh'
            have hcov : (sh : ℝ) + (m.ghi : ℝ) * (T.core.dt : ℝ) ≤ (sh' : ℝ) := by
              exact_mod_cast hshi' sh' hsh'
            rw [hsc', terrainΦDC_Rv]
            linarith
  obtain ⟨q2, hq2ret, hq2sat⟩ := hpick
  refine ⟨terrainΦDC m sb.sc (k : ℝ) (c : ℝ) base dampers, ?_, ?_, ?_,
    fun t ht => hstayEnv t ht.1, q2, hq2ret, hq2sat⟩
  · -- t = 0 recovers the base
    funext x
    obtain ⟨sd, ix⟩ := x
    cases sd with
    | R =>
        show terrainValDC m sb.sc (k : ℝ) (c : ℝ) base dampers 0 ix = base (Rv ix)
        by_cases his : ix = sb.sc
        · rw [his, terrainValDC_s]
          have h0 : dampValC m (k : ℝ) (c : ℝ) base dampers 0 = 0 := by
            unfold dampValC
            simp [expInt]
          rw [h0, add_zero]
        · rw [terrainValDC_ne his]
          unfold terrainVal
          by_cases hig : ix = m.gcoord
          · rw [if_pos hig]; subst hig; simp
          · rw [if_neg hig, if_neg his]
            rcases hshx : m.shapes ix with _ | _ | _ | _ | _ | _ <;> simp
    | L => rfl
    | Aux => rfl
  · -- derivatives
    intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hig : i = m.gcoord
    · rw [hig]
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf m.gcoord))
          (terrainΦDC m sb.sc (k : ℝ) (c : ℝ) base dampers t)
          = (k : ℝ)
            * ((c : ℝ) - terrainValDC m sb.sc (k : ℝ) (c : ℝ) base dampers t m.gcoord) := by
        simp [SettlingMode.fieldOf, hsh, CoordShape.field, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => terrainΦDC m sb.sc (k : ℝ) (c : ℝ) base dampers u (Rv m.gcoord))
          = fun u => (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)) := by
        funext u; rw [terrainΦDC_Rv, terrainValDC_g hsc]
      rw [hcurve]
      have hexp := expNeg_hasDeriv (k : ℝ) t
      have h1 : HasDerivAt
          (fun u => (c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * u)))
          ((base (Rv m.gcoord) - (c : ℝ)) * (-(k : ℝ) * Real.exp (-((k : ℝ) * t)))) t :=
        (hexp.const_mul (base (Rv m.gcoord) - (c : ℝ))).const_add (c : ℝ)
      have heq : (base (Rv m.gcoord) - (c : ℝ)) * (-(k : ℝ) * Real.exp (-((k : ℝ) * t)))
          = (k : ℝ)
            * ((c : ℝ) - terrainValDC m sb.sc (k : ℝ) (c : ℝ) base dampers t m.gcoord) := by
        rw [terrainValDC_g hsc]; ring
      rw [← heq]
      exact h1.hasDerivWithinAt
    · by_cases his : i = sb.sc
      · rw [his]
        -- the field eval at the witness: v(t) times the damping factor at the damper values
        have hdampval : ∀ d ∈ dampers,
            terrainValDC m sb.sc (k : ℝ) (c : ℝ) base dampers t d.1
              = (base (Rv d.1) + chaseDrv m base d * t)
                  * Real.exp (-(chaseGain m d * t)) := by
          intro d hd
          obtain ⟨hdg, hds, -, -, jd, kd, hkp, -, -⟩ := hdamp d hd
          rw [terrainValDC_chase hdg hds hkp]
          unfold chaseGain chaseDrv
          rw [hkp]
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf sb.sc))
            (terrainΦDC m sb.sc (k : ℝ) (c : ℝ) base dampers t)
            = (((c : ℝ) + (base (Rv m.gcoord) - (c : ℝ)) * Real.exp (-((k : ℝ) * t)))
              * (1 - ((dampers.map (fun d =>
                  ((d.2.1 : ℝ) / (d.2.2 : ℝ))
                    * (base (Rv d.1) + chaseDrv m base d * t) ^ 2
                    * Real.exp (-(2 * chaseGain m d * t)))).sum))) := by
          have hbase := eval_drivenDamp_field hscd
            (terrainΦDC m sb.sc (k : ℝ) (c : ℝ) base dampers t)
          have h1eval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf sb.sc))
              (terrainΦDC m sb.sc (k : ℝ) (c : ℝ) base dampers t)
              = Term.eval (m.fieldOf sb.sc)
                  (terrainΦDC m sb.sc (k : ℝ) (c : ℝ) base dampers t) := by
            simp [Term.eval, AOp.interp]
          rw [h1eval, hbase]
          rw [terrainΦDC_Rv, terrainValDC_g hsc]
          congr 2
          refine congrArg List.sum (List.map_congr_left ?_)
          intro d hd
          rw [terrainΦDC_Rv, hdampval d hd]
          have hsq : ((base (Rv d.1) + chaseDrv m base d * t)
                * Real.exp (-(chaseGain m d * t))) ^ 2
              = (base (Rv d.1) + chaseDrv m base d * t) ^ 2
                * Real.exp (-(2 * chaseGain m d * t)) := by
            rw [mul_pow]
            congr 1
            rw [show (-(2 * chaseGain m d * t)) = ((2 : ℕ) : ℝ) * (-(chaseGain m d * t)) by
              push_cast; ring, Real.exp_nat_mul]
          rw [hsq]
          ring
        rw [heval]
        have hcurve : (fun u => terrainΦDC m sb.sc (k : ℝ) (c : ℝ) base dampers u (Rv sb.sc))
            = fun u => base (Rv sb.sc) + dampValC m (k : ℝ) (c : ℝ) base dampers u := by
          funext u
          rw [terrainΦDC_Rv, terrainValDC_s]
        rw [hcurve]
        exact ((hF' t).const_add (base (Rv sb.sc))).hasDerivWithinAt
      · rcases hOth i hig his with hfz | ⟨k', c', hshi, -, -, -⟩ | hchase
        · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
              (terrainΦDC m sb.sc (k : ℝ) (c : ℝ) base dampers t) = 0 := by
            simp [SettlingMode.fieldOf, hfz, CoordShape.field, Term.eval, AOp.interp]
          rw [heval]
          have hcurve : (fun u => terrainΦDC m sb.sc (k : ℝ) (c : ℝ) base dampers u (Rv i))
              = fun _ => base (Rv i) := by
            funext u; rw [terrainΦDC_Rv, terrainValDC_frozen hig his hfz]
          rw [hcurve]
          exact hasDerivWithinAt_const t _ _
        · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
              (terrainΦDC m sb.sc (k : ℝ) (c : ℝ) base dampers t)
              = (k' : ℝ)
                * ((c' : ℝ) - terrainValDC m sb.sc (k : ℝ) (c : ℝ) base dampers t i) := by
            simp [SettlingMode.fieldOf, hshi, CoordShape.field, Term.eval, AOp.interp]
          rw [heval]
          have hcurve : (fun u => terrainΦDC m sb.sc (k : ℝ) (c : ℝ) base dampers u (Rv i))
              = fun u => (c' : ℝ) + (base (Rv i) - (c' : ℝ)) * Real.exp (-((k' : ℝ) * u)) := by
            funext u; rw [terrainΦDC_Rv, terrainValDC_contract hig his hshi]
          rw [hcurve]
          have hexp := expNeg_hasDeriv (k' : ℝ) t
          have h1 : HasDerivAt
              (fun u => (c' : ℝ) + (base (Rv i) - (c' : ℝ)) * Real.exp (-((k' : ℝ) * u)))
              ((base (Rv i) - (c' : ℝ)) * (-(k' : ℝ) * Real.exp (-((k' : ℝ) * t)))) t :=
            (hexp.const_mul (base (Rv i) - (c' : ℝ))).const_add (c' : ℝ)
          have heq : (base (Rv i) - (c' : ℝ)) * (-(k' : ℝ) * Real.exp (-((k' : ℝ) * t)))
              = (k' : ℝ)
                * ((c' : ℝ) - terrainValDC m sb.sc (k : ℝ) (c : ℝ) base dampers t i) := by
            rw [terrainValDC_contract hig his hshi]; ring
          rw [← heq]
          exact h1.hasDerivWithinAt
        · obtain ⟨j2, k2, loi, hii, loj, hij, hshi, hj2g, hj2s, hj2c, hk2, -, -, -, -,
            -, -, -, -⟩ := hchase
          have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
              (terrainΦDC m sb.sc (k : ℝ) (c : ℝ) base dampers t)
              = terrainValDC m sb.sc (k : ℝ) (c : ℝ) base dampers t j2
                - (k2 : ℝ) * terrainValDC m sb.sc (k : ℝ) (c : ℝ) base dampers t i := by
            simp [SettlingMode.fieldOf, hshi, CoordShape.field, Term.eval, AOp.interp]
          rw [heval]
          have hcurve : (fun u => terrainΦDC m sb.sc (k : ℝ) (c : ℝ) base dampers u (Rv i))
              = fun u => (base (Rv i) + base (Rv j2) * u) * Real.exp (-((k2 : ℝ) * u)) := by
            funext u; rw [terrainΦDC_Rv, terrainValDC_chase hig his hshi]
          rw [hcurve]
          have hlin : HasDerivAt (fun u : ℝ => base (Rv i) + base (Rv j2) * u)
              (base (Rv j2)) t := by
            simpa using ((hasDerivAt_id t).const_mul (base (Rv j2))).const_add (base (Rv i))
          have hexp := expNeg_hasDeriv (k2 : ℝ) t
          have h1 := hlin.mul hexp
          have heq : base (Rv j2) * Real.exp (-((k2 : ℝ) * t))
              + (base (Rv i) + base (Rv j2) * t) * (-(k2 : ℝ) * Real.exp (-((k2 : ℝ) * t)))
              = terrainValDC m sb.sc (k : ℝ) (c : ℝ) base dampers t j2
                - (k2 : ℝ) * terrainValDC m sb.sc (k : ℝ) (c : ℝ) base dampers t i := by
            rw [terrainValDC_chase hig his hshi, terrainValDC_contract hj2g hj2s hj2c]
            push_cast
            ring
          rw [← heq]
          exact h1.hasDerivWithinAt
  · -- mask
    intro t ht x hx
    refine terrainΦDC_nonR m sb.sc (k : ℝ) (c : ℝ) base dampers t ?_
    intro i hxi
    exact hx (by
      rw [hxi]
      simp only [rightBlock, ODESystem.bound, List.map_map]
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

/-! ### Extraction: the checker's Bool facts as Props -/

theorem checkModeT_true {M : SettlingModel n} {sbands : List (SBand n)}
    {m : SettlingMode n} {sb : SBand n}
    (h : checkModeT M sbands m sb = true) :
    ∃ k c, m.shapes m.gcoord = CoordShape.contract k c ∧ 0 ≤ k ∧
      m.glo ≤ c ∧ c ≤ m.ghi ∧ 0 ≤ m.glo ∧
      (∀ l', (M.env m.gcoord).lo = some l' → l' ≤ m.glo) ∧
      (∀ h', (M.env m.gcoord).hi = some h' → m.ghi ≤ h') ∧
      sb.sc ≠ m.gcoord ∧
      (m.shapes sb.sc = CoordShape.driven m.gcoord ∨
       (∃ dampers, m.shapes sb.sc = CoordShape.drivenDamp m.gcoord dampers ∧
         ∀ d ∈ dampers, d.1 ≠ m.gcoord ∧ d.1 ≠ sb.sc ∧ 0 ≤ d.2.1 ∧ 0 < d.2.2 ∧
           (∃ kp, m.shapes d.1 = CoordShape.contract kp 0 ∧ 0 ≤ kp) ∧
           (∃ lo hi, (M.env d.1).lo = some lo ∧ (M.env d.1).hi = some hi ∧
             lo ≤ 0 ∧ 0 ≤ hi ∧
             d.2.1 * (max (-lo) hi)^2 * (dampers.length : ℤ) ≤ d.2.2)) ∨
       (∃ dampers, m.shapes sb.sc = CoordShape.drivenDamp m.gcoord dampers ∧
         ∀ d ∈ dampers, d.1 ≠ m.gcoord ∧ d.1 ≠ sb.sc ∧ 0 ≤ d.2.1 ∧ 0 < d.2.2 ∧
           ∃ jd kd, m.shapes d.1 = CoordShape.chase jd kd ∧ 0 < kd ∧
             ∃ lo hi loj hij, (M.env d.1).lo = some lo ∧ (M.env d.1).hi = some hi ∧
               (M.env jd).lo = some loj ∧ (M.env jd).hi = some hij ∧
               lo ≤ 0 ∧ 0 ≤ hi ∧ hij ≤ kd * hi ∧ kd * lo ≤ loj ∧
               d.2.1 * (max (-lo) hi) ^ 2 * (dampers.length : ℤ) ≤ d.2.2)) ∧
      (∀ l', (M.env sb.sc).lo = some l' → l' ≤ sb.slo) ∧
      (M.env sb.sc).hi = none ∧
      (∀ i, i ≠ m.gcoord → i ≠ sb.sc →
        m.shapes i = CoordShape.frozen ∨
        (∃ k' c', m.shapes i = CoordShape.contract k' c' ∧ 0 ≤ k' ∧
          (∀ l', (M.env i).lo = some l' → l' ≤ c') ∧
          (∀ h', (M.env i).hi = some h' → c' ≤ h')) ∨
        (∃ j2 k2 loi hii loj hij, m.shapes i = CoordShape.chase j2 k2 ∧
          j2 ≠ m.gcoord ∧ j2 ≠ sb.sc ∧ m.shapes j2 = CoordShape.contract k2 0 ∧ 0 < k2 ∧
          (M.env i).lo = some loi ∧ (M.env i).hi = some hii ∧
          (M.env j2).lo = some loj ∧ (M.env j2).hi = some hij ∧
          loi ≤ 0 ∧ 0 ≤ hii ∧ hij ≤ k2 * hii ∧ k2 * loi ≤ loj)) ∧
      (∀ q' ∈ m.succs, q' < M.modes.length) ∧
      (∀ sh, sb.shi = some sh →
        ∃ q' ∈ m.succs, ∃ m' sb', M.modes[q']? = some m' ∧ sbands[q']? = some sb' ∧
          sb'.sc = sb.sc ∧ m'.gcoord = m.gcoord ∧ m'.glo ≤ m.glo ∧ m.ghi ≤ m'.ghi ∧
          sb'.slo ≤ sh ∧ (∀ sh', sb'.shi = some sh' → sh + m.ghi * M.dt ≤ sh')) := by
  unfold checkModeT at h
  rcases hsh : m.shapes m.gcoord with _ | _ | ⟨k, c⟩ | _ | _ | _ | _ | _ | _
  all_goals rw [hsh] at h
  · simp at h
  · simp at h
  · refine ⟨k, c, rfl, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, hcl⟩, hch⟩, hglo0⟩, -⟩, hinside⟩, hscne⟩, hscd⟩, hsloB⟩, hsHiB⟩,
      hothB⟩, hsuccB⟩, hlandB⟩ := h
    have hvLo : ∀ l', (M.env m.gcoord).lo = some l' → l' ≤ m.glo := by
      intro l' hl'
      unfold bandInside at hinside
      rw [Bool.and_eq_true] at hinside
      have := hinside.1
      rw [hl'] at this
      simpa using this
    have hvHi : ∀ h', (M.env m.gcoord).hi = some h' → m.ghi ≤ h' := by
      intro h' hh'
      unfold bandInside at hinside
      rw [Bool.and_eq_true] at hinside
      have := hinside.2
      rw [hh'] at this
      simpa using this
    have hsloIn : ∀ l', (M.env sb.sc).lo = some l' → l' ≤ sb.slo := by
      intro l' hl'
      rw [hl'] at hsloB
      simpa using hsloB
    have hOth : ∀ i, i ≠ m.gcoord → i ≠ sb.sc →
        m.shapes i = CoordShape.frozen ∨
        (∃ k' c', m.shapes i = CoordShape.contract k' c' ∧ 0 ≤ k' ∧
          (∀ l', (M.env i).lo = some l' → l' ≤ c') ∧
          (∀ h', (M.env i).hi = some h' → c' ≤ h')) ∨
        (∃ j2 k2 loi hii loj hij, m.shapes i = CoordShape.chase j2 k2 ∧
          j2 ≠ m.gcoord ∧ j2 ≠ sb.sc ∧ m.shapes j2 = CoordShape.contract k2 0 ∧ 0 < k2 ∧
          (M.env i).lo = some loi ∧ (M.env i).hi = some hii ∧
          (M.env j2).lo = some loj ∧ (M.env j2).hi = some hij ∧
          loi ≤ 0 ∧ 0 ≤ hii ∧ hij ≤ k2 * hii ∧ k2 * loi ≤ loj) := by
      intro i hig his
      have := hothB i (List.mem_finRange i)
      simp only [Bool.or_eq_true, decide_eq_true_eq] at this
      rcases this with ((h1 | h2) | h3) | h4
      · exact absurd h1 hig
      · exact absurd h2 his
      · exact Or.inl h3
      · rcases hshx : m.shapes i with _ | _ | ⟨k', c'⟩ | _ | _ | _ | _ | _ | ⟨j2, k2⟩
        all_goals rw [hshx] at h4
        · simp at h4
        · simp at h4
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at h4
          refine Or.inr (Or.inl ⟨k', c', rfl, h4.1.1, ?_, ?_⟩)
          · intro l' hl'
            have := h4.1.2
            rw [hl'] at this
            simpa using this
          · intro h' hh'
            have := h4.2
            rw [hh'] at this
            simpa using this
        · simp at h4
        · simp at h4
        · simp at h4
        · simp at h4
        · simp at h4
        · -- chase: decode the cascade-angle conditions
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
            decide_eq_true_eq] at h4
          obtain ⟨⟨⟨⟨hj2g, hj2s⟩, hj2c⟩, hk2⟩, henvm⟩ := h4
          rcases hloi : (M.env i).lo with _ | loi <;>
            rcases hhii : (M.env i).hi with _ | hii <;>
            rcases hloj : (M.env j2).lo with _ | loj <;>
            rcases hhij : (M.env j2).hi with _ | hij <;>
            rw [hloi, hhii, hloj, hhij] at henvm <;>
            simp at henvm
          refine Or.inr (Or.inr ⟨j2, k2, loi, hii, loj, hij, rfl, hj2g, hj2s, hj2c, hk2,
            rfl, rfl, hloj, hhij, ?_, ?_, ?_, ?_⟩) <;> tauto
    have hscP : m.shapes sb.sc = CoordShape.driven m.gcoord ∨
        (∃ dampers, m.shapes sb.sc = CoordShape.drivenDamp m.gcoord dampers ∧
          ∀ d ∈ dampers, d.1 ≠ m.gcoord ∧ d.1 ≠ sb.sc ∧ 0 ≤ d.2.1 ∧ 0 < d.2.2 ∧
            (∃ kp, m.shapes d.1 = CoordShape.contract kp 0 ∧ 0 ≤ kp) ∧
            (∃ lo hi, (M.env d.1).lo = some lo ∧ (M.env d.1).hi = some hi ∧
              lo ≤ 0 ∧ 0 ≤ hi ∧
              d.2.1 * (max (-lo) hi)^2 * (dampers.length : ℤ) ≤ d.2.2)) ∨
        (∃ dampers, m.shapes sb.sc = CoordShape.drivenDamp m.gcoord dampers ∧
          ∀ d ∈ dampers, d.1 ≠ m.gcoord ∧ d.1 ≠ sb.sc ∧ 0 ≤ d.2.1 ∧ 0 < d.2.2 ∧
            ∃ jd kd, m.shapes d.1 = CoordShape.chase jd kd ∧ 0 < kd ∧
              ∃ lo hi loj hij, (M.env d.1).lo = some lo ∧ (M.env d.1).hi = some hi ∧
                (M.env jd).lo = some loj ∧ (M.env jd).hi = some hij ∧
                lo ≤ 0 ∧ 0 ≤ hi ∧ hij ≤ kd * hi ∧ kd * lo ≤ loj ∧
                d.2.1 * (max (-lo) hi) ^ 2 * (dampers.length : ℤ) ≤ d.2.2) := by
      rw [Bool.or_eq_true] at hscd
      rcases hscd with h1 | h2
      · exact Or.inl (of_decide_eq_true h1)
      · rcases hs : m.shapes sb.sc with _ | _ | _ | _ | _ | ⟨j, dampers⟩ | _ | _ | _
        all_goals rw [hs] at h2
        · simp at h2
        · simp at h2
        · simp at h2
        · simp at h2
        · simp at h2
        · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
            List.all_eq_true] at h2
          obtain ⟨hj, hor⟩ := h2
          subst hj
          rcases hor with hall | hall
          · refine Or.inr (Or.inl ⟨dampers, rfl, ?_⟩)
            intro d hd
            have hthis := hall d hd
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
              decide_eq_false_iff_not] at hthis
            obtain ⟨⟨⟨⟨⟨hd1, hd2⟩, hd3⟩, hd4⟩, hshp⟩, henvd⟩ := hthis
            refine ⟨hd1, hd2, hd3, hd4, ?_, ?_⟩
            · rcases hsp : m.shapes d.1 with _ | _ | ⟨kp, cp⟩ | _ | _ | _ | _ | _ | _
              all_goals rw [hsp] at hshp
              · simp at hshp
              · simp at hshp
              · simp only [Bool.and_eq_true, decide_eq_true_eq] at hshp
                refine ⟨kp, ?_, hshp.1⟩
                rw [hshp.2]
              · simp at hshp
              · simp at hshp
              · simp at hshp
              · simp at hshp
              · simp at hshp
              · simp at hshp
            · rcases hlo : (M.env d.1).lo with _ | lo <;>
                rcases hhi : (M.env d.1).hi with _ | hi
              all_goals rw [hlo, hhi] at henvd
              · simp at henvd
              · simp at henvd
              · simp at henvd
              · simp only [Bool.and_eq_true, decide_eq_true_eq] at henvd
                exact ⟨lo, hi, rfl, rfl, henvd.1.1, henvd.1.2, henvd.2⟩
          · -- cascade dampers (EXT 4c)
            refine Or.inr (Or.inr ⟨dampers, rfl, ?_⟩)
            intro d hd
            have hthis := hall d hd
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
              decide_eq_false_iff_not] at hthis
            obtain ⟨⟨⟨⟨hd1, hd2⟩, hd3⟩, hd4⟩, hshp⟩ := hthis
            refine ⟨hd1, hd2, hd3, hd4, ?_⟩
            rcases hsp : m.shapes d.1 with _ | _ | _ | _ | _ | _ | _ | _ | ⟨jd, kd⟩
            all_goals rw [hsp] at hshp
            · simp at hshp
            · simp at hshp
            · simp at hshp
            · simp at hshp
            · simp at hshp
            · simp at hshp
            · simp at hshp
            · simp at hshp
            · rw [Bool.and_eq_true] at hshp
              obtain ⟨hkd, henvm⟩ := hshp
              refine ⟨jd, kd, rfl, of_decide_eq_true hkd, ?_⟩
              rcases hlo : (M.env d.1).lo with _ | lo <;>
                rcases hhi : (M.env d.1).hi with _ | hi <;>
                rcases hloj : (M.env jd).lo with _ | loj <;>
                rcases hhij : (M.env jd).hi with _ | hij <;>
                rw [hlo, hhi, hloj, hhij] at henvm <;>
                simp at henvm
              refine ⟨lo, hi, loj, hij, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> tauto
        · simp at h2
        · simp at h2
        · simp at h2
    refine ⟨hk, hcl, hch, hglo0, hvLo, hvHi, hscne, hscP, hsloIn, hsHiB, hOth, hsuccB, ?_⟩
    intro sh hshi
    rw [hshi] at hlandB
    rw [List.any_eq_true] at hlandB
    obtain ⟨q', hq'mem, hq'⟩ := hlandB
    rcases hm' : M.modes[q']? with _ | m' <;> rcases hsb' : sbands[q']? with _ | sb'
    all_goals rw [hm', hsb'] at hq'
    · simp at hq'
    · simp at hq'
    · simp at hq'
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
      obtain ⟨⟨⟨⟨⟨hsc', hgc'⟩, hglo'⟩, hghi'⟩, hslo'⟩, hshi'B⟩ := hq'
      refine ⟨q', hq'mem, m', sb', hm', hsb', hsc', hgc', hglo', hghi', hslo', ?_⟩
      intro sh' hsh'
      rw [hsh'] at hshi'B
      simpa using hshi'B
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h

/-! ### The assembly: `wellformed_sound_terrain` -/

/-- The terrain analog of `WellFormedSound`: checker + freshness + per-run certificates ⟹
the settling hypothesis with the terrain guard map. -/
def WellFormedSoundT (T : TerrainModel n) (mv tg : Var n) (g : Term (Var n))
    (fL : Fin n → Term (Var n)) : Prop :=
  decideWellFormedT T = true →
  (0 : ℝ) ≤ (T.core.dt : ℝ) →
  mv ∉ g.fv → mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound → mv ≠ tg →
  (∀ q', mv ∉ (T.GdOf q').fv) → (∀ q', tg ∉ (T.GdOf q').fv) →
  (∀ q', ∀ x ∈ (T.GdOf q').fv, x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound) →
  GuardSettlingH T.core.graph T.GdOf mv g (Term.const 1) tg (T.core.dt : ℝ) fL T.core.envF

/-- **The terrain checker is sound** — the EXT 3 reduction theorem. -/
theorem wellformed_sound_terrain (T : TerrainModel n) (mv tg : Var n) (g : Term (Var n))
    (fL : Fin n → Term (Var n)) : WellFormedSoundT T mv tg g fL := by
  intro hwf hdt hg hmvclk hmvtg hmvGd htgGd hfrzGd
  unfold decideWellFormedT at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hwf
  obtain ⟨⟨-, -⟩, hall⟩ := hwf
  have hcheck : ∀ (q : ℕ) (m : SettlingMode n), T.core.modes[q]? = some m →
      ∃ sb, T.sbands[q]? = some sb ∧ checkModeT T.core T.sbands m sb = true := by
    intro q m hqm
    have hqlt : q < T.core.modes.length := (List.getElem?_eq_some_iff.mp hqm).1
    have := hall q (List.mem_range.mpr hqlt)
    rw [hqm] at this
    rcases hsb : T.sbands[q]? with _ | sb
    · rw [hsb] at this; simp at this
    · rw [hsb] at this; exact ⟨sb, rfl, this⟩
  refine ⟨hdt, hg, hmvclk, hmvtg, hmvGd, htgGd, hfrzGd, ?_⟩
  intro q m' hm'
  rw [graph_modeAt] at hm'
  obtain ⟨SM, hSM, rfl⟩ := Option.map_eq_some_iff.mp hm'
  obtain ⟨sb, hsb, hchk⟩ := hcheck q SM hSM
  obtain ⟨k, c, hsh, hk, hcl, hch, hglo0, hvLo, hvHi, hscne, hscd, hsloIn, hsHiNone, hOth,
    hsucclen, hland⟩ := checkModeT_true hchk
  have hqlt : q < T.core.modes.length := (List.getElem?_eq_some_iff.mp hSM).1
  have hlen : T.core.graph.modes.length = T.core.modes.length := by
    unfold SettlingModel.graph; simp
  have hmodeAt : T.core.graph.modeAt q = some (SM.toRMode T.core) := by
    rw [graph_modeAt, hSM]; rfl
  refine ⟨SM.fieldOf, rfl, rfl, by rw [hlen]; exact hqlt, ?_, ?_, ?_, ?_⟩
  · rcases hscd with hplain | ⟨dampers, hscdD, hdamp⟩ | ⟨dampers, hscdD, hdamp⟩
    · exact settling_terrain T hSM hsb hsh hk hcl hch hglo0 hvLo hvHi hscne hplain hsloIn
        hsHiNone hOth hland hdt
    · exact settling_terrain_damp T hSM hsb hsh hk hcl hch hglo0 hvLo hvHi hscne hscdD hdamp
        hsloIn hsHiNone hOth hland hdt
    · exact settling_terrain_dampC T hSM hsb hsh hk hcl hch hglo0 hvLo hvHi hscne hscdD hdamp
        hsloIn hsHiNone hOth hland hdt
  · exact ⟨_, self_edge_mem T.core hSM, rfl, rfl⟩
  · exact retainedSucc_edges T.core hSM hsucclen
  · intro q' _ hq'
    exact graph_modeAll T.core q' hq'

end RelCertifier
