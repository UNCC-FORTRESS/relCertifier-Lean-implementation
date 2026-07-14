/-
# EXT 3 — the terrain checker: box guards over a driven position coordinate

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
import RelCertifier.WellFormedChecker

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
      decide (0 ≤ k) && decide (m.ghi = c) && decide (0 ≤ m.glo) &&
      decide (m.glo ≤ m.ghi) && bandInside m.glo m.ghi (M.env m.gcoord) &&
      !decide (sb.sc = m.gcoord) &&
      decide (m.shapes sb.sc = CoordShape.driven m.gcoord) &&
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
         | _ => false)) &&
      m.succs.all (fun q' => decide (q' < M.modes.length)) &&
      (match sb.shi with
       | none => true
       | some sh =>
           m.succs.any fun q' =>
             match M.modes[q']?, sbands[q']? with
             | some m', some sb' =>
                 decide (sb'.sc = sb.sc) && decide (m'.gcoord = m.gcoord) &&
                 decide (m'.glo ≤ m.glo) && decide (c ≤ m'.ghi) &&
                 decide (sb'.slo ≤ sh) &&
                 (match sb'.shi with
                  | none => true
                  | some sh' => decide (sh + c * dt ≤ sh'))
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

/-! ## The per-mode discharge -/

/-- TERRAIN mode: contract `v` (cap at the equilibrium), integrated `s` over the terrain
segment, decaying/frozen others — stays, and lands in the own box or the declared successor
segment, by an endpoint case-split at `shi`. -/
theorem settling_terrain (T : TerrainModel n) {q : ℕ} {m : SettlingMode n} {sb : SBand n}
    (hq : T.core.modes[q]? = some m) (hsb : T.sbands[q]? = some sb) {k c : ℤ}
    (hsh : m.shapes m.gcoord = CoordShape.contract k c)
    (hk : 0 ≤ k) (hcap : m.ghi = c) (hglo0 : 0 ≤ m.glo)
    (hvHi : ∀ h', (T.core.env m.gcoord).hi = some h' → m.ghi ≤ h')
    (hsc : sb.sc ≠ m.gcoord)
    (hscd : m.shapes sb.sc = CoordShape.driven m.gcoord)
    (hsloIn : ∀ l', (T.core.env sb.sc).lo = some l' → l' ≤ sb.slo)
    (hsHiNone : (T.core.env sb.sc).hi = none)
    (hOth : ∀ i, i ≠ m.gcoord → i ≠ sb.sc →
        m.shapes i = CoordShape.frozen ∨
        ∃ k' c', m.shapes i = CoordShape.contract k' c' ∧ 0 ≤ k' ∧
          (∀ l', (T.core.env i).lo = some l' → l' ≤ c') ∧
          (∀ h', (T.core.env i).hi = some h' → c' ≤ h'))
    (hland : ∀ sh, sb.shi = some sh →
        ∃ q' ∈ m.succs, ∃ m' sb', T.core.modes[q']? = some m' ∧ T.sbands[q']? = some sb' ∧
          sb'.sc = sb.sc ∧ m'.gcoord = m.gcoord ∧ m'.glo ≤ m.glo ∧ c ≤ m'.ghi ∧
          sb'.slo ≤ sh ∧ (∀ sh', sb'.shi = some sh' → sh + c * T.core.dt ≤ sh'))
    (hdt : (0 : ℝ) ≤ (T.core.dt : ℝ)) :
    GuardSettlingB T.core.graph T.GdOf m.fieldOf (Term.const 1) T.core.envF
      ((T.core.dt : ℝ)) q := by
  intro base hb
  obtain ⟨⟨henv, hblo, hbhi⟩, hbslo, hbshi⟩ := (sat_GdOfT hq hsb).mp hb
  have hkR0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hglo0R : (0 : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hglo0
  have hcapR : (m.ghi : ℝ) = (c : ℝ) := by exact_mod_cast hcap
  have hbc : base (Rv m.gcoord) ≤ (c : ℝ) := hcapR ▸ hbhi
  have hbv0 : (0 : ℝ) ≤ base (Rv m.gcoord) := le_trans hglo0R hblo
  -- the active value's band: [v₀, c] for all t ≥ 0
  have hbandV : ∀ t, 0 ≤ t →
      base (Rv m.gcoord) ≤ terrainVal m sb.sc (k : ℝ) (c : ℝ) base t m.gcoord
      ∧ terrainVal m sb.sc (k : ℝ) (c : ℝ) base t m.gcoord ≤ (c : ℝ) := by
    intro t ht
    have hθpos : 0 < Real.exp (-((k : ℝ) * t)) := Real.exp_pos _
    have hθle : Real.exp (-((k : ℝ) * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    rw [terrainVal_g]
    constructor
    · nlinarith
    · nlinarith
  -- the position's band: [s₀, s₀ + c·t] for all t ≥ 0
  have hbandS : ∀ t, 0 ≤ t →
      base (Rv sb.sc) ≤ terrainVal m sb.sc (k : ℝ) (c : ℝ) base t sb.sc
      ∧ terrainVal m sb.sc (k : ℝ) (c : ℝ) base t sb.sc
          ≤ base (Rv sb.sc) + (c : ℝ) * t := by
    intro t ht
    have hEI0 : 0 ≤ expInt (k : ℝ) t := expInt_nonneg hkR0 ht
    have hEIt : expInt (k : ℝ) t ≤ t := expInt_le hkR0 ht
    rw [terrainVal_s hsc]
    constructor
    · -- c·t + (v₀ − c)·expInt ≥ c·t + (v₀ − c)·t = v₀·t ≥ 0
      nlinarith
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
            rw [hcase] at hbl
            exact le_trans hbl h1
      · cases hcase : (T.core.env m.gcoord).hi with
        | none => trivial
        | some h =>
            have hgh : (m.ghi : ℝ) ≤ (h : ℝ) := by exact_mod_cast hvHi h hcase
            calc terrainVal m sb.sc (k : ℝ) (c : ℝ) base t m.gcoord ≤ (c : ℝ) := h2
              _ = (m.ghi : ℝ) := hcapR.symm
              _ ≤ (h : ℝ) := hgh
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
      · rcases hOth i hig his with hfz | ⟨k', c', hshi, hk', hloO, hhiO⟩
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
  -- landing: the own box below `shi`, the declared successor above
  have hpick : ∃ q2 ∈ q :: T.core.graph.retainedSucc q,
      Formula.sat (T.GdOf q2) (terrainΦ m sb.sc (k : ℝ) (c : ℝ) base (T.core.dt : ℝ)) := by
    obtain ⟨hv1, hv2⟩ := hbandV (T.core.dt : ℝ) hdt
    obtain ⟨hs1, hs2⟩ := hbandS (T.core.dt : ℝ) hdt
    have hself_v : (m.glo : ℝ) ≤ terrainVal m sb.sc (k : ℝ) (c : ℝ) base (T.core.dt : ℝ)
        m.gcoord ∧ terrainVal m sb.sc (k : ℝ) (c : ℝ) base (T.core.dt : ℝ) m.gcoord
          ≤ (m.ghi : ℝ) := ⟨le_trans hblo hv1, hcapR ▸ hv2⟩
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
          have hghi'R : (c : ℝ) ≤ (m'.ghi : ℝ) := by exact_mod_cast hghi'
          have hslo'R : (sb'.slo : ℝ) ≤ (sh : ℝ) := by exact_mod_cast hslo'
          refine ⟨q', List.mem_cons_of_mem _ (succ_mem_retained T.core hq hq'mem), ?_⟩
          rw [sat_GdOfT hm' hsb']
          refine ⟨⟨hstayEnv _ hdt, ?_, ?_⟩, ?_, ?_⟩
          · rw [hgc', terrainΦ_Rv]; linarith
          · rw [hgc', terrainΦ_Rv]; linarith
          · rw [hsc', terrainΦ_Rv]; linarith
          · intro sh' hsh'
            have hcov : (sh : ℝ) + (c : ℝ) * (T.core.dt : ℝ) ≤ (sh' : ℝ) := by
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
      · rcases hOth i hig his with hfz | ⟨k', c', hshi, -, -, -⟩
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
  · -- mask
    intro t ht x hx
    refine terrainΦ_nonR m sb.sc (k : ℝ) (c : ℝ) base t ?_
    intro i hxi
    exact hx (by
      rw [hxi]
      simp only [rightBlock, ODESystem.bound, List.map_map]
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

/-! ### Extraction: the checker's Bool facts as Props -/

theorem checkModeT_true {M : SettlingModel n} {sbands : List (SBand n)}
    {m : SettlingMode n} {sb : SBand n}
    (h : checkModeT M sbands m sb = true) :
    ∃ k c, m.shapes m.gcoord = CoordShape.contract k c ∧ 0 ≤ k ∧ m.ghi = c ∧ 0 ≤ m.glo ∧
      (∀ h', (M.env m.gcoord).hi = some h' → m.ghi ≤ h') ∧
      sb.sc ≠ m.gcoord ∧ m.shapes sb.sc = CoordShape.driven m.gcoord ∧
      (∀ l', (M.env sb.sc).lo = some l' → l' ≤ sb.slo) ∧
      (M.env sb.sc).hi = none ∧
      (∀ i, i ≠ m.gcoord → i ≠ sb.sc →
        m.shapes i = CoordShape.frozen ∨
        ∃ k' c', m.shapes i = CoordShape.contract k' c' ∧ 0 ≤ k' ∧
          (∀ l', (M.env i).lo = some l' → l' ≤ c') ∧
          (∀ h', (M.env i).hi = some h' → c' ≤ h')) ∧
      (∀ q' ∈ m.succs, q' < M.modes.length) ∧
      (∀ sh, sb.shi = some sh →
        ∃ q' ∈ m.succs, ∃ m' sb', M.modes[q']? = some m' ∧ sbands[q']? = some sb' ∧
          sb'.sc = sb.sc ∧ m'.gcoord = m.gcoord ∧ m'.glo ≤ m.glo ∧ c ≤ m'.ghi ∧
          sb'.slo ≤ sh ∧ (∀ sh', sb'.shi = some sh' → sh + c * M.dt ≤ sh')) := by
  unfold checkModeT at h
  rcases hsh : m.shapes m.gcoord with _ | _ | ⟨k, c⟩ | _ | _
  all_goals rw [hsh] at h
  · simp at h
  · simp at h
  · refine ⟨k, c, rfl, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, hcap⟩, hglo0⟩, -⟩, hinside⟩, hscne⟩, hscd⟩, hsloB⟩, hsHiB⟩,
      hothB⟩, hsuccB⟩, hlandB⟩ := h
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
        ∃ k' c', m.shapes i = CoordShape.contract k' c' ∧ 0 ≤ k' ∧
          (∀ l', (M.env i).lo = some l' → l' ≤ c') ∧
          (∀ h', (M.env i).hi = some h' → c' ≤ h') := by
      intro i hig his
      have := hothB i (List.mem_finRange i)
      simp only [Bool.or_eq_true, decide_eq_true_eq] at this
      rcases this with ((h1 | h2) | h3) | h4
      · exact absurd h1 hig
      · exact absurd h2 his
      · exact Or.inl h3
      · rcases hshx : m.shapes i with _ | _ | ⟨k', c'⟩ | _ | _
        all_goals rw [hshx] at h4
        · simp at h4
        · simp at h4
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at h4
          refine Or.inr ⟨k', c', rfl, h4.1.1, ?_, ?_⟩
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
    refine ⟨hk, hcap, hglo0, hvHi, hscne, hscd, hsloIn, hsHiB, hOth, hsuccB, ?_⟩
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
  (∀ q m, T.core.graph.modeAt q = some m → ∀ ν, Formula.sat (T.GdOf q) ν →
      BoxLe (Program.ode m.sys T.core.envF) (fun ω => Term.eval g ω) ν) →
  GuardSettlingH T.core.graph T.GdOf mv g (Term.const 1) tg (T.core.dt : ℝ) fL T.core.envF

/-- **The terrain checker is sound** — the EXT 3 reduction theorem. -/
theorem wellformed_sound_terrain (T : TerrainModel n) (mv tg : Var n) (g : Term (Var n))
    (fL : Fin n → Term (Var n)) : WellFormedSoundT T mv tg g fL := by
  intro hwf hdt hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert
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
  obtain ⟨k, c, hsh, hk, hcap, hglo0, hvHi, hscne, hscd, hsloIn, hsHiNone, hOth,
    hsucclen, hland⟩ := checkModeT_true hchk
  have hqlt : q < T.core.modes.length := (List.getElem?_eq_some_iff.mp hSM).1
  have hlen : T.core.graph.modes.length = T.core.modes.length := by
    unfold SettlingModel.graph; simp
  have hmodeAt : T.core.graph.modeAt q = some (SM.toRMode T.core) := by
    rw [graph_modeAt, hSM]; rfl
  refine ⟨SM.fieldOf, rfl, rfl, by rw [hlen]; exact hqlt, ?_, ?_, ?_, ?_, ?_⟩
  · exact settling_terrain T hSM hsb hsh hk hcap hglo0 hvHi hscne hscd hsloIn hsHiNone
      hOth hland hdt
  · intro ν hν
    exact hcert q (SM.toRMode T.core) hmodeAt ν hν
  · exact ⟨_, self_edge_mem T.core hSM, rfl, rfl⟩
  · exact retainedSucc_edges T.core hSM hsucclen
  · intro q' _ hq'
    exact graph_modeAll T.core q' hq'

end RelCertifier
