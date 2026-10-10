/-
# EXT 2b — the affine checker: a driven-active velocity under a frozen acceleration

**Status.** Part of the settling / `Faithful` route (per-benchmark settling, terrain and
affine models of the legacy suite, kernel-certified against the parsed IR). Its
per-benchmark batteries (`SettlingInstances`, `TerrainInstances`, `AffineInstances`,
`FaithfulCerts`, `RealInstances`) were retired with the legacy suite (git history); the
suite_v2 theorems use the modal chain instead. The generic definitions and lemmas stay
compiled as part of the soundness development.

The driven-active class (`rover_tier_r1`, `rover3tier_rung12`): the guarded velocity
satisfies `v' = a` with `a` FROZEN and nonneg (its envelope floor `alo ≥ 0`), so the witness
is the phase-B quadratic stack with the affine rate `a₀ = base(a)` — `drivenVal` with
`cR := base (Rv j)`, no new witness function at all. The guard bands are `[glo, ∞)` or
`[glo, gh]` with an OPTIONAL top (the terminal-band fix left the last band unbounded), which
`SettlingMode`'s integer `ghi` cannot carry — so, as with the terrain checker, an
`AffineModel` WRAPS a `SettlingModel` and adds the per-mode optional tops; the graph and
envelope stack are reused verbatim and `GuardSettlingH`'s guard-map parameter absorbs the
new guard shape.

THE GEOMETRY. `v(t) = v₀ + a₀·t` is nondecreasing (`a₀ ≥ alo ≥ 0`), so
* staying needs only `env.lo ≤ glo ≤ v₀ ≤ v(t)` and NO upper envelope wall (`env.hi = none`
  — nothing in the dynamics bounds `v` above: the honest-envelope discipline);
* a driven integrator (`s' = v`) grows quadratically and needs no upper wall either;
* landing is an endpoint case-split at the optional top: no top → the own band; top `gh` →
  at or below lands home, above lands in a declared successor whose band starts at or below
  `gh` and has NO top — so no rate arithmetic enters the checker at all.

TRUST: definitions + decidable functions; no `native_decide`; axioms-clean.
-/
import RelCertifier.Checker.WellFormedChecker

namespace RelCertifier
open DL Function Set

variable {n : ℕ}

/-! ## The affine model: a settling core plus per-mode optional band tops -/

/-- An affine model: the settling core plus, per mode, the optional v-band top (`none` = the
unbounded terminal band). The core mode's `ghi` is unused by this guard map. -/
structure AffineModel (n : ℕ) where
  core  : SettlingModel n
  vtops : List (Option ℤ)

/-- The affine guard map: envelope ∧ `glo ≤ v` ∧ the optional top. -/
noncomputable def AffineModel.GdOf (A : AffineModel n) : ℕ → Formula (Var n) :=
  fun q => match A.core.modes[q]?, A.vtops[q]? with
    | some m, some top =>
        Formula.and A.core.envF (Formula.and
          (Formula.cmp CompOp.le (Term.const (m.glo : ℝ)) (Term.var (Rv m.gcoord)))
          (match top with
           | some gh => Formula.cmp CompOp.le (Term.var (Rv m.gcoord)) (Term.const (gh : ℝ))
           | none => Formula.tt))
    | _, _ => Formula.tt

/-- **Reflection**: affine guard satisfaction. -/
theorem sat_GdOfA {A : AffineModel n} {q : ℕ} {m : SettlingMode n} {top : Option ℤ}
    (hq : A.core.modes[q]? = some m) (htop : A.vtops[q]? = some top) {μ : State (Var n)} :
    Formula.sat (A.GdOf q) μ ↔
      Formula.sat A.core.envF μ ∧ (m.glo : ℝ) ≤ μ (Rv m.gcoord)
      ∧ (∀ gh, top = some gh → μ (Rv m.gcoord) ≤ (gh : ℝ)) := by
  unfold AffineModel.GdOf
  rw [hq, htop]
  cases htp : top with
  | none => simp [Formula.sat, CompOp.interp, Term.eval]
  | some gh =>
      simp only [Formula.sat, CompOp.interp, Term.eval]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, fun gh' hgh' => by cases hgh'; exact h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, h3 gh rfl⟩

/-! ## The checker (computable, ℤ arithmetic) -/

/-- One affine mode's check. -/
def checkModeA (M : SettlingModel n) (vtops : List (Option ℤ)) (m : SettlingMode n)
    (top : Option ℤ) : Bool :=
  match m.shapes m.gcoord with
  | CoordShape.driven j =>
      !decide (j = m.gcoord) &&
      decide (m.shapes j = CoordShape.frozen) &&
      -- the acceleration is nonneg on its envelope floor
      (match (M.env j).lo with
       | some alo => decide (0 ≤ alo)
       | none => false) &&
      decide (0 ≤ m.glo) &&
      ((M.env m.gcoord).lo.all fun lo => decide (lo ≤ m.glo)) &&
      decide ((M.env m.gcoord).hi = none) &&
      -- others: frozen, or integrators of the active coordinate with no upper wall
      ((List.finRange n).all fun i =>
        decide (i = m.gcoord) || decide (m.shapes i = CoordShape.frozen) ||
        (decide (m.shapes i = CoordShape.driven m.gcoord) &&
          decide ((M.env i).hi = none))) &&
      m.succs.all (fun q' => decide (q' < M.modes.length)) &&
      -- landing: no top → self; top gh → a declared topless successor starting at or below gh
      (match top with
       | none => true
       | some gh =>
           decide (m.glo ≤ gh) &&
           (m.succs.any fun q' =>
             match M.modes[q']?, vtops[q']? with
             | some m', some none =>
                 decide (m'.gcoord = m.gcoord) && decide (m'.glo ≤ gh)
             | _, _ => false))
  | _ => false

/-- **The affine well-formedness checker.** Decidable; no Z3, no ODE reasoning. -/
def decideWellFormedA (A : AffineModel n) : Bool :=
  decide (0 ≤ A.core.dtQ) &&
  ((List.finRange n).all fun i => bandOrdered (A.core.env i)) &&
  (List.range A.core.modes.length).all (fun q =>
    match A.core.modes[q]?, A.vtops[q]? with
    | some m, some top => checkModeA A.core A.vtops m top
    | _, _ => false)

/-! ## The per-mode discharge -/

/-- AFFINE mode: `v' = a₀ ≥ 0` frozen, integrators quadratic — the phase-B witness with the
base-dependent rate; stays (no upper walls), lands by an endpoint case-split at the optional
band top. -/
theorem settling_affine (A : AffineModel n) {q : ℕ} {m : SettlingMode n} {top : Option ℤ}
    (hq : A.core.modes[q]? = some m) (htop : A.vtops[q]? = some top) {j : Fin n}
    (hsh : m.shapes m.gcoord = CoordShape.driven j)
    (hjne : j ≠ m.gcoord)
    (hjfz : m.shapes j = CoordShape.frozen)
    (halo : ∃ alo, (A.core.env j).lo = some alo ∧ 0 ≤ alo)
    (hglo0 : 0 ≤ m.glo)
    (hvLo : ∀ l', (A.core.env m.gcoord).lo = some l' → l' ≤ m.glo)
    (hvHi : (A.core.env m.gcoord).hi = none)
    (hOth : ∀ i, i ≠ m.gcoord →
        m.shapes i = CoordShape.frozen ∨
        (m.shapes i = CoordShape.driven m.gcoord ∧ (A.core.env i).hi = none))
    (hland : ∀ gh, top = some gh → m.glo ≤ gh ∧
        ∃ q' ∈ m.succs, ∃ m', A.core.modes[q']? = some m' ∧ A.vtops[q']? = some none ∧
          m'.gcoord = m.gcoord ∧ m'.glo ≤ gh)
    (hdt : (0 : ℝ) ≤ (A.core.dt : ℝ)) :
    GuardSettlingB A.core.graph A.GdOf m.fieldOf (Term.const 1) A.core.envF
      ((A.core.dt : ℝ)) q := by
  intro base hb
  obtain ⟨henv, hblo, hbtop⟩ := (sat_GdOfA hq htop).mp hb
  obtain ⟨alo, halo', halo0⟩ := halo
  have hglo0R : (0 : ℝ) ≤ (m.glo : ℝ) := by exact_mod_cast hglo0
  -- the frozen acceleration is nonneg (its envelope floor bounds the base)
  have ha0 : (0 : ℝ) ≤ base (Rv j) := by
    have hbe := (sat_envF.mp henv) j
    unfold Band.memR at hbe
    rw [halo'] at hbe
    have haloR : (0 : ℝ) ≤ (alo : ℝ) := by exact_mod_cast halo0
    linarith [hbe.1]
  have hbv0 : (0 : ℝ) ≤ base (Rv m.gcoord) := le_trans hglo0R hblo
  -- the active value is nondecreasing from the base
  have hbandV : ∀ t, 0 ≤ t →
      base (Rv m.gcoord) ≤ drivenVal m (base (Rv j)) base t m.gcoord := by
    intro t ht
    have : drivenVal m (base (Rv j)) base t m.gcoord
        = base (Rv m.gcoord) + base (Rv j) * t := by
      simp [drivenVal]
    rw [this]
    nlinarith
  -- staying in the envelope (no upper walls anywhere the flow moves)
  have hstayEnv : ∀ t, 0 ≤ t →
      Formula.sat A.core.envF (drivenΦ m (base (Rv j)) base t) := by
    intro t ht
    rw [sat_envF]
    intro i
    rw [drivenΦ_Rv]
    by_cases hig : i = m.gcoord
    · rw [hig]
      have h1 := hbandV t ht
      have hbe := (sat_envF.mp henv) m.gcoord
      unfold Band.memR at hbe ⊢
      rcases hbe with ⟨hbl, -⟩
      constructor
      · cases hcase : (A.core.env m.gcoord).lo with
        | none => trivial
        | some l =>
            rw [hcase] at hbl
            linarith
      · rw [hvHi]; trivial
    · rcases hOth i hig with hfz | ⟨hdr, hhi⟩
      · rw [drivenVal_frozen hig hfz]
        exact (sat_envF.mp henv) i
      · rw [drivenVal_dactive hig hdr]
        have hbe := (sat_envF.mp henv) i
        unfold Band.memR at hbe ⊢
        rcases hbe with ⟨hbl, -⟩
        constructor
        · cases hcase : (A.core.env i).lo with
          | none => trivial
          | some l =>
              rw [hcase] at hbl
              show (l : ℝ) ≤ base (Rv i) + base (Rv m.gcoord) * t + base (Rv j) / 2 * t ^ 2
              nlinarith
        · rw [hhi]; trivial
  -- landing: the own band, or the declared topless successor above the top
  have hpick : ∃ q2 ∈ q :: A.core.graph.retainedSucc q,
      Formula.sat (A.GdOf q2) (drivenΦ m (base (Rv j)) base (A.core.dt : ℝ)) := by
    have hv1 := hbandV (A.core.dt : ℝ) hdt
    cases htp : top with
    | none =>
        refine ⟨q, List.mem_cons_self .., ?_⟩
        rw [sat_GdOfA hq htop]
        refine ⟨hstayEnv _ hdt, by rw [drivenΦ_Rv]; linarith, ?_⟩
        intro gh hgh
        rw [htp] at hgh
        exact absurd hgh (by simp)
    | some gh =>
        obtain ⟨hglogh, q', hq'mem, m', hm', htop', hgc', hglo'⟩ := hland gh htp
        rcases le_or_gt (drivenVal m (base (Rv j)) base (A.core.dt : ℝ) m.gcoord)
          ((gh : ℝ)) with he | he
        · refine ⟨q, List.mem_cons_self .., ?_⟩
          rw [sat_GdOfA hq htop]
          refine ⟨hstayEnv _ hdt, by rw [drivenΦ_Rv]; linarith, ?_⟩
          intro gh' hgh'
          rw [htp] at hgh'
          cases hgh'
          rw [drivenΦ_Rv]
          exact he
        · have hglo'R : (m'.glo : ℝ) ≤ (gh : ℝ) := by exact_mod_cast hglo'
          refine ⟨q', List.mem_cons_of_mem _ (succ_mem_retained A.core hq hq'mem), ?_⟩
          rw [sat_GdOfA hm' htop']
          refine ⟨hstayEnv _ hdt, ?_, ?_⟩
          · rw [hgc', drivenΦ_Rv]
            linarith
          · intro gh' hgh'
            exact absurd hgh' (by simp)
  obtain ⟨q2, hq2ret, hq2sat⟩ := hpick
  refine ⟨drivenΦ m (base (Rv j)) base, ?_, ?_, ?_,
    fun t ht => hstayEnv t ht.1, q2, hq2ret, hq2sat⟩
  · -- t = 0 recovers the base
    funext x
    obtain ⟨sd, ix⟩ := x
    cases sd with
    | R =>
        show drivenVal m (base (Rv j)) base 0 ix = base (Rv ix)
        unfold drivenVal
        by_cases hig : ix = m.gcoord
        · rw [if_pos hig]; subst hig; simp
        · rw [if_neg hig]
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
          (drivenΦ m (base (Rv j)) base t) = base (Rv j) := by
        have hj : drivenΦ m (base (Rv j)) base t (Rv j) = base (Rv j) := by
          rw [drivenΦ_Rv, drivenVal_frozen hjne hjfz]
        simp only [SettlingMode.fieldOf, hsh, CoordShape.field, Term.eval, AOp.interp]
        rw [hj]; ring
      rw [heval]
      have hcurve : (fun u => drivenΦ m (base (Rv j)) base u (Rv m.gcoord))
          = fun u => base (Rv m.gcoord) + base (Rv j) * u := by
        funext u
        rw [drivenΦ_Rv]
        simp [drivenVal]
      rw [hcurve]
      have h := ((hasDerivAt_id t).const_mul (base (Rv j))).const_add (base (Rv m.gcoord))
      simp only [id, mul_one] at h
      exact h.hasDerivWithinAt
    · rcases hOth i hig with hfz | ⟨hdr, -⟩
      · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦ m (base (Rv j)) base t) = 0 := by
          simp [SettlingMode.fieldOf, hfz, CoordShape.field, Term.eval, AOp.interp]
        rw [heval]
        have hcurve : (fun u => drivenΦ m (base (Rv j)) base u (Rv i))
            = fun _ => base (Rv i) := by
          funext u; rw [drivenΦ_Rv, drivenVal_frozen hig hfz]
        rw [hcurve]
        exact hasDerivWithinAt_const t _ _
      · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (m.fieldOf i))
            (drivenΦ m (base (Rv j)) base t)
            = base (Rv m.gcoord) + base (Rv j) * t := by
          have hg : drivenΦ m (base (Rv j)) base t (Rv m.gcoord)
              = base (Rv m.gcoord) + base (Rv j) * t := by
            rw [drivenΦ_Rv]
            simp [drivenVal]
          simp only [SettlingMode.fieldOf, hdr, CoordShape.field, Term.eval, AOp.interp]
          rw [hg]; ring
        rw [heval]
        have hcurve : (fun u => drivenΦ m (base (Rv j)) base u (Rv i))
            = fun u => base (Rv i) + base (Rv m.gcoord) * u
                + base (Rv j) / 2 * u ^ 2 := by
          funext u; rw [drivenΦ_Rv, drivenVal_dactive hig hdr]
        rw [hcurve]
        have h1 : HasDerivAt (fun u : ℝ => base (Rv i) + base (Rv m.gcoord) * u)
            (base (Rv m.gcoord)) t := by
          have h := ((hasDerivAt_id t).const_mul (base (Rv m.gcoord))).const_add
            (base (Rv i))
          simpa using h
        have h2 : HasDerivAt (fun u : ℝ => base (Rv j) / 2 * u ^ 2)
            (base (Rv j) * t) t := by
          have h := (hasDerivAt_pow 2 t).const_mul (base (Rv j) / 2)
          have heq2 : base (Rv j) / 2 * ((2 : ℕ) * t ^ (2 - 1)) = base (Rv j) * t := by
            push_cast
            ring
          rw [heq2] at h
          exact h
        have h := h1.add h2
        exact h.hasDerivWithinAt
  · -- mask
    intro t ht x hx
    refine drivenΦ_nonR m (base (Rv j)) base t ?_
    intro i hxi
    exact hx (by
      rw [hxi]
      simp only [rightBlock, ODESystem.bound, List.map_map]
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

/-! ### Extraction -/

theorem checkModeA_true {M : SettlingModel n} {vtops : List (Option ℤ)}
    {m : SettlingMode n} {top : Option ℤ}
    (h : checkModeA M vtops m top = true) :
    ∃ j, m.shapes m.gcoord = CoordShape.driven j ∧ j ≠ m.gcoord ∧
      m.shapes j = CoordShape.frozen ∧
      (∃ alo, (M.env j).lo = some alo ∧ 0 ≤ alo) ∧
      0 ≤ m.glo ∧
      (∀ l', (M.env m.gcoord).lo = some l' → l' ≤ m.glo) ∧
      (M.env m.gcoord).hi = none ∧
      (∀ i, i ≠ m.gcoord →
        m.shapes i = CoordShape.frozen ∨
        (m.shapes i = CoordShape.driven m.gcoord ∧ (M.env i).hi = none)) ∧
      (∀ q' ∈ m.succs, q' < M.modes.length) ∧
      (∀ gh, top = some gh → m.glo ≤ gh ∧
        ∃ q' ∈ m.succs, ∃ m', M.modes[q']? = some m' ∧ vtops[q']? = some none ∧
          m'.gcoord = m.gcoord ∧ m'.glo ≤ gh) := by
  unfold checkModeA at h
  rcases hsh : m.shapes m.gcoord with _ | _ | _ | _ | j | _ | _ | _ | _
  all_goals rw [hsh] at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · refine ⟨j, rfl, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hjne, hjfz⟩, haloB⟩, hglo0⟩, hloB⟩, hhiB⟩, hothB⟩, hsuccB⟩, hlandB⟩ := h
    have halo : ∃ alo, (M.env j).lo = some alo ∧ 0 ≤ alo := by
      rcases hlo : (M.env j).lo with _ | alo
      · rw [hlo] at haloB; simp at haloB
      · rw [hlo] at haloB
        exact ⟨alo, rfl, by simpa using haloB⟩
    have hvLo : ∀ l', (M.env m.gcoord).lo = some l' → l' ≤ m.glo := by
      intro l' hl'
      rw [hl'] at hloB
      simpa using hloB
    have hOth : ∀ i, i ≠ m.gcoord →
        m.shapes i = CoordShape.frozen ∨
        (m.shapes i = CoordShape.driven m.gcoord ∧ (M.env i).hi = none) := by
      intro i hi
      have := hothB i (List.mem_finRange i)
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
      rcases this with (h1 | h2) | h3
      · exact absurd h1 hi
      · exact Or.inl h2
      · exact Or.inr h3
    refine ⟨hjne, hjfz, halo, hglo0, hvLo, hhiB, hOth, hsuccB, ?_⟩
    intro gh hgh
    rw [hgh] at hlandB
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hlandB
    obtain ⟨hglogh, hany⟩ := hlandB
    rw [List.any_eq_true] at hany
    obtain ⟨q', hq'mem, hq'⟩ := hany
    rcases hm' : M.modes[q']? with _ | m' <;> rcases htp' : vtops[q']? with _ | tp'
    all_goals rw [hm', htp'] at hq'
    · simp at hq'
    · simp at hq'
    · simp at hq'
    · rcases htpn : tp' with _ | gh2
      all_goals rw [htpn] at hq'
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
        exact ⟨hglogh, q', hq'mem, m', hm', htpn ▸ htp', hq'.1, hq'.2⟩
      · simp at hq'
  · simp at h
  · simp at h
  · simp at h
  · simp at h

/-! ### The assembly: `wellformed_sound_affine` -/

/-- The affine analog of `WellFormedSound`. -/
def WellFormedSoundA (A : AffineModel n) (mv tg : Var n) (g : Term (Var n))
    (fL : Fin n → Term (Var n)) : Prop :=
  decideWellFormedA A = true →
  (0 : ℝ) ≤ (A.core.dt : ℝ) →
  mv ∉ g.fv → mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound → mv ≠ tg →
  (∀ q', mv ∉ (A.GdOf q').fv) → (∀ q', tg ∉ (A.GdOf q').fv) →
  (∀ q', ∀ x ∈ (A.GdOf q').fv, x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound) →
  GuardSettlingH A.core.graph A.GdOf mv g (Term.const 1) tg (A.core.dt : ℝ) fL A.core.envF

/-- **The affine checker is sound** — the EXT 2b reduction theorem. -/
theorem wellformed_sound_affine (A : AffineModel n) (mv tg : Var n) (g : Term (Var n))
    (fL : Fin n → Term (Var n)) : WellFormedSoundA A mv tg g fL := by
  intro hwf hdt hg hmvclk hmvtg hmvGd htgGd hfrzGd
  unfold decideWellFormedA at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hwf
  obtain ⟨⟨-, -⟩, hall⟩ := hwf
  have hcheck : ∀ (q : ℕ) (m : SettlingMode n), A.core.modes[q]? = some m →
      ∃ top, A.vtops[q]? = some top ∧ checkModeA A.core A.vtops m top = true := by
    intro q m hqm
    have hqlt : q < A.core.modes.length := (List.getElem?_eq_some_iff.mp hqm).1
    have := hall q (List.mem_range.mpr hqlt)
    rw [hqm] at this
    rcases htp : A.vtops[q]? with _ | top
    · rw [htp] at this; simp at this
    · rw [htp] at this; exact ⟨top, rfl, this⟩
  refine ⟨hdt, hg, hmvclk, hmvtg, hmvGd, htgGd, hfrzGd, ?_⟩
  intro q m' hm'
  rw [graph_modeAt] at hm'
  obtain ⟨SM, hSM, rfl⟩ := Option.map_eq_some_iff.mp hm'
  obtain ⟨top, htop, hchk⟩ := hcheck q SM hSM
  obtain ⟨j, hsh, hjne, hjfz, halo, hglo0, hvLo, hvHi, hOth, hsucclen, hland⟩ :=
    checkModeA_true hchk
  have hqlt : q < A.core.modes.length := (List.getElem?_eq_some_iff.mp hSM).1
  have hlen : A.core.graph.modes.length = A.core.modes.length := by
    unfold SettlingModel.graph; simp
  have hmodeAt : A.core.graph.modeAt q = some (SM.toRMode A.core) := by
    rw [graph_modeAt, hSM]; rfl
  refine ⟨SM.fieldOf, rfl, rfl, by rw [hlen]; exact hqlt, ?_, ?_, ?_, ?_⟩
  · exact settling_affine A hSM htop hsh hjne hjfz halo hglo0 hvLo hvHi hOth hland hdt
  · exact ⟨_, self_edge_mem A.core hSM, rfl, rfl⟩
  · exact retainedSucc_edges A.core hSM hsucclen
  · intro q' _ hq'
    exact graph_modeAll A.core q' hq'

end RelCertifier
