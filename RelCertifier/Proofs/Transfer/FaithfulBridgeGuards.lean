/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The Faithful bridge, terrain and affine guard variants

`FaithfulBridge` assembled the settling family: fields (`realFieldOf` + the nine shape
bridges) and envelope (`realEnvOf`/`envFormulaR_sat`) are family-independent and reused
verbatim here. What changes per family is the GUARD MAP. The terrain/affine guard bands
are only partially pinned by the parsed guard (`bandTerrain`/`bandAffine` allow a design
band inside the envelope where the parsed guard is silent), so the real-side guard
constants are defined uniformly as the scaled model's integers divided by the coordinate
scale — `z/σ`. Where the parsed guard does speak, the kernel fidelity certificate
(`bandTerrain`/`sbandFaithful`/`bandAffine`) pins the parsed bound to the same real value,
so nothing is lost: the correspondence lemma becomes a pure division identity, needing no
per-benchmark band facts at all.
-/
import RelCertifier.Proofs.Transfer.FaithfulBridge
import RelCertifier.Checker.TerrainChecker
import RelCertifier.Checker.AffineChecker

namespace RelCertifier

open DL DLCalTiming DLRel Function Set

variable {n : ℕ}

/-! ## Scaled-band correspondence: the division identity -/

/-- The scaled-down constant: `z/σᵢ` as a `QF` value. -/
noncomputable def scaledConst (σq : List QF) (i : Fin n) (z : ℤ) : ℝ :=
  (qDiv (qOfInt z) (σq.getD i.val (qOfInt 0))).val

theorem scaledConst_mul {σq : List QF} {i : Fin n}
    (hσd : (σq.getD i.val (qOfInt 0)).pos) (hσv : 0 < sigmaOf σq i) (z : ℤ) :
    scaledConst σq i z * sigmaOf σq i = (z : ℝ) := by
  have hne : (σq.getD i.val (qOfInt 0)).val ≠ 0 := ne_of_gt (by exact hσv)
  unfold scaledConst sigmaOf
  rw [qDiv_val (qOfInt_pos z) hσd, qOfInt_val]
  field_simp

/-- Lower scaled band: `z/σ ≤ x` at the raw state ↔ `z ≤ σ·x` at the scaled state. -/
theorem scaledLo_sat {σq : List QF} (i : Fin n)
    (hσd : (σq.getD i.val (qOfInt 0)).pos) (hσv : 0 < sigmaOf σq i) (z : ℤ)
    (ν : DL.State (Var n)) :
    Formula.sat (Formula.cmp CompOp.le (Term.const (scaledConst σq i z))
        (Term.var (Rv i))) ν
      ↔ Formula.sat (Formula.cmp CompOp.le (Term.const (z : ℝ)) (Term.var (Rv i)))
          (scaleState (sigmaOf σq) ν) := by
  simp only [Formula.sat, CompOp.interp, Term.eval, scaleState_R]
  rw [← scaledConst_mul hσd hσv z]
  constructor
  · intro h
    exact mul_le_mul_of_nonneg_right h hσv.le |>.trans_eq (by ring)
  · intro h
    have := le_of_mul_le_mul_right (by
      calc scaledConst σq i z * sigmaOf σq i ≤ sigmaOf σq i * ν (Rv i) := h
        _ = ν (Rv i) * sigmaOf σq i := by ring) hσv
    exact this

/-- Upper scaled band: `x ≤ z/σ` ↔ `σ·x ≤ z`. -/
theorem scaledHi_sat {σq : List QF} (i : Fin n)
    (hσd : (σq.getD i.val (qOfInt 0)).pos) (hσv : 0 < sigmaOf σq i) (z : ℤ)
    (ν : DL.State (Var n)) :
    Formula.sat (Formula.cmp CompOp.le (Term.var (Rv i))
        (Term.const (scaledConst σq i z))) ν
      ↔ Formula.sat (Formula.cmp CompOp.le (Term.var (Rv i)) (Term.const (z : ℝ)))
          (scaleState (sigmaOf σq) ν) := by
  simp only [Formula.sat, CompOp.interp, Term.eval, scaleState_R]
  rw [← scaledConst_mul hσd hσv z]
  constructor
  · intro h
    calc sigmaOf σq i * ν (Rv i) = ν (Rv i) * sigmaOf σq i := by ring
      _ ≤ scaledConst σq i z * sigmaOf σq i := mul_le_mul_of_nonneg_right h hσv.le
  · intro h
    exact le_of_mul_le_mul_right (by
      calc ν (Rv i) * sigmaOf σq i = sigmaOf σq i * ν (Rv i) := by ring
        _ ≤ scaledConst σq i z * sigmaOf σq i := h) hσv

/-! ## The real-side guard maps -/

/-- Real-side terrain guard: parsed envelope ∧ scaled-down v-band ∧ scaled-down s-band. -/
noncomputable def realGdOfT (P : Parse.PProblem) (σq : List QF) (T : TerrainModel n) :
    ℕ → Formula (Var n) :=
  fun q => match P.R.modes[q]?, T.core.modes[q]?, T.sbands[q]? with
    | some pm, some m, some sb =>
        match boundsOfForm pm.evolve with
        | some eb =>
            Formula.and (envFormulaR P.R.stateVars n eb)
              (Formula.and
                (Formula.and
                  (Formula.cmp CompOp.le (Term.const (scaledConst σq m.gcoord m.glo))
                    (Term.var (Rv m.gcoord)))
                  (Formula.cmp CompOp.le (Term.var (Rv m.gcoord))
                    (Term.const (scaledConst σq m.gcoord m.ghi))))
                (Formula.and
                  (Formula.cmp CompOp.le (Term.const (scaledConst σq sb.sc sb.slo))
                    (Term.var (Rv sb.sc)))
                  (match sb.shi with
                   | some sh => Formula.cmp CompOp.le (Term.var (Rv sb.sc))
                       (Term.const (scaledConst σq sb.sc sh))
                   | none => Formula.tt)))
        | none => Formula.tt
    | _, _, _ => Formula.tt

/-- Real-side affine guard: parsed envelope ∧ scaled-down `glo ≤ v` ∧ optional top. -/
noncomputable def realGdOfA (P : Parse.PProblem) (σq : List QF) (A : AffineModel n) :
    ℕ → Formula (Var n) :=
  fun q => match P.R.modes[q]?, A.core.modes[q]?, A.vtops[q]? with
    | some pm, some m, some top =>
        match boundsOfForm pm.evolve with
        | some eb =>
            Formula.and (envFormulaR P.R.stateVars n eb)
              (Formula.and
                (Formula.cmp CompOp.le (Term.const (scaledConst σq m.gcoord m.glo))
                  (Term.var (Rv m.gcoord)))
                (match top with
                 | some gh => Formula.cmp CompOp.le (Term.var (Rv m.gcoord))
                     (Term.const (scaledConst σq m.gcoord gh))
                 | none => Formula.tt))
        | none => Formula.tt
    | _, _, _ => Formula.tt

/-! ## Frame extraction, generalized over the per-mode extra clause -/

theorem faithfulFrame_facts {P : Parse.PProblem} {mt : TransMeta}
    {M : SettlingModel n} {εR : QF}
    {extra : Nat → Parse.PMode → SettlingMode n → Bool}
    (hεR : parseQ P.R.epsilon = some εR)
    (hf : faithfulFrame P mt M extra = true) :
    mt.lam.n ≠ 0 ∧ M.dtQ ≠ 0
    ∧ P.R.stateVars.length ≤ n
    ∧ P.R.modes.length = M.modes.length
    ∧ ∀ q pm m, P.R.modes[q]? = some pm → M.modes[q]? = some m →
        modeCore P.R.stateVars mt.scales (qDiv (qDiv εR mt.lam) (qOfInt M.dtQ))
          (P.R.modes.map (·.name)) q pm m M.env = true
        ∧ extra q pm m = true := by
  unfold faithfulFrame at hf
  rw [hεR] at hf
  simp only [Bool.and_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨hlam, hdt⟩, hle⟩, hsc⟩, hml⟩, hall⟩ := hf
  refine ⟨by unfold qIsZero at hlam; simpa using hlam, by simpa using hdt,
    by simpa using hle,
    by first
      | exact of_decide_eq_true hml
      | exact Nat.eq_of_beq_eq_true hml
      | simpa using hml, ?_⟩
  intro q pm m hpm hm
  have hq : q < P.R.modes.length := by
    obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hpm
    exact h
  have hfact := List.all_eq_true.mp hall q (List.mem_range.mpr hq)
  rw [hpm, hm] at hfact
  simpa [Bool.and_eq_true] using hfact

/-! ## Guard-map correspondences -/

/-- **The terrain `hGd` discharger.** -/
theorem realGdOfT_sat (P : Parse.PProblem) (mt : TransMeta) (T : TerrainModel n)
    {εR : QF} (hεR : parseQ P.R.epsilon = some εR)
    (hf : faithfulTerrain P mt T = true)
    (hlen : P.R.stateVars.length = n)
    (hσd : ∀ j, j < n → (mt.scales.getD j (qOfInt 0)).pos)
    (hσv : ∀ j : Fin n, 0 < sigmaOf mt.scales j) :
    ∀ (q' : ℕ) (ν : DL.State (Var n)),
      Formula.sat (realGdOfT P mt.scales T q') ν
        ↔ Formula.sat (T.GdOf q') (scaleState (sigmaOf mt.scales) ν) := by
  unfold faithfulTerrain at hf
  simp only [Bool.and_eq_true] at hf
  obtain ⟨hsblen, hframe⟩ := hf
  obtain ⟨-, -, -, hml, hmode⟩ := faithfulFrame_facts hεR hframe
  have hsbl : T.sbands.length = T.core.modes.length := by
    simpa using hsblen
  intro q' ν
  rcases hpm : P.R.modes[q']? with _ | pm
  · have hmn : T.core.modes[q']? = none := by
      rw [List.getElem?_eq_none_iff] at hpm ⊢
      omega
    have hsn : T.sbands[q']? = none := by
      rw [List.getElem?_eq_none_iff]
      rw [List.getElem?_eq_none_iff] at hpm
      omega
    unfold realGdOfT TerrainModel.GdOf
    rw [hpm, hsn]
    simp [Formula.sat]
  rcases hm : T.core.modes[q']? with _ | m
  · exfalso
    rw [List.getElem?_eq_none_iff] at hm
    obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hpm
    omega
  rcases hsb : T.sbands[q']? with _ | sb
  · exfalso
    rw [List.getElem?_eq_none_iff] at hsb
    obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hpm
    omega
  obtain ⟨hmc, -⟩ := hmode q' pm m hpm hm
  obtain ⟨eb, heb, hef⟩ := modeCore_env_facts hlen hmc
  have henv := envFormulaR_sat T.core (boundsOfForm_pos heb) hσd hσv hef ν
  have hglo := scaledLo_sat m.gcoord (hσd m.gcoord.val m.gcoord.isLt) (hσv m.gcoord)
    m.glo ν
  have hghi := scaledHi_sat m.gcoord (hσd m.gcoord.val m.gcoord.isLt) (hσv m.gcoord)
    m.ghi ν
  have hslo := scaledLo_sat sb.sc (hσd sb.sc.val sb.sc.isLt) (hσv sb.sc) sb.slo ν
  have hcore : T.core.GdOf q'
      = Formula.and T.core.envF (bandDom m.gcoord (m.glo : ℝ) (m.ghi : ℝ)) := by
    unfold SettlingModel.GdOf
    rw [hm]
  unfold realGdOfT TerrainModel.GdOf
  simp only [hpm, hm, hsb, heb, hcore]
  cases hshi : sb.shi with
  | none =>
      simp only [hshi, Formula.sat, bandDom]
      constructor
      · rintro ⟨he, ⟨hg1, hg2⟩, hs1, -⟩
        exact ⟨⟨henv.mp he, hglo.mp hg1, hghi.mp hg2⟩,
          hslo.mp hs1, trivial⟩
      · rintro ⟨⟨he, hg1, hg2⟩, hs1, -⟩
        exact ⟨henv.mpr he, ⟨hglo.mpr hg1, hghi.mpr hg2⟩,
          hslo.mpr hs1, trivial⟩
  | some sh =>
      have hshi' := scaledHi_sat sb.sc (hσd sb.sc.val sb.sc.isLt) (hσv sb.sc) sh ν
      simp only [hshi, Formula.sat, bandDom]
      constructor
      · rintro ⟨he, ⟨hg1, hg2⟩, hs1, hs2⟩
        exact ⟨⟨henv.mp he, hglo.mp hg1, hghi.mp hg2⟩,
          hslo.mp hs1, hshi'.mp hs2⟩
      · rintro ⟨⟨he, hg1, hg2⟩, hs1, hs2⟩
        exact ⟨henv.mpr he, ⟨hglo.mpr hg1, hghi.mpr hg2⟩,
          hslo.mpr hs1, hshi'.mpr hs2⟩

/-- **The affine `hGd` discharger.** -/
theorem realGdOfA_sat (P : Parse.PProblem) (mt : TransMeta) (A : AffineModel n)
    {εR : QF} (hεR : parseQ P.R.epsilon = some εR)
    (hf : faithfulAffine P mt A = true)
    (hlen : P.R.stateVars.length = n)
    (hσd : ∀ j, j < n → (mt.scales.getD j (qOfInt 0)).pos)
    (hσv : ∀ j : Fin n, 0 < sigmaOf mt.scales j) :
    ∀ (q' : ℕ) (ν : DL.State (Var n)),
      Formula.sat (realGdOfA P mt.scales A q') ν
        ↔ Formula.sat (A.GdOf q') (scaleState (sigmaOf mt.scales) ν) := by
  unfold faithfulAffine at hf
  simp only [Bool.and_eq_true] at hf
  obtain ⟨hvtlen, hframe⟩ := hf
  obtain ⟨-, -, -, hml, hmode⟩ := faithfulFrame_facts hεR hframe
  have hvtl : A.vtops.length = A.core.modes.length := by
    simpa using hvtlen
  intro q' ν
  rcases hpm : P.R.modes[q']? with _ | pm
  · have hmn : A.core.modes[q']? = none := by
      rw [List.getElem?_eq_none_iff] at hpm ⊢
      omega
    unfold realGdOfA AffineModel.GdOf
    rw [hpm, hmn]
    simp [Formula.sat]
  rcases hm : A.core.modes[q']? with _ | m
  · exfalso
    rw [List.getElem?_eq_none_iff] at hm
    obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hpm
    omega
  rcases htop : A.vtops[q']? with _ | top
  · exfalso
    rw [List.getElem?_eq_none_iff] at htop
    obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hpm
    omega
  obtain ⟨hmc, -⟩ := hmode q' pm m hpm hm
  obtain ⟨eb, heb, hef⟩ := modeCore_env_facts hlen hmc
  have henv := envFormulaR_sat A.core (boundsOfForm_pos heb) hσd hσv hef ν
  have hglo := scaledLo_sat m.gcoord (hσd m.gcoord.val m.gcoord.isLt) (hσv m.gcoord)
    m.glo ν
  unfold realGdOfA AffineModel.GdOf
  simp only [hpm, hm, htop, heb]
  clear htop
  cases htp : top with
  | none =>
      simp only [htp, Formula.sat]
      constructor
      · rintro ⟨he, hg1, -⟩
        exact ⟨henv.mp he, hglo.mp hg1, trivial⟩
      · rintro ⟨he, hg1, -⟩
        exact ⟨henv.mpr he, hglo.mpr hg1, trivial⟩
  | some gh =>
      have hgh := scaledHi_sat m.gcoord (hσd m.gcoord.val m.gcoord.isLt) (hσv m.gcoord)
        gh ν
      simp only [htp, Formula.sat]
      constructor
      · rintro ⟨he, hg1, hg2⟩
        exact ⟨henv.mp he, hglo.mp hg1, hgh.mp hg2⟩
      · rintro ⟨he, hg1, hg2⟩
        exact ⟨henv.mpr he, hglo.mpr hg1, hgh.mpr hg2⟩

/-! ## The assembled per-family rescale theorems -/

/-- **Terrain bridge.** A `faithfulTerrain` verdict upgrades the scaled model's per-mode
settling certificate (at the terrain guard map) to the real parsed model. -/
theorem faithfulTerrain_rescale (P : Parse.PProblem) (mt : TransMeta)
    (T : TerrainModel n) {εR : QF} (hεR : parseQ P.R.epsilon = some εR)
    (hf : faithfulTerrain P mt T = true)
    (hnod : P.R.stateVars.Nodup) (hlen : P.R.stateVars.length = n)
    (hσd : ∀ j, j < n → (mt.scales.getD j (qOfInt 0)).pos)
    (hσv : ∀ j : Fin n, 0 < sigmaOf mt.scales j)
    (huv : 0 < (qDiv (qDiv εR mt.lam) (qOfInt T.core.dtQ)).val)
    (hidx : ∀ m ∈ T.core.modes, ∀ i : Fin n, shapeIdxOkB i (m.shapes i) = true)
    {q : ℕ} {pm : Parse.PMode} {m : SettlingMode n}
    (hpm : P.R.modes[q]? = some pm) (hm : T.core.modes[q]? = some m)
    (dts : ℝ)
    (hB : GuardSettlingB T.core.graph T.GdOf m.fieldOf (Term.const 1) T.core.envF dts q) :
    GuardSettlingB T.core.graph (realGdOfT P mt.scales T)
      (realFieldOf P.R.stateVars pm n) (Term.const 1)
      (realEnvOf P.R.stateVars n pm)
      ((qDiv (qDiv εR mt.lam) (qOfInt T.core.dtQ)).val * dts) q := by
  have hframe : faithfulFrame P mt T.core
      (fun q pm m => bandTerrain P.R.stateVars mt.scales pm m T.core.env &&
        (match T.sbands[q]? with
         | some sb => sbandFaithful P.R.stateVars mt.scales pm sb
         | none => false)) = true := by
    unfold faithfulTerrain at hf
    simp only [Bool.and_eq_true] at hf
    exact hf.2
  obtain ⟨hlam, hdt, -, hml, hmode⟩ := faithfulFrame_facts hεR hframe
  obtain ⟨hmc, -⟩ := hmode q pm m hpm hm
  obtain ⟨eb, heb, hef⟩ := modeCore_env_facts hlen hmc
  have hmm : m ∈ T.core.modes := by
    obtain ⟨h, hEq⟩ := List.getElem?_eq_some_iff.mp hm
    exact hEq ▸ List.getElem_mem h
  refine GuardSettlingB_rescale T.core.graph T.GdOf (realGdOfT P mt.scales T)
    m.fieldOf (realFieldOf P.R.stateVars pm n) T.core.envF
    (realEnvOf P.R.stateVars n pm) (sigmaOf mt.scales)
    (qDiv (qDiv εR mt.lam) (qOfInt T.core.dtQ)).val dts q
    (fun i => ne_of_gt (hσv i)) huv
    (fieldOf_bridge hnod hlen hσd hσv
      (qDiv_pos (qDiv_pos (parseQ_pos hεR) hlam) (by simpa [qOfInt] using hdt))
      pm m (modeCore_ode_facts hlen hmc) (hidx m hmm))
    (realGdOfT_sat P mt T hεR hf hlen hσd hσv)
    ?_ hB
  intro ν
  have hered : realEnvOf P.R.stateVars n pm = envFormulaR P.R.stateVars n eb := by
    unfold realEnvOf
    simp only [heb]
  rw [hered]
  exact envFormulaR_sat T.core (boundsOfForm_pos heb) hσd hσv hef ν

/-- **Affine bridge.** -/
theorem faithfulAffine_rescale (P : Parse.PProblem) (mt : TransMeta)
    (A : AffineModel n) {εR : QF} (hεR : parseQ P.R.epsilon = some εR)
    (hf : faithfulAffine P mt A = true)
    (hnod : P.R.stateVars.Nodup) (hlen : P.R.stateVars.length = n)
    (hσd : ∀ j, j < n → (mt.scales.getD j (qOfInt 0)).pos)
    (hσv : ∀ j : Fin n, 0 < sigmaOf mt.scales j)
    (huv : 0 < (qDiv (qDiv εR mt.lam) (qOfInt A.core.dtQ)).val)
    (hidx : ∀ m ∈ A.core.modes, ∀ i : Fin n, shapeIdxOkB i (m.shapes i) = true)
    {q : ℕ} {pm : Parse.PMode} {m : SettlingMode n}
    (hpm : P.R.modes[q]? = some pm) (hm : A.core.modes[q]? = some m)
    (dts : ℝ)
    (hB : GuardSettlingB A.core.graph A.GdOf m.fieldOf (Term.const 1) A.core.envF dts q) :
    GuardSettlingB A.core.graph (realGdOfA P mt.scales A)
      (realFieldOf P.R.stateVars pm n) (Term.const 1)
      (realEnvOf P.R.stateVars n pm)
      ((qDiv (qDiv εR mt.lam) (qOfInt A.core.dtQ)).val * dts) q := by
  have hframe : faithfulFrame P mt A.core
      (fun q pm m => match A.vtops[q]? with
        | some top => bandAffine P.R.stateVars mt.scales pm m top
        | none => false) = true := by
    unfold faithfulAffine at hf
    simp only [Bool.and_eq_true] at hf
    exact hf.2
  obtain ⟨hlam, hdt, -, hml, hmode⟩ := faithfulFrame_facts hεR hframe
  obtain ⟨hmc, -⟩ := hmode q pm m hpm hm
  obtain ⟨eb, heb, hef⟩ := modeCore_env_facts hlen hmc
  have hmm : m ∈ A.core.modes := by
    obtain ⟨h, hEq⟩ := List.getElem?_eq_some_iff.mp hm
    exact hEq ▸ List.getElem_mem h
  refine GuardSettlingB_rescale A.core.graph A.GdOf (realGdOfA P mt.scales A)
    m.fieldOf (realFieldOf P.R.stateVars pm n) A.core.envF
    (realEnvOf P.R.stateVars n pm) (sigmaOf mt.scales)
    (qDiv (qDiv εR mt.lam) (qOfInt A.core.dtQ)).val dts q
    (fun i => ne_of_gt (hσv i)) huv
    (fieldOf_bridge hnod hlen hσd hσv
      (qDiv_pos (qDiv_pos (parseQ_pos hεR) hlam) (by simpa [qOfInt] using hdt))
      pm m (modeCore_ode_facts hlen hmc) (hidx m hmm))
    (realGdOfA_sat P mt A hεR hf hlen hσd hσv)
    ?_ hB
  intro ν
  have hered : realEnvOf P.R.stateVars n pm = envFormulaR P.R.stateVars n eb := by
    unfold realEnvOf
    simp only [heb]
  rw [hered]
  exact envFormulaR_sat A.core (boundsOfForm_pos heb) hσd hσv hef ν

end RelCertifier
