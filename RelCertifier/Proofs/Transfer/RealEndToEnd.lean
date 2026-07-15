/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Real-model end-to-end, generic per family

One theorem per model family, fully generic in the benchmark: from the kernel checker
verdict (`decideWellFormed{,T,A}`), the kernel fidelity certificate
(`faithfulSettling`/`Terrain`/`Affine`), the per-benchmark decidable side conditions,
the freshness data, and the Z3 `BoxLe` certificates, every declared mode of the REAL
parsed benchmark satisfies the settling obligation at the real duration `u·dt`.

Per-benchmark instantiation (Instances/) is then a dozen lines of `decide`/`rfl`/
`norm_num` discharges — the watertank pattern, mechanized for all 46.
-/
import RelCertifier.Proofs.Transfer.FaithfulBridgeGuards
import RelCertifier.Proofs.Encoding.FvDischarge

namespace RelCertifier

open DL DLCalTiming DLRel Function Set

variable {n : ℕ}

/-- Per-mode `GuardSettlingB` extraction from the Tier-B H bundle, generic in the guard
map (settling/terrain/affine all produce H over the settling core's graph). -/
theorem GuardSettlingH_B' (M : SettlingModel n) (Gd : ℕ → Formula (Var n))
    {mv : Var n} {g : Term (Var n)} {tg : Var n} {dt : ℝ} {fL : Fin n → Term (Var n)}
    (hH : GuardSettlingH M.graph Gd mv g (Term.const 1) tg dt fL M.envF)
    {q : ℕ} {m : SettlingMode n} (hm : M.modes[q]? = some m) :
    GuardSettlingB M.graph Gd m.fieldOf (Term.const 1) M.envF dt q := by
  obtain ⟨-, -, -, -, -, -, -, hmodes⟩ := hH
  have hma : M.graph.modeAt q = some (m.toRMode M) := by
    rw [graph_modeAt, hm]
    rfl
  obtain ⟨fR, hsys, -, -, hB, -⟩ := hmodes q (m.toRMode M) hma
  have hfr : m.fieldOf = fR := rightBlock_inj hsys
  rw [hfr]
  exact hB

/-- **Settling family, real-model end to end (generic).** -/
theorem settling_real_end_to_end (P : Parse.PProblem) (mt : TransMeta)
    (M : SettlingModel n) {εR : QF} (hεR : parseQ P.R.epsilon = some εR)
    (hfaith : faithfulSettling P mt M = true)
    (hnod : P.R.stateVars.Nodup) (hlen : P.R.stateVars.length = n)
    (hσd : ∀ j, j < n → (mt.scales.getD j (qOfInt 0)).pos)
    (hσv : ∀ j : Fin n, 0 < sigmaOf mt.scales j)
    (huv : 0 < (qDiv (qDiv εR mt.lam) (qOfInt M.dtQ)).val)
    (hidx : ∀ m ∈ M.modes, ∀ i : Fin n, shapeIdxOkB i (m.shapes i) = true)
    (mv tg : Var n) (g : Term (Var n)) (fL : Fin n → Term (Var n))
    (hwf : decideWellFormed M = true) (hdt : (0 : ℝ) ≤ (M.dt : ℝ))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (M.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (M.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (M.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    :
    ∀ q pm m, P.R.modes[q]? = some pm → M.modes[q]? = some m →
      GuardSettlingB M.graph (realGdOf P M) (realFieldOf P.R.stateVars pm n)
        (Term.const 1) (realEnvOf P.R.stateVars n pm)
        ((qDiv (qDiv εR mt.lam) (qOfInt M.dtQ)).val * (M.dt : ℝ)) q := by
  intro q pm m hpm hm
  have hH : GuardSettlingH M.graph M.GdOf mv g (Term.const 1) tg (M.dt : ℝ) fL M.envF :=
    wellformed_sound M mv tg g fL hwf hdt hg hmvclk hmvtg hmvGd htgGd hfrzGd
  exact faithfulSettling_rescale P mt M hεR hfaith hnod hlen hσd hσv huv hidx
    hpm hm (M.dt : ℝ) (GuardSettlingH_B' M M.GdOf hH hm)

/-- **Terrain family, real-model end to end (generic).** -/
theorem terrain_real_end_to_end (P : Parse.PProblem) (mt : TransMeta)
    (T : TerrainModel n) {εR : QF} (hεR : parseQ P.R.epsilon = some εR)
    (hfaith : faithfulTerrain P mt T = true)
    (hnod : P.R.stateVars.Nodup) (hlen : P.R.stateVars.length = n)
    (hσd : ∀ j, j < n → (mt.scales.getD j (qOfInt 0)).pos)
    (hσv : ∀ j : Fin n, 0 < sigmaOf mt.scales j)
    (huv : 0 < (qDiv (qDiv εR mt.lam) (qOfInt T.core.dtQ)).val)
    (hidx : ∀ m ∈ T.core.modes, ∀ i : Fin n, shapeIdxOkB i (m.shapes i) = true)
    (mv tg : Var n) (g : Term (Var n)) (fL : Fin n → Term (Var n))
    (hwf : decideWellFormedT T = true) (hdt : (0 : ℝ) ≤ (T.core.dt : ℝ))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (T.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (T.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (T.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    :
    ∀ q pm m, P.R.modes[q]? = some pm → T.core.modes[q]? = some m →
      GuardSettlingB T.core.graph (realGdOfT P mt.scales T)
        (realFieldOf P.R.stateVars pm n) (Term.const 1)
        (realEnvOf P.R.stateVars n pm)
        ((qDiv (qDiv εR mt.lam) (qOfInt T.core.dtQ)).val * (T.core.dt : ℝ)) q := by
  intro q pm m hpm hm
  have hH : GuardSettlingH T.core.graph T.GdOf mv g (Term.const 1) tg
      (T.core.dt : ℝ) fL T.core.envF :=
    wellformed_sound_terrain T mv tg g fL hwf hdt hg hmvclk hmvtg hmvGd htgGd
      hfrzGd
  exact faithfulTerrain_rescale P mt T hεR hfaith hnod hlen hσd hσv huv hidx
    hpm hm (T.core.dt : ℝ) (GuardSettlingH_B' T.core T.GdOf hH hm)

/-- **Affine family, real-model end to end (generic).** -/
theorem affine_real_end_to_end (P : Parse.PProblem) (mt : TransMeta)
    (A : AffineModel n) {εR : QF} (hεR : parseQ P.R.epsilon = some εR)
    (hfaith : faithfulAffine P mt A = true)
    (hnod : P.R.stateVars.Nodup) (hlen : P.R.stateVars.length = n)
    (hσd : ∀ j, j < n → (mt.scales.getD j (qOfInt 0)).pos)
    (hσv : ∀ j : Fin n, 0 < sigmaOf mt.scales j)
    (huv : 0 < (qDiv (qDiv εR mt.lam) (qOfInt A.core.dtQ)).val)
    (hidx : ∀ m ∈ A.core.modes, ∀ i : Fin n, shapeIdxOkB i (m.shapes i) = true)
    (mv tg : Var n) (g : Term (Var n)) (fL : Fin n → Term (Var n))
    (hwf : decideWellFormedA A = true) (hdt : (0 : ℝ) ≤ (A.core.dt : ℝ))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (A.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (A.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (A.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    :
    ∀ q pm m, P.R.modes[q]? = some pm → A.core.modes[q]? = some m →
      GuardSettlingB A.core.graph (realGdOfA P mt.scales A)
        (realFieldOf P.R.stateVars pm n) (Term.const 1)
        (realEnvOf P.R.stateVars n pm)
        ((qDiv (qDiv εR mt.lam) (qOfInt A.core.dtQ)).val * (A.core.dt : ℝ)) q := by
  intro q pm m hpm hm
  have hH : GuardSettlingH A.core.graph A.GdOf mv g (Term.const 1) tg
      (A.core.dt : ℝ) fL A.core.envF :=
    wellformed_sound_affine A mv tg g fL hwf hdt hg hmvclk hmvtg hmvGd htgGd
      hfrzGd
  exact faithfulAffine_rescale P mt A hεR hfaith hnod hlen hσd hσv huv hidx
    hpm hm (A.core.dt : ℝ) (GuardSettlingH_B' A.core A.GdOf hH hm)

end RelCertifier
