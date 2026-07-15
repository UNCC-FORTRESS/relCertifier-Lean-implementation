/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# GENERATED per-benchmark real-model end-to-end theorems (scripts/gen_real_instances.py)

One theorem per benchmark: the generic family theorem instantiated at the parser-emitted
IR, the transcription metadata, and the kernel-certified model, with every decidable side
condition discharged. Residual hypotheses per theorem: the freshness data (mv/tg choices)
and the Z3 BoxLe certificates — the z3_unsat_sound leaf, exactly as in the watertank demo.
-/
import RelCertifier.Proofs.Transfer.RealEndToEnd
import RelCertifier.Proofs.Transfer.FaithfulBridgePad
import RelCertifier.Instances.FaithfulCerts

namespace RelCertifier

open DL DLCalTiming DLRel Function Set RelCertifier.Parse

/-- `arm_chain_rung1`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem arm_chain_rung1_real
    (mv tg : Var 1) (g : Term (Var 1)) (fL : Fin 1 → Term (Var 1))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (arm_chain_rung1M.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (arm_chain_rung1M.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (arm_chain_rung1M.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, arm_chain_rung1M.graph.modeAt q = some m →
        ∀ ν, Formula.sat (arm_chain_rung1M.GdOf q) ν →
          BoxLe (Program.ode m.sys arm_chain_rung1M.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, arm_chain_rung1_IR.R.modes[q]? = some pm → arm_chain_rung1M.modes[q]? = some m →
      GuardSettlingB arm_chain_rung1M.graph (realGdOf arm_chain_rung1_IR arm_chain_rung1M)
        (realFieldOf arm_chain_rung1_IR.R.stateVars pm 1) (Term.const 1)
        (realEnvOf arm_chain_rung1_IR.R.stateVars 1 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) arm_chain_rung1_meta.lam) (qOfInt arm_chain_rung1M.dtQ)).val
          * ((arm_chain_rung1M.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end arm_chain_rung1_IR arm_chain_rung1_meta arm_chain_rung1M
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) arm_chain_rung1_meta.lam)
          (qOfInt arm_chain_rung1M.dtQ) = (⟨10, 20⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, arm_chain_rung1M])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `arm_chain_rung2`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem arm_chain_rung2_real
    (mv tg : Var 1) (g : Term (Var 1)) (fL : Fin 1 → Term (Var 1))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (arm_chain_rung2M.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (arm_chain_rung2M.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (arm_chain_rung2M.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, arm_chain_rung2M.graph.modeAt q = some m →
        ∀ ν, Formula.sat (arm_chain_rung2M.GdOf q) ν →
          BoxLe (Program.ode m.sys arm_chain_rung2M.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, arm_chain_rung2_IR.R.modes[q]? = some pm → arm_chain_rung2M.modes[q]? = some m →
      GuardSettlingB arm_chain_rung2M.graph (realGdOf arm_chain_rung2_IR arm_chain_rung2M)
        (realFieldOf arm_chain_rung2_IR.R.stateVars pm 1) (Term.const 1)
        (realEnvOf arm_chain_rung2_IR.R.stateVars 1 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) arm_chain_rung2_meta.lam) (qOfInt arm_chain_rung2M.dtQ)).val
          * ((arm_chain_rung2M.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end arm_chain_rung2_IR arm_chain_rung2_meta arm_chain_rung2M
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) arm_chain_rung2_meta.lam)
          (qOfInt arm_chain_rung2M.dtQ) = (⟨10, 20⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, arm_chain_rung2M])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `arm_chain_rung3` (PADDED model): real-model end to end (residuals: freshness data +
Z3 certificates). -/
theorem arm_chain_rung3_real
    (mv tg : Var 2) (g : Term (Var 2)) (fL : Fin 2 → Term (Var 2))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (arm_chain_rung3M.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (arm_chain_rung3M.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (arm_chain_rung3M.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, arm_chain_rung3M.graph.modeAt q = some m →
        ∀ ν, Formula.sat (arm_chain_rung3M.GdOf q) ν →
          BoxLe (Program.ode m.sys arm_chain_rung3M.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, arm_chain_rung3_IR.R.modes[q]? = some pm → arm_chain_rung3M.modes[q]? = some m →
      GuardSettlingB arm_chain_rung3M.graph (realGdOf arm_chain_rung3_IR arm_chain_rung3M)
        (realFieldOf arm_chain_rung3_IR.R.stateVars pm 2) (Term.const 1)
        (realEnvOf arm_chain_rung3_IR.R.stateVars 2 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) arm_chain_rung3_meta.lam) (qOfInt arm_chain_rung3M.dtQ)).val
          * ((arm_chain_rung3M.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end_pad arm_chain_rung3_IR arm_chain_rung3_meta arm_chain_rung3M
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) (by decide)
    (by intro j hj; interval_cases j <;> decide)
    (fun j hj => sigmaOf_pos_lt (by decide) hj)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) arm_chain_rung3_meta.lam)
          (qOfInt arm_chain_rung3M.dtQ) = (⟨10, 50⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide) (by decide) (by decide) (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, arm_chain_rung3M])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `arm_fidelity_high` (PADDED model): real-model end to end (residuals: freshness data +
Z3 certificates). -/
theorem arm_fidelity_high_real
    (mv tg : Var 2) (g : Term (Var 2)) (fL : Fin 2 → Term (Var 2))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (arm_fidelity_highM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (arm_fidelity_highM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (arm_fidelity_highM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, arm_fidelity_highM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (arm_fidelity_highM.GdOf q) ν →
          BoxLe (Program.ode m.sys arm_fidelity_highM.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, arm_fidelity_high_IR.R.modes[q]? = some pm → arm_fidelity_highM.modes[q]? = some m →
      GuardSettlingB arm_fidelity_highM.graph (realGdOf arm_fidelity_high_IR arm_fidelity_highM)
        (realFieldOf arm_fidelity_high_IR.R.stateVars pm 2) (Term.const 1)
        (realEnvOf arm_fidelity_high_IR.R.stateVars 2 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) arm_fidelity_high_meta.lam) (qOfInt arm_fidelity_highM.dtQ)).val
          * ((arm_fidelity_highM.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end_pad arm_fidelity_high_IR arm_fidelity_high_meta arm_fidelity_highM
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) (by decide)
    (by intro j hj; interval_cases j <;> decide)
    (fun j hj => sigmaOf_pos_lt (by decide) hj)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) arm_fidelity_high_meta.lam)
          (qOfInt arm_fidelity_highM.dtQ) = (⟨10, 50⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide) (by decide) (by decide) (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, arm_fidelity_highM])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `arm_fidelity_low` (PADDED model): real-model end to end (residuals: freshness data +
Z3 certificates). -/
theorem arm_fidelity_low_real
    (mv tg : Var 2) (g : Term (Var 2)) (fL : Fin 2 → Term (Var 2))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (arm_fidelity_lowM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (arm_fidelity_lowM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (arm_fidelity_lowM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, arm_fidelity_lowM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (arm_fidelity_lowM.GdOf q) ν →
          BoxLe (Program.ode m.sys arm_fidelity_lowM.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, arm_fidelity_low_IR.R.modes[q]? = some pm → arm_fidelity_lowM.modes[q]? = some m →
      GuardSettlingB arm_fidelity_lowM.graph (realGdOf arm_fidelity_low_IR arm_fidelity_lowM)
        (realFieldOf arm_fidelity_low_IR.R.stateVars pm 2) (Term.const 1)
        (realEnvOf arm_fidelity_low_IR.R.stateVars 2 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) arm_fidelity_low_meta.lam) (qOfInt arm_fidelity_lowM.dtQ)).val
          * ((arm_fidelity_lowM.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end_pad arm_fidelity_low_IR arm_fidelity_low_meta arm_fidelity_lowM
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) (by decide)
    (by intro j hj; interval_cases j <;> decide)
    (fun j hj => sigmaOf_pos_lt (by decide) hj)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) arm_fidelity_low_meta.lam)
          (qOfInt arm_fidelity_lowM.dtQ) = (⟨10, 20⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide) (by decide) (by decide) (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, arm_fidelity_lowM])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `arm_fidelity_mid` (PADDED model): real-model end to end (residuals: freshness data +
Z3 certificates). -/
theorem arm_fidelity_mid_real
    (mv tg : Var 2) (g : Term (Var 2)) (fL : Fin 2 → Term (Var 2))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (arm_fidelity_midM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (arm_fidelity_midM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (arm_fidelity_midM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, arm_fidelity_midM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (arm_fidelity_midM.GdOf q) ν →
          BoxLe (Program.ode m.sys arm_fidelity_midM.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, arm_fidelity_mid_IR.R.modes[q]? = some pm → arm_fidelity_midM.modes[q]? = some m →
      GuardSettlingB arm_fidelity_midM.graph (realGdOf arm_fidelity_mid_IR arm_fidelity_midM)
        (realFieldOf arm_fidelity_mid_IR.R.stateVars pm 2) (Term.const 1)
        (realEnvOf arm_fidelity_mid_IR.R.stateVars 2 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) arm_fidelity_mid_meta.lam) (qOfInt arm_fidelity_midM.dtQ)).val
          * ((arm_fidelity_midM.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end_pad arm_fidelity_mid_IR arm_fidelity_mid_meta arm_fidelity_midM
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) (by decide)
    (by intro j hj; interval_cases j <;> decide)
    (fun j hj => sigmaOf_pos_lt (by decide) hj)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) arm_fidelity_mid_meta.lam)
          (qOfInt arm_fidelity_midM.dtQ) = (⟨10, 20⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide) (by decide) (by decide) (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, arm_fidelity_midM])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `arm_refinement` (PADDED model): real-model end to end (residuals: freshness data +
Z3 certificates). -/
theorem arm_refinement_real
    (mv tg : Var 2) (g : Term (Var 2)) (fL : Fin 2 → Term (Var 2))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (arm_refinementM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (arm_refinementM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (arm_refinementM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, arm_refinementM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (arm_refinementM.GdOf q) ν →
          BoxLe (Program.ode m.sys arm_refinementM.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, arm_refinement_IR.R.modes[q]? = some pm → arm_refinementM.modes[q]? = some m →
      GuardSettlingB arm_refinementM.graph (realGdOf arm_refinement_IR arm_refinementM)
        (realFieldOf arm_refinement_IR.R.stateVars pm 2) (Term.const 1)
        (realEnvOf arm_refinement_IR.R.stateVars 2 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) arm_refinement_meta.lam) (qOfInt arm_refinementM.dtQ)).val
          * ((arm_refinementM.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end_pad arm_refinement_IR arm_refinement_meta arm_refinementM
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) (by decide)
    (by intro j hj; interval_cases j <;> decide)
    (fun j hj => sigmaOf_pos_lt (by decide) hj)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) arm_refinement_meta.lam)
          (qOfInt arm_refinementM.dtQ) = (⟨10, 20⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide) (by decide) (by decide) (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, arm_refinementM])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `attitude_rate`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem attitude_rate_real
    (mv tg : Var 6) (g : Term (Var 6)) (fL : Fin 6 → Term (Var 6))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (attitude_rateM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (attitude_rateM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (attitude_rateM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, attitude_rateM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (attitude_rateM.GdOf q) ν →
          BoxLe (Program.ode m.sys attitude_rateM.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, attitude_rate_IR.R.modes[q]? = some pm → attitude_rateM.modes[q]? = some m →
      GuardSettlingB attitude_rateM.graph (realGdOf attitude_rate_IR attitude_rateM)
        (realFieldOf attitude_rate_IR.R.stateVars pm 6) (Term.const 1)
        (realEnvOf attitude_rate_IR.R.stateVars 6 pm)
        ((qDiv (qDiv (⟨20, 10⟩ : QF) attitude_rate_meta.lam) (qOfInt attitude_rateM.dtQ)).val
          * ((attitude_rateM.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end attitude_rate_IR attitude_rate_meta attitude_rateM
    (εR := ⟨20, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨20, 10⟩ : QF) attitude_rate_meta.lam)
          (qOfInt attitude_rateM.dtQ) = (⟨20, 20⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, attitude_rateM])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `endurance_gain_M1`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem endurance_gain_M1_real
    (mv tg : Var 2) (g : Term (Var 2)) (fL : Fin 2 → Term (Var 2))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (endurance_gain_M1M.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (endurance_gain_M1M.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (endurance_gain_M1M.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, endurance_gain_M1M.graph.modeAt q = some m →
        ∀ ν, Formula.sat (endurance_gain_M1M.GdOf q) ν →
          BoxLe (Program.ode m.sys endurance_gain_M1M.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, endurance_gain_M1_IR.R.modes[q]? = some pm → endurance_gain_M1M.modes[q]? = some m →
      GuardSettlingB endurance_gain_M1M.graph (realGdOf endurance_gain_M1_IR endurance_gain_M1M)
        (realFieldOf endurance_gain_M1_IR.R.stateVars pm 2) (Term.const 1)
        (realEnvOf endurance_gain_M1_IR.R.stateVars 2 pm)
        ((qDiv (qDiv (⟨5, 10⟩ : QF) endurance_gain_M1_meta.lam) (qOfInt endurance_gain_M1M.dtQ)).val
          * ((endurance_gain_M1M.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end endurance_gain_M1_IR endurance_gain_M1_meta endurance_gain_M1M
    (εR := ⟨5, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨5, 10⟩ : QF) endurance_gain_M1_meta.lam)
          (qOfInt endurance_gain_M1M.dtQ) = (⟨5, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, endurance_gain_M1M])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `endurance_orderlift_1to2`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem endurance_orderlift_1to2_real
    (mv tg : Var 3) (g : Term (Var 3)) (fL : Fin 3 → Term (Var 3))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (endurance_orderlift_1to2M.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (endurance_orderlift_1to2M.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (endurance_orderlift_1to2M.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, endurance_orderlift_1to2M.graph.modeAt q = some m →
        ∀ ν, Formula.sat (endurance_orderlift_1to2M.GdOf q) ν →
          BoxLe (Program.ode m.sys endurance_orderlift_1to2M.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, endurance_orderlift_1to2_IR.R.modes[q]? = some pm → endurance_orderlift_1to2M.modes[q]? = some m →
      GuardSettlingB endurance_orderlift_1to2M.graph (realGdOf endurance_orderlift_1to2_IR endurance_orderlift_1to2M)
        (realFieldOf endurance_orderlift_1to2_IR.R.stateVars pm 3) (Term.const 1)
        (realEnvOf endurance_orderlift_1to2_IR.R.stateVars 3 pm)
        ((qDiv (qDiv (⟨5, 10⟩ : QF) endurance_orderlift_1to2_meta.lam) (qOfInt endurance_orderlift_1to2M.dtQ)).val
          * ((endurance_orderlift_1to2M.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end endurance_orderlift_1to2_IR endurance_orderlift_1to2_meta endurance_orderlift_1to2M
    (εR := ⟨5, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨5, 10⟩ : QF) endurance_orderlift_1to2_meta.lam)
          (qOfInt endurance_orderlift_1to2M.dtQ) = (⟨5, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, endurance_orderlift_1to2M])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `endurance_orderlift_2to3`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem endurance_orderlift_2to3_real
    (mv tg : Var 4) (g : Term (Var 4)) (fL : Fin 4 → Term (Var 4))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (endurance_orderlift_2to3M.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (endurance_orderlift_2to3M.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (endurance_orderlift_2to3M.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, endurance_orderlift_2to3M.graph.modeAt q = some m →
        ∀ ν, Formula.sat (endurance_orderlift_2to3M.GdOf q) ν →
          BoxLe (Program.ode m.sys endurance_orderlift_2to3M.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, endurance_orderlift_2to3_IR.R.modes[q]? = some pm → endurance_orderlift_2to3M.modes[q]? = some m →
      GuardSettlingB endurance_orderlift_2to3M.graph (realGdOf endurance_orderlift_2to3_IR endurance_orderlift_2to3M)
        (realFieldOf endurance_orderlift_2to3_IR.R.stateVars pm 4) (Term.const 1)
        (realEnvOf endurance_orderlift_2to3_IR.R.stateVars 4 pm)
        ((qDiv (qDiv (⟨5, 10⟩ : QF) endurance_orderlift_2to3_meta.lam) (qOfInt endurance_orderlift_2to3M.dtQ)).val
          * ((endurance_orderlift_2to3M.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end endurance_orderlift_2to3_IR endurance_orderlift_2to3_meta endurance_orderlift_2to3M
    (εR := ⟨5, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨5, 10⟩ : QF) endurance_orderlift_2to3_meta.lam)
          (qOfInt endurance_orderlift_2to3M.dtQ) = (⟨5, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, endurance_orderlift_2to3M])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `match_multi_eps`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem match_multi_eps_real
    (mv tg : Var 2) (g : Term (Var 2)) (fL : Fin 2 → Term (Var 2))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (match_multi_epsM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (match_multi_epsM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (match_multi_epsM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, match_multi_epsM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (match_multi_epsM.GdOf q) ν →
          BoxLe (Program.ode m.sys match_multi_epsM.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, match_multi_eps_IR.R.modes[q]? = some pm → match_multi_epsM.modes[q]? = some m →
      GuardSettlingB match_multi_epsM.graph (realGdOf match_multi_eps_IR match_multi_epsM)
        (realFieldOf match_multi_eps_IR.R.stateVars pm 2) (Term.const 1)
        (realEnvOf match_multi_eps_IR.R.stateVars 2 pm)
        ((qDiv (qDiv (⟨3, 10⟩ : QF) match_multi_eps_meta.lam) (qOfInt match_multi_epsM.dtQ)).val
          * ((match_multi_epsM.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end match_multi_eps_IR match_multi_eps_meta match_multi_epsM
    (εR := ⟨3, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨3, 10⟩ : QF) match_multi_eps_meta.lam)
          (qOfInt match_multi_epsM.dtQ) = (⟨3, 150⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, match_multi_epsM])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `match_multi_rate`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem match_multi_rate_real
    (mv tg : Var 2) (g : Term (Var 2)) (fL : Fin 2 → Term (Var 2))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (match_multi_rateM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (match_multi_rateM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (match_multi_rateM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, match_multi_rateM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (match_multi_rateM.GdOf q) ν →
          BoxLe (Program.ode m.sys match_multi_rateM.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, match_multi_rate_IR.R.modes[q]? = some pm → match_multi_rateM.modes[q]? = some m →
      GuardSettlingB match_multi_rateM.graph (realGdOf match_multi_rate_IR match_multi_rateM)
        (realFieldOf match_multi_rate_IR.R.stateVars pm 2) (Term.const 1)
        (realEnvOf match_multi_rate_IR.R.stateVars 2 pm)
        ((qDiv (qDiv (⟨3, 10⟩ : QF) match_multi_rate_meta.lam) (qOfInt match_multi_rateM.dtQ)).val
          * ((match_multi_rateM.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end match_multi_rate_IR match_multi_rate_meta match_multi_rateM
    (εR := ⟨3, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨3, 10⟩ : QF) match_multi_rate_meta.lam)
          (qOfInt match_multi_rateM.dtQ) = (⟨3, 30⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, match_multi_rateM])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `plant_fan_high` (PADDED model): real-model end to end (residuals: freshness data +
Z3 certificates). -/
theorem plant_fan_high_real
    (mv tg : Var 2) (g : Term (Var 2)) (fL : Fin 2 → Term (Var 2))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (plant_fan_highM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (plant_fan_highM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (plant_fan_highM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, plant_fan_highM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (plant_fan_highM.GdOf q) ν →
          BoxLe (Program.ode m.sys plant_fan_highM.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, plant_fan_high_IR.R.modes[q]? = some pm → plant_fan_highM.modes[q]? = some m →
      GuardSettlingB plant_fan_highM.graph (realGdOf plant_fan_high_IR plant_fan_highM)
        (realFieldOf plant_fan_high_IR.R.stateVars pm 2) (Term.const 1)
        (realEnvOf plant_fan_high_IR.R.stateVars 2 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) plant_fan_high_meta.lam) (qOfInt plant_fan_highM.dtQ)).val
          * ((plant_fan_highM.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end_pad plant_fan_high_IR plant_fan_high_meta plant_fan_highM
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) (by decide)
    (by intro j hj; interval_cases j <;> decide)
    (fun j hj => sigmaOf_pos_lt (by decide) hj)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) plant_fan_high_meta.lam)
          (qOfInt plant_fan_highM.dtQ) = (⟨10, 50⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide) (by decide) (by decide) (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, plant_fan_highM])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `plant_fan_low` (PADDED model): real-model end to end (residuals: freshness data +
Z3 certificates). -/
theorem plant_fan_low_real
    (mv tg : Var 2) (g : Term (Var 2)) (fL : Fin 2 → Term (Var 2))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (plant_fan_lowM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (plant_fan_lowM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (plant_fan_lowM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, plant_fan_lowM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (plant_fan_lowM.GdOf q) ν →
          BoxLe (Program.ode m.sys plant_fan_lowM.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, plant_fan_low_IR.R.modes[q]? = some pm → plant_fan_lowM.modes[q]? = some m →
      GuardSettlingB plant_fan_lowM.graph (realGdOf plant_fan_low_IR plant_fan_lowM)
        (realFieldOf plant_fan_low_IR.R.stateVars pm 2) (Term.const 1)
        (realEnvOf plant_fan_low_IR.R.stateVars 2 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) plant_fan_low_meta.lam) (qOfInt plant_fan_lowM.dtQ)).val
          * ((plant_fan_lowM.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end_pad plant_fan_low_IR plant_fan_low_meta plant_fan_lowM
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) (by decide)
    (by intro j hj; interval_cases j <;> decide)
    (fun j hj => sigmaOf_pos_lt (by decide) hj)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) plant_fan_low_meta.lam)
          (qOfInt plant_fan_lowM.dtQ) = (⟨10, 20⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide) (by decide) (by decide) (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, plant_fan_lowM])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `plant_fan_mid` (PADDED model): real-model end to end (residuals: freshness data +
Z3 certificates). -/
theorem plant_fan_mid_real
    (mv tg : Var 2) (g : Term (Var 2)) (fL : Fin 2 → Term (Var 2))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (plant_fan_midM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (plant_fan_midM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (plant_fan_midM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, plant_fan_midM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (plant_fan_midM.GdOf q) ν →
          BoxLe (Program.ode m.sys plant_fan_midM.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, plant_fan_mid_IR.R.modes[q]? = some pm → plant_fan_midM.modes[q]? = some m →
      GuardSettlingB plant_fan_midM.graph (realGdOf plant_fan_mid_IR plant_fan_midM)
        (realFieldOf plant_fan_mid_IR.R.stateVars pm 2) (Term.const 1)
        (realEnvOf plant_fan_mid_IR.R.stateVars 2 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) plant_fan_mid_meta.lam) (qOfInt plant_fan_midM.dtQ)).val
          * ((plant_fan_midM.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end_pad plant_fan_mid_IR plant_fan_mid_meta plant_fan_midM
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) (by decide)
    (by intro j hj; interval_cases j <;> decide)
    (fun j hj => sigmaOf_pos_lt (by decide) hj)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) plant_fan_mid_meta.lam)
          (qOfInt plant_fan_midM.dtQ) = (⟨10, 20⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide) (by decide) (by decide) (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, plant_fan_midM])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `refinement_ladder_rover_rung1_2to3`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem refinement_ladder_rover_rung1_2to3_real
    (mv tg : Var 2) (g : Term (Var 2)) (fL : Fin 2 → Term (Var 2))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (refinement_ladder_rover_rung1_2to3T.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (refinement_ladder_rover_rung1_2to3T.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (refinement_ladder_rover_rung1_2to3T.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, refinement_ladder_rover_rung1_2to3T.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (refinement_ladder_rover_rung1_2to3T.GdOf q) ν →
          BoxLe (Program.ode m.sys refinement_ladder_rover_rung1_2to3T.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, refinement_ladder_rover_rung1_2to3_IR.R.modes[q]? = some pm → refinement_ladder_rover_rung1_2to3T.core.modes[q]? = some m →
      GuardSettlingB refinement_ladder_rover_rung1_2to3T.core.graph (realGdOfT refinement_ladder_rover_rung1_2to3_IR refinement_ladder_rover_rung1_2to3_meta.scales refinement_ladder_rover_rung1_2to3T)
        (realFieldOf refinement_ladder_rover_rung1_2to3_IR.R.stateVars pm 2) (Term.const 1)
        (realEnvOf refinement_ladder_rover_rung1_2to3_IR.R.stateVars 2 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) refinement_ladder_rover_rung1_2to3_meta.lam) (qOfInt refinement_ladder_rover_rung1_2to3T.core.dtQ)).val
          * ((refinement_ladder_rover_rung1_2to3T.core.dt : ℤ) : ℝ)) q :=
  terrain_real_end_to_end refinement_ladder_rover_rung1_2to3_IR refinement_ladder_rover_rung1_2to3_meta refinement_ladder_rover_rung1_2to3T
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) refinement_ladder_rover_rung1_2to3_meta.lam)
          (qOfInt refinement_ladder_rover_rung1_2to3T.core.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, refinement_ladder_rover_rung1_2to3T])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `refinement_ladder_rover_rung2_3to6`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem refinement_ladder_rover_rung2_3to6_real
    (mv tg : Var 6) (g : Term (Var 6)) (fL : Fin 6 → Term (Var 6))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (refinement_ladder_rover_rung2_3to6T.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (refinement_ladder_rover_rung2_3to6T.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (refinement_ladder_rover_rung2_3to6T.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, refinement_ladder_rover_rung2_3to6T.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (refinement_ladder_rover_rung2_3to6T.GdOf q) ν →
          BoxLe (Program.ode m.sys refinement_ladder_rover_rung2_3to6T.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, refinement_ladder_rover_rung2_3to6_IR.R.modes[q]? = some pm → refinement_ladder_rover_rung2_3to6T.core.modes[q]? = some m →
      GuardSettlingB refinement_ladder_rover_rung2_3to6T.core.graph (realGdOfT refinement_ladder_rover_rung2_3to6_IR refinement_ladder_rover_rung2_3to6_meta.scales refinement_ladder_rover_rung2_3to6T)
        (realFieldOf refinement_ladder_rover_rung2_3to6_IR.R.stateVars pm 6) (Term.const 1)
        (realEnvOf refinement_ladder_rover_rung2_3to6_IR.R.stateVars 6 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) refinement_ladder_rover_rung2_3to6_meta.lam) (qOfInt refinement_ladder_rover_rung2_3to6T.core.dtQ)).val
          * ((refinement_ladder_rover_rung2_3to6T.core.dt : ℤ) : ℝ)) q :=
  terrain_real_end_to_end refinement_ladder_rover_rung2_3to6_IR refinement_ladder_rover_rung2_3to6_meta refinement_ladder_rover_rung2_3to6T
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) refinement_ladder_rover_rung2_3to6_meta.lam)
          (qOfInt refinement_ladder_rover_rung2_3to6T.core.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, refinement_ladder_rover_rung2_3to6T])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `refinement_ladder_rover_rung2_6dof`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem refinement_ladder_rover_rung2_6dof_real
    (mv tg : Var 4) (g : Term (Var 4)) (fL : Fin 4 → Term (Var 4))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (refinement_ladder_rover_rung2_6dofT.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (refinement_ladder_rover_rung2_6dofT.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (refinement_ladder_rover_rung2_6dofT.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, refinement_ladder_rover_rung2_6dofT.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (refinement_ladder_rover_rung2_6dofT.GdOf q) ν →
          BoxLe (Program.ode m.sys refinement_ladder_rover_rung2_6dofT.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, refinement_ladder_rover_rung2_6dof_IR.R.modes[q]? = some pm → refinement_ladder_rover_rung2_6dofT.core.modes[q]? = some m →
      GuardSettlingB refinement_ladder_rover_rung2_6dofT.core.graph (realGdOfT refinement_ladder_rover_rung2_6dof_IR refinement_ladder_rover_rung2_6dof_meta.scales refinement_ladder_rover_rung2_6dofT)
        (realFieldOf refinement_ladder_rover_rung2_6dof_IR.R.stateVars pm 4) (Term.const 1)
        (realEnvOf refinement_ladder_rover_rung2_6dof_IR.R.stateVars 4 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) refinement_ladder_rover_rung2_6dof_meta.lam) (qOfInt refinement_ladder_rover_rung2_6dofT.core.dtQ)).val
          * ((refinement_ladder_rover_rung2_6dofT.core.dt : ℤ) : ℝ)) q :=
  terrain_real_end_to_end refinement_ladder_rover_rung2_6dof_IR refinement_ladder_rover_rung2_6dof_meta refinement_ladder_rover_rung2_6dofT
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) refinement_ladder_rover_rung2_6dof_meta.lam)
          (qOfInt refinement_ladder_rover_rung2_6dofT.core.dtQ) = (⟨10, 30⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, refinement_ladder_rover_rung2_6dofT])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `refinement_ladder_rover_rung2b_6dof`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem refinement_ladder_rover_rung2b_6dof_real
    (mv tg : Var 6) (g : Term (Var 6)) (fL : Fin 6 → Term (Var 6))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (refinement_ladder_rover_rung2b_6dofT.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (refinement_ladder_rover_rung2b_6dofT.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (refinement_ladder_rover_rung2b_6dofT.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, refinement_ladder_rover_rung2b_6dofT.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (refinement_ladder_rover_rung2b_6dofT.GdOf q) ν →
          BoxLe (Program.ode m.sys refinement_ladder_rover_rung2b_6dofT.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, refinement_ladder_rover_rung2b_6dof_IR.R.modes[q]? = some pm → refinement_ladder_rover_rung2b_6dofT.core.modes[q]? = some m →
      GuardSettlingB refinement_ladder_rover_rung2b_6dofT.core.graph (realGdOfT refinement_ladder_rover_rung2b_6dof_IR refinement_ladder_rover_rung2b_6dof_meta.scales refinement_ladder_rover_rung2b_6dofT)
        (realFieldOf refinement_ladder_rover_rung2b_6dof_IR.R.stateVars pm 6) (Term.const 1)
        (realEnvOf refinement_ladder_rover_rung2b_6dof_IR.R.stateVars 6 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) refinement_ladder_rover_rung2b_6dof_meta.lam) (qOfInt refinement_ladder_rover_rung2b_6dofT.core.dtQ)).val
          * ((refinement_ladder_rover_rung2b_6dofT.core.dt : ℤ) : ℝ)) q :=
  terrain_real_end_to_end refinement_ladder_rover_rung2b_6dof_IR refinement_ladder_rover_rung2b_6dof_meta refinement_ladder_rover_rung2b_6dofT
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) refinement_ladder_rover_rung2b_6dof_meta.lam)
          (qOfInt refinement_ladder_rover_rung2b_6dofT.core.dtQ) = (⟨10, 30⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, refinement_ladder_rover_rung2b_6dofT])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `refinement_ladder_rover_rung2c_6dof`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem refinement_ladder_rover_rung2c_6dof_real
    (mv tg : Var 6) (g : Term (Var 6)) (fL : Fin 6 → Term (Var 6))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (refinement_ladder_rover_rung2c_6dofT.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (refinement_ladder_rover_rung2c_6dofT.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (refinement_ladder_rover_rung2c_6dofT.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, refinement_ladder_rover_rung2c_6dofT.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (refinement_ladder_rover_rung2c_6dofT.GdOf q) ν →
          BoxLe (Program.ode m.sys refinement_ladder_rover_rung2c_6dofT.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, refinement_ladder_rover_rung2c_6dof_IR.R.modes[q]? = some pm → refinement_ladder_rover_rung2c_6dofT.core.modes[q]? = some m →
      GuardSettlingB refinement_ladder_rover_rung2c_6dofT.core.graph (realGdOfT refinement_ladder_rover_rung2c_6dof_IR refinement_ladder_rover_rung2c_6dof_meta.scales refinement_ladder_rover_rung2c_6dofT)
        (realFieldOf refinement_ladder_rover_rung2c_6dof_IR.R.stateVars pm 6) (Term.const 1)
        (realEnvOf refinement_ladder_rover_rung2c_6dof_IR.R.stateVars 6 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) refinement_ladder_rover_rung2c_6dof_meta.lam) (qOfInt refinement_ladder_rover_rung2c_6dofT.core.dtQ)).val
          * ((refinement_ladder_rover_rung2c_6dofT.core.dt : ℤ) : ℝ)) q :=
  terrain_real_end_to_end refinement_ladder_rover_rung2c_6dof_IR refinement_ladder_rover_rung2c_6dof_meta refinement_ladder_rover_rung2c_6dofT
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) refinement_ladder_rover_rung2c_6dof_meta.lam)
          (qOfInt refinement_ladder_rover_rung2c_6dofT.core.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, refinement_ladder_rover_rung2c_6dofT])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `refinement_ladder_rover_rung3_6to8`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem refinement_ladder_rover_rung3_6to8_real
    (mv tg : Var 8) (g : Term (Var 8)) (fL : Fin 8 → Term (Var 8))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (refinement_ladder_rover_rung3_6to8T.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (refinement_ladder_rover_rung3_6to8T.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (refinement_ladder_rover_rung3_6to8T.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, refinement_ladder_rover_rung3_6to8T.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (refinement_ladder_rover_rung3_6to8T.GdOf q) ν →
          BoxLe (Program.ode m.sys refinement_ladder_rover_rung3_6to8T.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, refinement_ladder_rover_rung3_6to8_IR.R.modes[q]? = some pm → refinement_ladder_rover_rung3_6to8T.core.modes[q]? = some m →
      GuardSettlingB refinement_ladder_rover_rung3_6to8T.core.graph (realGdOfT refinement_ladder_rover_rung3_6to8_IR refinement_ladder_rover_rung3_6to8_meta.scales refinement_ladder_rover_rung3_6to8T)
        (realFieldOf refinement_ladder_rover_rung3_6to8_IR.R.stateVars pm 8) (Term.const 1)
        (realEnvOf refinement_ladder_rover_rung3_6to8_IR.R.stateVars 8 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) refinement_ladder_rover_rung3_6to8_meta.lam) (qOfInt refinement_ladder_rover_rung3_6to8T.core.dtQ)).val
          * ((refinement_ladder_rover_rung3_6to8T.core.dt : ℤ) : ℝ)) q :=
  terrain_real_end_to_end refinement_ladder_rover_rung3_6to8_IR refinement_ladder_rover_rung3_6to8_meta refinement_ladder_rover_rung3_6to8T
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) refinement_ladder_rover_rung3_6to8_meta.lam)
          (qOfInt refinement_ladder_rover_rung3_6to8T.core.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, refinement_ladder_rover_rung3_6to8T])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `refinement_ladder_rover_rung4_8to12`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem refinement_ladder_rover_rung4_8to12_real
    (mv tg : Var 12) (g : Term (Var 12)) (fL : Fin 12 → Term (Var 12))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (refinement_ladder_rover_rung4_8to12T.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (refinement_ladder_rover_rung4_8to12T.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (refinement_ladder_rover_rung4_8to12T.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, refinement_ladder_rover_rung4_8to12T.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (refinement_ladder_rover_rung4_8to12T.GdOf q) ν →
          BoxLe (Program.ode m.sys refinement_ladder_rover_rung4_8to12T.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, refinement_ladder_rover_rung4_8to12_IR.R.modes[q]? = some pm → refinement_ladder_rover_rung4_8to12T.core.modes[q]? = some m →
      GuardSettlingB refinement_ladder_rover_rung4_8to12T.core.graph (realGdOfT refinement_ladder_rover_rung4_8to12_IR refinement_ladder_rover_rung4_8to12_meta.scales refinement_ladder_rover_rung4_8to12T)
        (realFieldOf refinement_ladder_rover_rung4_8to12_IR.R.stateVars pm 12) (Term.const 1)
        (realEnvOf refinement_ladder_rover_rung4_8to12_IR.R.stateVars 12 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) refinement_ladder_rover_rung4_8to12_meta.lam) (qOfInt refinement_ladder_rover_rung4_8to12T.core.dtQ)).val
          * ((refinement_ladder_rover_rung4_8to12T.core.dt : ℤ) : ℝ)) q :=
  terrain_real_end_to_end refinement_ladder_rover_rung4_8to12_IR refinement_ladder_rover_rung4_8to12_meta refinement_ladder_rover_rung4_8to12T
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) refinement_ladder_rover_rung4_8to12_meta.lam)
          (qOfInt refinement_ladder_rover_rung4_8to12T.core.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, refinement_ladder_rover_rung4_8to12T])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `robot_braking`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem robot_braking_real
    (mv tg : Var 1) (g : Term (Var 1)) (fL : Fin 1 → Term (Var 1))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (robot_brakingM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (robot_brakingM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (robot_brakingM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, robot_brakingM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (robot_brakingM.GdOf q) ν →
          BoxLe (Program.ode m.sys robot_brakingM.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, robot_braking_IR.R.modes[q]? = some pm → robot_brakingM.modes[q]? = some m →
      GuardSettlingB robot_brakingM.graph (realGdOf robot_braking_IR robot_brakingM)
        (realFieldOf robot_braking_IR.R.stateVars pm 1) (Term.const 1)
        (realEnvOf robot_braking_IR.R.stateVars 1 pm)
        ((qDiv (qDiv (⟨20, 10⟩ : QF) robot_braking_meta.lam) (qOfInt robot_brakingM.dtQ)).val
          * ((robot_brakingM.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end robot_braking_IR robot_braking_meta robot_brakingM
    (εR := ⟨20, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨20, 10⟩ : QF) robot_braking_meta.lam)
          (qOfInt robot_brakingM.dtQ) = (⟨20, 20⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, robot_brakingM])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `rover3_M1`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem rover3_M1_real
    (mv tg : Var 2) (g : Term (Var 2)) (fL : Fin 2 → Term (Var 2))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (rover3_M1M.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (rover3_M1M.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (rover3_M1M.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, rover3_M1M.graph.modeAt q = some m →
        ∀ ν, Formula.sat (rover3_M1M.GdOf q) ν →
          BoxLe (Program.ode m.sys rover3_M1M.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, rover3_M1_IR.R.modes[q]? = some pm → rover3_M1M.modes[q]? = some m →
      GuardSettlingB rover3_M1M.graph (realGdOf rover3_M1_IR rover3_M1M)
        (realFieldOf rover3_M1_IR.R.stateVars pm 2) (Term.const 1)
        (realEnvOf rover3_M1_IR.R.stateVars 2 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) rover3_M1_meta.lam) (qOfInt rover3_M1M.dtQ)).val
          * ((rover3_M1M.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end rover3_M1_IR rover3_M1_meta rover3_M1M
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) rover3_M1_meta.lam)
          (qOfInt rover3_M1M.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, rover3_M1M])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `rover3tier_M1`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem rover3tier_M1_real
    (mv tg : Var 2) (g : Term (Var 2)) (fL : Fin 2 → Term (Var 2))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (rover3tier_M1M.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (rover3tier_M1M.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (rover3tier_M1M.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, rover3tier_M1M.graph.modeAt q = some m →
        ∀ ν, Formula.sat (rover3tier_M1M.GdOf q) ν →
          BoxLe (Program.ode m.sys rover3tier_M1M.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, rover3tier_M1_IR.R.modes[q]? = some pm → rover3tier_M1M.modes[q]? = some m →
      GuardSettlingB rover3tier_M1M.graph (realGdOf rover3tier_M1_IR rover3tier_M1M)
        (realFieldOf rover3tier_M1_IR.R.stateVars pm 2) (Term.const 1)
        (realEnvOf rover3tier_M1_IR.R.stateVars 2 pm)
        ((qDiv (qDiv (⟨3, 10⟩ : QF) rover3tier_M1_meta.lam) (qOfInt rover3tier_M1M.dtQ)).val
          * ((rover3tier_M1M.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end rover3tier_M1_IR rover3tier_M1_meta rover3tier_M1M
    (εR := ⟨3, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨3, 10⟩ : QF) rover3tier_M1_meta.lam)
          (qOfInt rover3tier_M1M.dtQ) = (⟨3, 150⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, rover3tier_M1M])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `rover3tier_rung12`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem rover3tier_rung12_real
    (mv tg : Var 3) (g : Term (Var 3)) (fL : Fin 3 → Term (Var 3))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (rover3tier_rung12A.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (rover3tier_rung12A.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (rover3tier_rung12A.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, rover3tier_rung12A.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (rover3tier_rung12A.GdOf q) ν →
          BoxLe (Program.ode m.sys rover3tier_rung12A.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, rover3tier_rung12_IR.R.modes[q]? = some pm → rover3tier_rung12A.core.modes[q]? = some m →
      GuardSettlingB rover3tier_rung12A.core.graph (realGdOfA rover3tier_rung12_IR rover3tier_rung12_meta.scales rover3tier_rung12A)
        (realFieldOf rover3tier_rung12_IR.R.stateVars pm 3) (Term.const 1)
        (realEnvOf rover3tier_rung12_IR.R.stateVars 3 pm)
        ((qDiv (qDiv (⟨3, 10⟩ : QF) rover3tier_rung12_meta.lam) (qOfInt rover3tier_rung12A.core.dtQ)).val
          * ((rover3tier_rung12A.core.dt : ℤ) : ℝ)) q :=
  affine_real_end_to_end rover3tier_rung12_IR rover3tier_rung12_meta rover3tier_rung12A
    (εR := ⟨3, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨3, 10⟩ : QF) rover3tier_rung12_meta.lam)
          (qOfInt rover3tier_rung12A.core.dtQ) = (⟨3, 30⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, rover3tier_rung12A])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `rover_4d_box`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem rover_4d_box_real
    (mv tg : Var 4) (g : Term (Var 4)) (fL : Fin 4 → Term (Var 4))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (rover_4d_boxM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (rover_4d_boxM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (rover_4d_boxM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, rover_4d_boxM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (rover_4d_boxM.GdOf q) ν →
          BoxLe (Program.ode m.sys rover_4d_boxM.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, rover_4d_box_IR.R.modes[q]? = some pm → rover_4d_boxM.modes[q]? = some m →
      GuardSettlingB rover_4d_boxM.graph (realGdOf rover_4d_box_IR rover_4d_boxM)
        (realFieldOf rover_4d_box_IR.R.stateVars pm 4) (Term.const 1)
        (realEnvOf rover_4d_box_IR.R.stateVars 4 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) rover_4d_box_meta.lam) (qOfInt rover_4d_boxM.dtQ)).val
          * ((rover_4d_boxM.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end rover_4d_box_IR rover_4d_box_meta rover_4d_boxM
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) rover_4d_box_meta.lam)
          (qOfInt rover_4d_boxM.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, rover_4d_boxM])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `rover_attitude_cone_12dof`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem rover_attitude_cone_12dof_real
    (mv tg : Var 12) (g : Term (Var 12)) (fL : Fin 12 → Term (Var 12))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (rover_attitude_cone_12dofT.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (rover_attitude_cone_12dofT.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (rover_attitude_cone_12dofT.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, rover_attitude_cone_12dofT.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (rover_attitude_cone_12dofT.GdOf q) ν →
          BoxLe (Program.ode m.sys rover_attitude_cone_12dofT.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, rover_attitude_cone_12dof_IR.R.modes[q]? = some pm → rover_attitude_cone_12dofT.core.modes[q]? = some m →
      GuardSettlingB rover_attitude_cone_12dofT.core.graph (realGdOfT rover_attitude_cone_12dof_IR rover_attitude_cone_12dof_meta.scales rover_attitude_cone_12dofT)
        (realFieldOf rover_attitude_cone_12dof_IR.R.stateVars pm 12) (Term.const 1)
        (realEnvOf rover_attitude_cone_12dof_IR.R.stateVars 12 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) rover_attitude_cone_12dof_meta.lam) (qOfInt rover_attitude_cone_12dofT.core.dtQ)).val
          * ((rover_attitude_cone_12dofT.core.dt : ℤ) : ℝ)) q :=
  terrain_real_end_to_end rover_attitude_cone_12dof_IR rover_attitude_cone_12dof_meta rover_attitude_cone_12dofT
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) rover_attitude_cone_12dof_meta.lam)
          (qOfInt rover_attitude_cone_12dofT.core.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, rover_attitude_cone_12dofT])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `rover_coupled`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem rover_coupled_real
    (mv tg : Var 4) (g : Term (Var 4)) (fL : Fin 4 → Term (Var 4))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (rover_coupledM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (rover_coupledM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (rover_coupledM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, rover_coupledM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (rover_coupledM.GdOf q) ν →
          BoxLe (Program.ode m.sys rover_coupledM.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, rover_coupled_IR.R.modes[q]? = some pm → rover_coupledM.modes[q]? = some m →
      GuardSettlingB rover_coupledM.graph (realGdOf rover_coupled_IR rover_coupledM)
        (realFieldOf rover_coupled_IR.R.stateVars pm 4) (Term.const 1)
        (realEnvOf rover_coupled_IR.R.stateVars 4 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) rover_coupled_meta.lam) (qOfInt rover_coupledM.dtQ)).val
          * ((rover_coupledM.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end rover_coupled_IR rover_coupled_meta rover_coupledM
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) rover_coupled_meta.lam)
          (qOfInt rover_coupledM.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, rover_coupledM])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `rover_dof_terrain_rung1`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem rover_dof_terrain_rung1_real
    (mv tg : Var 3) (g : Term (Var 3)) (fL : Fin 3 → Term (Var 3))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (rover_dof_terrain_rung1T.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (rover_dof_terrain_rung1T.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (rover_dof_terrain_rung1T.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, rover_dof_terrain_rung1T.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (rover_dof_terrain_rung1T.GdOf q) ν →
          BoxLe (Program.ode m.sys rover_dof_terrain_rung1T.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, rover_dof_terrain_rung1_IR.R.modes[q]? = some pm → rover_dof_terrain_rung1T.core.modes[q]? = some m →
      GuardSettlingB rover_dof_terrain_rung1T.core.graph (realGdOfT rover_dof_terrain_rung1_IR rover_dof_terrain_rung1_meta.scales rover_dof_terrain_rung1T)
        (realFieldOf rover_dof_terrain_rung1_IR.R.stateVars pm 3) (Term.const 1)
        (realEnvOf rover_dof_terrain_rung1_IR.R.stateVars 3 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) rover_dof_terrain_rung1_meta.lam) (qOfInt rover_dof_terrain_rung1T.core.dtQ)).val
          * ((rover_dof_terrain_rung1T.core.dt : ℤ) : ℝ)) q :=
  terrain_real_end_to_end rover_dof_terrain_rung1_IR rover_dof_terrain_rung1_meta rover_dof_terrain_rung1T
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) rover_dof_terrain_rung1_meta.lam)
          (qOfInt rover_dof_terrain_rung1T.core.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, rover_dof_terrain_rung1T])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `rover_dof_terrain_rung2`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem rover_dof_terrain_rung2_real
    (mv tg : Var 6) (g : Term (Var 6)) (fL : Fin 6 → Term (Var 6))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (rover_dof_terrain_rung2T.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (rover_dof_terrain_rung2T.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (rover_dof_terrain_rung2T.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, rover_dof_terrain_rung2T.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (rover_dof_terrain_rung2T.GdOf q) ν →
          BoxLe (Program.ode m.sys rover_dof_terrain_rung2T.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, rover_dof_terrain_rung2_IR.R.modes[q]? = some pm → rover_dof_terrain_rung2T.core.modes[q]? = some m →
      GuardSettlingB rover_dof_terrain_rung2T.core.graph (realGdOfT rover_dof_terrain_rung2_IR rover_dof_terrain_rung2_meta.scales rover_dof_terrain_rung2T)
        (realFieldOf rover_dof_terrain_rung2_IR.R.stateVars pm 6) (Term.const 1)
        (realEnvOf rover_dof_terrain_rung2_IR.R.stateVars 6 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) rover_dof_terrain_rung2_meta.lam) (qOfInt rover_dof_terrain_rung2T.core.dtQ)).val
          * ((rover_dof_terrain_rung2T.core.dt : ℤ) : ℝ)) q :=
  terrain_real_end_to_end rover_dof_terrain_rung2_IR rover_dof_terrain_rung2_meta rover_dof_terrain_rung2T
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) rover_dof_terrain_rung2_meta.lam)
          (qOfInt rover_dof_terrain_rung2T.core.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, rover_dof_terrain_rung2T])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `rover_dof_terrain_rung3`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem rover_dof_terrain_rung3_real
    (mv tg : Var 12) (g : Term (Var 12)) (fL : Fin 12 → Term (Var 12))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (rover_dof_terrain_rung3T.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (rover_dof_terrain_rung3T.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (rover_dof_terrain_rung3T.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, rover_dof_terrain_rung3T.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (rover_dof_terrain_rung3T.GdOf q) ν →
          BoxLe (Program.ode m.sys rover_dof_terrain_rung3T.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, rover_dof_terrain_rung3_IR.R.modes[q]? = some pm → rover_dof_terrain_rung3T.core.modes[q]? = some m →
      GuardSettlingB rover_dof_terrain_rung3T.core.graph (realGdOfT rover_dof_terrain_rung3_IR rover_dof_terrain_rung3_meta.scales rover_dof_terrain_rung3T)
        (realFieldOf rover_dof_terrain_rung3_IR.R.stateVars pm 12) (Term.const 1)
        (realEnvOf rover_dof_terrain_rung3_IR.R.stateVars 12 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) rover_dof_terrain_rung3_meta.lam) (qOfInt rover_dof_terrain_rung3T.core.dtQ)).val
          * ((rover_dof_terrain_rung3T.core.dt : ℤ) : ℝ)) q :=
  terrain_real_end_to_end rover_dof_terrain_rung3_IR rover_dof_terrain_rung3_meta rover_dof_terrain_rung3T
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) rover_dof_terrain_rung3_meta.lam)
          (qOfInt rover_dof_terrain_rung3T.core.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, rover_dof_terrain_rung3T])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `rover_dof_terrain_rung3_8d`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem rover_dof_terrain_rung3_8d_real
    (mv tg : Var 8) (g : Term (Var 8)) (fL : Fin 8 → Term (Var 8))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (rover_dof_terrain_rung3_8dT.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (rover_dof_terrain_rung3_8dT.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (rover_dof_terrain_rung3_8dT.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, rover_dof_terrain_rung3_8dT.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (rover_dof_terrain_rung3_8dT.GdOf q) ν →
          BoxLe (Program.ode m.sys rover_dof_terrain_rung3_8dT.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, rover_dof_terrain_rung3_8d_IR.R.modes[q]? = some pm → rover_dof_terrain_rung3_8dT.core.modes[q]? = some m →
      GuardSettlingB rover_dof_terrain_rung3_8dT.core.graph (realGdOfT rover_dof_terrain_rung3_8d_IR rover_dof_terrain_rung3_8d_meta.scales rover_dof_terrain_rung3_8dT)
        (realFieldOf rover_dof_terrain_rung3_8d_IR.R.stateVars pm 8) (Term.const 1)
        (realEnvOf rover_dof_terrain_rung3_8d_IR.R.stateVars 8 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) rover_dof_terrain_rung3_8d_meta.lam) (qOfInt rover_dof_terrain_rung3_8dT.core.dtQ)).val
          * ((rover_dof_terrain_rung3_8dT.core.dt : ℤ) : ℝ)) q :=
  terrain_real_end_to_end rover_dof_terrain_rung3_8d_IR rover_dof_terrain_rung3_8d_meta rover_dof_terrain_rung3_8dT
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) rover_dof_terrain_rung3_8d_meta.lam)
          (qOfInt rover_dof_terrain_rung3_8dT.core.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, rover_dof_terrain_rung3_8dT])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `rover_drag`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem rover_drag_real
    (mv tg : Var 1) (g : Term (Var 1)) (fL : Fin 1 → Term (Var 1))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (rover_dragM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (rover_dragM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (rover_dragM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, rover_dragM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (rover_dragM.GdOf q) ν →
          BoxLe (Program.ode m.sys rover_dragM.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, rover_drag_IR.R.modes[q]? = some pm → rover_dragM.modes[q]? = some m →
      GuardSettlingB rover_dragM.graph (realGdOf rover_drag_IR rover_dragM)
        (realFieldOf rover_drag_IR.R.stateVars pm 1) (Term.const 1)
        (realEnvOf rover_drag_IR.R.stateVars 1 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) rover_drag_meta.lam) (qOfInt rover_dragM.dtQ)).val
          * ((rover_dragM.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end rover_drag_IR rover_drag_meta rover_dragM
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) rover_drag_meta.lam)
          (qOfInt rover_dragM.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, rover_dragM])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `rover_position`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem rover_position_real
    (mv tg : Var 4) (g : Term (Var 4)) (fL : Fin 4 → Term (Var 4))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (rover_positionM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (rover_positionM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (rover_positionM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, rover_positionM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (rover_positionM.GdOf q) ν →
          BoxLe (Program.ode m.sys rover_positionM.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, rover_position_IR.R.modes[q]? = some pm → rover_positionM.modes[q]? = some m →
      GuardSettlingB rover_positionM.graph (realGdOf rover_position_IR rover_positionM)
        (realFieldOf rover_position_IR.R.stateVars pm 4) (Term.const 1)
        (realEnvOf rover_position_IR.R.stateVars 4 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) rover_position_meta.lam) (qOfInt rover_positionM.dtQ)).val
          * ((rover_positionM.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end rover_position_IR rover_position_meta rover_positionM
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) rover_position_meta.lam)
          (qOfInt rover_positionM.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, rover_positionM])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `rover_terrain_M1`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem rover_terrain_M1_real
    (mv tg : Var 2) (g : Term (Var 2)) (fL : Fin 2 → Term (Var 2))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (rover_terrain_M1M.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (rover_terrain_M1M.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (rover_terrain_M1M.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, rover_terrain_M1M.graph.modeAt q = some m →
        ∀ ν, Formula.sat (rover_terrain_M1M.GdOf q) ν →
          BoxLe (Program.ode m.sys rover_terrain_M1M.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, rover_terrain_M1_IR.R.modes[q]? = some pm → rover_terrain_M1M.modes[q]? = some m →
      GuardSettlingB rover_terrain_M1M.graph (realGdOf rover_terrain_M1_IR rover_terrain_M1M)
        (realFieldOf rover_terrain_M1_IR.R.stateVars pm 2) (Term.const 1)
        (realEnvOf rover_terrain_M1_IR.R.stateVars 2 pm)
        ((qDiv (qDiv (⟨5, 10⟩ : QF) rover_terrain_M1_meta.lam) (qOfInt rover_terrain_M1M.dtQ)).val
          * ((rover_terrain_M1M.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end rover_terrain_M1_IR rover_terrain_M1_meta rover_terrain_M1M
    (εR := ⟨5, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨5, 10⟩ : QF) rover_terrain_M1_meta.lam)
          (qOfInt rover_terrain_M1M.dtQ) = (⟨5, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, rover_terrain_M1M])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `rover_tier_r1`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem rover_tier_r1_real
    (mv tg : Var 3) (g : Term (Var 3)) (fL : Fin 3 → Term (Var 3))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (rover_tier_r1A.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (rover_tier_r1A.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (rover_tier_r1A.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, rover_tier_r1A.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (rover_tier_r1A.GdOf q) ν →
          BoxLe (Program.ode m.sys rover_tier_r1A.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, rover_tier_r1_IR.R.modes[q]? = some pm → rover_tier_r1A.core.modes[q]? = some m →
      GuardSettlingB rover_tier_r1A.core.graph (realGdOfA rover_tier_r1_IR rover_tier_r1_meta.scales rover_tier_r1A)
        (realFieldOf rover_tier_r1_IR.R.stateVars pm 3) (Term.const 1)
        (realEnvOf rover_tier_r1_IR.R.stateVars 3 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) rover_tier_r1_meta.lam) (qOfInt rover_tier_r1A.core.dtQ)).val
          * ((rover_tier_r1A.core.dt : ℤ) : ℝ)) q :=
  affine_real_end_to_end rover_tier_r1_IR rover_tier_r1_meta rover_tier_r1A
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) rover_tier_r1_meta.lam)
          (qOfInt rover_tier_r1A.core.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, rover_tier_r1A])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `story1_attdist_rung_a_6to8`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem story1_attdist_rung_a_6to8_real
    (mv tg : Var 8) (g : Term (Var 8)) (fL : Fin 8 → Term (Var 8))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (story1_attdist_rung_a_6to8T.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (story1_attdist_rung_a_6to8T.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (story1_attdist_rung_a_6to8T.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, story1_attdist_rung_a_6to8T.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (story1_attdist_rung_a_6to8T.GdOf q) ν →
          BoxLe (Program.ode m.sys story1_attdist_rung_a_6to8T.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, story1_attdist_rung_a_6to8_IR.R.modes[q]? = some pm → story1_attdist_rung_a_6to8T.core.modes[q]? = some m →
      GuardSettlingB story1_attdist_rung_a_6to8T.core.graph (realGdOfT story1_attdist_rung_a_6to8_IR story1_attdist_rung_a_6to8_meta.scales story1_attdist_rung_a_6to8T)
        (realFieldOf story1_attdist_rung_a_6to8_IR.R.stateVars pm 8) (Term.const 1)
        (realEnvOf story1_attdist_rung_a_6to8_IR.R.stateVars 8 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) story1_attdist_rung_a_6to8_meta.lam) (qOfInt story1_attdist_rung_a_6to8T.core.dtQ)).val
          * ((story1_attdist_rung_a_6to8T.core.dt : ℤ) : ℝ)) q :=
  terrain_real_end_to_end story1_attdist_rung_a_6to8_IR story1_attdist_rung_a_6to8_meta story1_attdist_rung_a_6to8T
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) story1_attdist_rung_a_6to8_meta.lam)
          (qOfInt story1_attdist_rung_a_6to8T.core.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, story1_attdist_rung_a_6to8T])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `story1_attdist_rung_b_12dof`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem story1_attdist_rung_b_12dof_real
    (mv tg : Var 12) (g : Term (Var 12)) (fL : Fin 12 → Term (Var 12))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (story1_attdist_rung_b_12dofT.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (story1_attdist_rung_b_12dofT.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (story1_attdist_rung_b_12dofT.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, story1_attdist_rung_b_12dofT.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (story1_attdist_rung_b_12dofT.GdOf q) ν →
          BoxLe (Program.ode m.sys story1_attdist_rung_b_12dofT.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, story1_attdist_rung_b_12dof_IR.R.modes[q]? = some pm → story1_attdist_rung_b_12dofT.core.modes[q]? = some m →
      GuardSettlingB story1_attdist_rung_b_12dofT.core.graph (realGdOfT story1_attdist_rung_b_12dof_IR story1_attdist_rung_b_12dof_meta.scales story1_attdist_rung_b_12dofT)
        (realFieldOf story1_attdist_rung_b_12dof_IR.R.stateVars pm 12) (Term.const 1)
        (realEnvOf story1_attdist_rung_b_12dof_IR.R.stateVars 12 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) story1_attdist_rung_b_12dof_meta.lam) (qOfInt story1_attdist_rung_b_12dofT.core.dtQ)).val
          * ((story1_attdist_rung_b_12dofT.core.dt : ℤ) : ℝ)) q :=
  terrain_real_end_to_end story1_attdist_rung_b_12dof_IR story1_attdist_rung_b_12dof_meta story1_attdist_rung_b_12dofT
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) story1_attdist_rung_b_12dof_meta.lam)
          (qOfInt story1_attdist_rung_b_12dofT.core.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, story1_attdist_rung_b_12dofT])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `story2_lateral_rung_a_8dof`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem story2_lateral_rung_a_8dof_real
    (mv tg : Var 8) (g : Term (Var 8)) (fL : Fin 8 → Term (Var 8))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (story2_lateral_rung_a_8dofT.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (story2_lateral_rung_a_8dofT.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (story2_lateral_rung_a_8dofT.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, story2_lateral_rung_a_8dofT.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (story2_lateral_rung_a_8dofT.GdOf q) ν →
          BoxLe (Program.ode m.sys story2_lateral_rung_a_8dofT.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, story2_lateral_rung_a_8dof_IR.R.modes[q]? = some pm → story2_lateral_rung_a_8dofT.core.modes[q]? = some m →
      GuardSettlingB story2_lateral_rung_a_8dofT.core.graph (realGdOfT story2_lateral_rung_a_8dof_IR story2_lateral_rung_a_8dof_meta.scales story2_lateral_rung_a_8dofT)
        (realFieldOf story2_lateral_rung_a_8dof_IR.R.stateVars pm 8) (Term.const 1)
        (realEnvOf story2_lateral_rung_a_8dof_IR.R.stateVars 8 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) story2_lateral_rung_a_8dof_meta.lam) (qOfInt story2_lateral_rung_a_8dofT.core.dtQ)).val
          * ((story2_lateral_rung_a_8dofT.core.dt : ℤ) : ℝ)) q :=
  terrain_real_end_to_end story2_lateral_rung_a_8dof_IR story2_lateral_rung_a_8dof_meta story2_lateral_rung_a_8dofT
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) story2_lateral_rung_a_8dof_meta.lam)
          (qOfInt story2_lateral_rung_a_8dofT.core.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, story2_lateral_rung_a_8dofT])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `story2_lateral_rung_b_12dof`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem story2_lateral_rung_b_12dof_real
    (mv tg : Var 12) (g : Term (Var 12)) (fL : Fin 12 → Term (Var 12))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (story2_lateral_rung_b_12dofT.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (story2_lateral_rung_b_12dofT.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (story2_lateral_rung_b_12dofT.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, story2_lateral_rung_b_12dofT.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (story2_lateral_rung_b_12dofT.GdOf q) ν →
          BoxLe (Program.ode m.sys story2_lateral_rung_b_12dofT.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, story2_lateral_rung_b_12dof_IR.R.modes[q]? = some pm → story2_lateral_rung_b_12dofT.core.modes[q]? = some m →
      GuardSettlingB story2_lateral_rung_b_12dofT.core.graph (realGdOfT story2_lateral_rung_b_12dof_IR story2_lateral_rung_b_12dof_meta.scales story2_lateral_rung_b_12dofT)
        (realFieldOf story2_lateral_rung_b_12dof_IR.R.stateVars pm 12) (Term.const 1)
        (realEnvOf story2_lateral_rung_b_12dof_IR.R.stateVars 12 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) story2_lateral_rung_b_12dof_meta.lam) (qOfInt story2_lateral_rung_b_12dofT.core.dtQ)).val
          * ((story2_lateral_rung_b_12dofT.core.dt : ℤ) : ℝ)) q :=
  terrain_real_end_to_end story2_lateral_rung_b_12dof_IR story2_lateral_rung_b_12dof_meta story2_lateral_rung_b_12dofT
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) story2_lateral_rung_b_12dof_meta.lam)
          (qOfInt story2_lateral_rung_b_12dofT.core.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, story2_lateral_rung_b_12dofT])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `story3_rollover_base_12dof`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem story3_rollover_base_12dof_real
    (mv tg : Var 12) (g : Term (Var 12)) (fL : Fin 12 → Term (Var 12))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (story3_rollover_base_12dofT.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (story3_rollover_base_12dofT.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (story3_rollover_base_12dofT.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, story3_rollover_base_12dofT.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (story3_rollover_base_12dofT.GdOf q) ν →
          BoxLe (Program.ode m.sys story3_rollover_base_12dofT.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, story3_rollover_base_12dof_IR.R.modes[q]? = some pm → story3_rollover_base_12dofT.core.modes[q]? = some m →
      GuardSettlingB story3_rollover_base_12dofT.core.graph (realGdOfT story3_rollover_base_12dof_IR story3_rollover_base_12dof_meta.scales story3_rollover_base_12dofT)
        (realFieldOf story3_rollover_base_12dof_IR.R.stateVars pm 12) (Term.const 1)
        (realEnvOf story3_rollover_base_12dof_IR.R.stateVars 12 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) story3_rollover_base_12dof_meta.lam) (qOfInt story3_rollover_base_12dofT.core.dtQ)).val
          * ((story3_rollover_base_12dofT.core.dt : ℤ) : ℝ)) q :=
  terrain_real_end_to_end story3_rollover_base_12dof_IR story3_rollover_base_12dof_meta story3_rollover_base_12dofT
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) story3_rollover_base_12dof_meta.lam)
          (qOfInt story3_rollover_base_12dofT.core.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, story3_rollover_base_12dofT])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `story3_rollover_ladder_rung_a`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem story3_rollover_ladder_rung_a_real
    (mv tg : Var 12) (g : Term (Var 12)) (fL : Fin 12 → Term (Var 12))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (story3_rollover_ladder_rung_aT.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (story3_rollover_ladder_rung_aT.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (story3_rollover_ladder_rung_aT.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, story3_rollover_ladder_rung_aT.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (story3_rollover_ladder_rung_aT.GdOf q) ν →
          BoxLe (Program.ode m.sys story3_rollover_ladder_rung_aT.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, story3_rollover_ladder_rung_a_IR.R.modes[q]? = some pm → story3_rollover_ladder_rung_aT.core.modes[q]? = some m →
      GuardSettlingB story3_rollover_ladder_rung_aT.core.graph (realGdOfT story3_rollover_ladder_rung_a_IR story3_rollover_ladder_rung_a_meta.scales story3_rollover_ladder_rung_aT)
        (realFieldOf story3_rollover_ladder_rung_a_IR.R.stateVars pm 12) (Term.const 1)
        (realEnvOf story3_rollover_ladder_rung_a_IR.R.stateVars 12 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) story3_rollover_ladder_rung_a_meta.lam) (qOfInt story3_rollover_ladder_rung_aT.core.dtQ)).val
          * ((story3_rollover_ladder_rung_aT.core.dt : ℤ) : ℝ)) q :=
  terrain_real_end_to_end story3_rollover_ladder_rung_a_IR story3_rollover_ladder_rung_a_meta story3_rollover_ladder_rung_aT
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) story3_rollover_ladder_rung_a_meta.lam)
          (qOfInt story3_rollover_ladder_rung_aT.core.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, story3_rollover_ladder_rung_aT])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `story3_rollover_ladder_rung_b`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem story3_rollover_ladder_rung_b_real
    (mv tg : Var 12) (g : Term (Var 12)) (fL : Fin 12 → Term (Var 12))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (story3_rollover_ladder_rung_bT.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (story3_rollover_ladder_rung_bT.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (story3_rollover_ladder_rung_bT.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, story3_rollover_ladder_rung_bT.core.graph.modeAt q = some m →
        ∀ ν, Formula.sat (story3_rollover_ladder_rung_bT.GdOf q) ν →
          BoxLe (Program.ode m.sys story3_rollover_ladder_rung_bT.core.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, story3_rollover_ladder_rung_b_IR.R.modes[q]? = some pm → story3_rollover_ladder_rung_bT.core.modes[q]? = some m →
      GuardSettlingB story3_rollover_ladder_rung_bT.core.graph (realGdOfT story3_rollover_ladder_rung_b_IR story3_rollover_ladder_rung_b_meta.scales story3_rollover_ladder_rung_bT)
        (realFieldOf story3_rollover_ladder_rung_b_IR.R.stateVars pm 12) (Term.const 1)
        (realEnvOf story3_rollover_ladder_rung_b_IR.R.stateVars 12 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) story3_rollover_ladder_rung_b_meta.lam) (qOfInt story3_rollover_ladder_rung_bT.core.dtQ)).val
          * ((story3_rollover_ladder_rung_bT.core.dt : ℤ) : ℝ)) q :=
  terrain_real_end_to_end story3_rollover_ladder_rung_b_IR story3_rollover_ladder_rung_b_meta story3_rollover_ladder_rung_bT
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) story3_rollover_ladder_rung_b_meta.lam)
          (qOfInt story3_rollover_ladder_rung_bT.core.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, story3_rollover_ladder_rung_bT])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

/-- `watertank`: real-model end to end (residuals: freshness data + Z3 certificates). -/
theorem watertank_real
    (mv tg : Var 1) (g : Term (Var 1)) (fL : Fin 1 → Term (Var 1))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (watertankSuiteM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (watertankSuiteM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (watertankSuiteM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, watertankSuiteM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (watertankSuiteM.GdOf q) ν →
          BoxLe (Program.ode m.sys watertankSuiteM.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, watertank_IR.R.modes[q]? = some pm → watertankSuiteM.modes[q]? = some m →
      GuardSettlingB watertankSuiteM.graph (realGdOf watertank_IR watertankSuiteM)
        (realFieldOf watertank_IR.R.stateVars pm 1) (Term.const 1)
        (realEnvOf watertank_IR.R.stateVars 1 pm)
        ((qDiv (qDiv (⟨10, 10⟩ : QF) watertankSuite_meta.lam) (qOfInt watertankSuiteM.dtQ)).val
          * ((watertankSuiteM.dt : ℤ) : ℝ)) q :=
  settling_real_end_to_end watertank_IR watertankSuite_meta watertankSuiteM
    (εR := ⟨10, 10⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨10, 10⟩ : QF) watertankSuite_meta.lam)
          (qOfInt watertankSuiteM.dtQ) = (⟨10, 10⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, watertankSuiteM])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert

end RelCertifier
