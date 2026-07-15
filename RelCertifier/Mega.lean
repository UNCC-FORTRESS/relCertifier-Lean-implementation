/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The per-benchmark mega-theorem (arm_refinement): fidelity ∧ settling, one term

Bundles the whole checker-side pipeline for one benchmark into a single theorem whose
only hypotheses are the pipeline's designed residuals:

  (1) `faithfulSettling … = true`  — the certified instance IS the parsed benchmark
      file's image under the declared scales (kernel `rfl`, against the parser-emitted
      IR literal; the runtime battery pins literal == file);
  (2) `GuardSettlingH …`           — the settling hypothesis, at the Aux-side
      `mv = (Aux, 0)`, `tg = (Aux, 1)`, with EVERY freshness/bookkeeping hypothesis
      discharged generically (`FvDischarge`).

Residuals: the invariant term reads no Aux coordinate (`hgAux` — a fact about `g`, not
about the model), and the per-mode Z3 `BoxLe` certificates (`hcert` — the
`z3_unsat_sound` leaf). From (2), `theorem3_faithful_settling` yields
`rvalid (theorem3Form …)` exactly as in `EndToEnd.lean`; and `GuardSettlingB_rescale`
(Rescale.lean) transports the per-mode content to the benchmark's real-valued chart,
with (1) supplying precisely the coefficient laws its pushforward hypothesis needs.

The template scales to any instance with `n ≥ 2` (two spare Aux coordinates; the
`n = 1` models are padded for exactly this reason).
-/
import RelCertifier.FvDischarge
import RelCertifier.FaithfulCerts

namespace RelCertifier
open DL RelCertifier.Parse

/-- **arm_refinement, checker-side pipeline as one term.** -/
theorem arm_refinement_mega (g : Term (Var 2)) (fL : Fin 2 → Term (Var 2))
    (hgAux : ∀ i : Fin 2, ((Side.Aux, i) : Var 2) ∉ g.fv)
    (hcert : ∀ q m, arm_refinementM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (arm_refinementM.GdOf q) ν →
          BoxLe (Program.ode m.sys arm_refinementM.envF)
            (fun ω => Term.eval g ω) ν) :
    faithfulSettling arm_refinement_IR arm_refinement_meta arm_refinementM = true
    ∧ GuardSettlingH arm_refinementM.graph arm_refinementM.GdOf
        ((Side.Aux, 0) : Var 2) g (Term.const 1) ((Side.Aux, 1) : Var 2)
        ((arm_refinementM.dt : ℝ)) fL arm_refinementM.envF :=
  ⟨rfl,
   wellformed_sound_aux arm_refinementM 0 1 (by decide) g fL
     rfl (by norm_num [SettlingModel.dt, arm_refinementM]) hgAux hcert⟩

end RelCertifier
