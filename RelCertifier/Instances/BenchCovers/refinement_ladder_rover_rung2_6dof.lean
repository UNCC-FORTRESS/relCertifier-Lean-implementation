/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung2_6dof` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `refinement_ladder_rover_rung2_6dof` (emitted). -/
def refinement_ladder_rover_rung2_6dof_cover : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung2_6dof", [], [
    ⟨"STEEP", (1001 : ℚ) / 1000, 2, [⟨"STEEP", true, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0], [0], [0]⟩, ⟨"MODER", [0], [0], [0]⟩, ⟨"FLAT", [0], [0], [0]⟩]⟩,
    ⟨"MODER", (1001 : ℚ) / 1000, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [], [0], [0]⟩, ⟨"MODER", [0], [0], [0]⟩, ⟨"FLAT", [0], [0], [0]⟩]⟩,
    ⟨"FLAT", (1001 : ℚ) / 1000, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", false, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [], [0], [0]⟩, ⟨"MODER", [], [0], [0]⟩, ⟨"FLAT", [0], [0], [0]⟩]⟩]⟩

end RelCertifier
