/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung2_3to6` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `refinement_ladder_rover_rung2_3to6` (emitted). -/
def refinement_ladder_rover_rung2_3to6_cover : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung2_3to6", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 2, 3, 1], [1], [1]⟩, ⟨"MODER", [0, 2, 3, 1], [1], [1]⟩, ⟨"FLAT", [0, 2, 3, 1], [1], [1]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["MODER", "FLAT"], [⟨"STEEP", [2, 3], [1], [1]⟩, ⟨"MODER", [0, 2, 3, 1], [1], [1]⟩, ⟨"FLAT", [0, 2, 3, 1], [1], [1]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false⟩, ⟨"MODER", false, false, false⟩, ⟨"FLAT", true, false, false⟩], ["FLAT"], [⟨"STEEP", [2, 3], [1], [1]⟩, ⟨"MODER", [2, 3], [1], [1]⟩, ⟨"FLAT", [0, 2, 3, 1], [1], [1]⟩]⟩]⟩

end RelCertifier
