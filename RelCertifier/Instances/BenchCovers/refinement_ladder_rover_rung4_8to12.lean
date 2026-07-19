/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung4_8to12` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `refinement_ladder_rover_rung4_8to12` (emitted). -/
def refinement_ladder_rover_rung4_8to12_cover : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung4_8to12", [], [
    ⟨"STEEP", (17 : ℚ) / 10, 2, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1], [0, 1], [0, 1]⟩, ⟨"MODER", [0, 1], [0, 1], [0, 1]⟩, ⟨"FLAT", [0, 1], [0, 1], [0, 1]⟩]⟩,
    ⟨"MODER", (17 : ℚ) / 10, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [], [0, 1], [0, 1]⟩, ⟨"MODER", [0, 1], [0, 1], [0, 1]⟩, ⟨"FLAT", [0, 1], [0, 1], [0, 1]⟩]⟩,
    ⟨"FLAT", (17 : ℚ) / 10, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", [], [0, 1], [0, 1]⟩, ⟨"MODER", [], [0, 1], [0, 1]⟩, ⟨"FLAT", [0, 1], [0, 1], [0, 1]⟩]⟩]⟩

end RelCertifier
