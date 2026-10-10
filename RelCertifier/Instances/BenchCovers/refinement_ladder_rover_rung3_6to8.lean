/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung3_6to8` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `refinement_ladder_rover_rung3_6to8` (emitted). -/
def refinement_ladder_rover_rung3_6to8_cover : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung3_6to8", [], [
    ⟨"STEEP", (9 : ℚ) / 4, 3, [⟨"STEEP", true, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩, ⟨"MODER", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩, ⟨"FLAT", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩]⟩,
    ⟨"MODER", (9 : ℚ) / 4, 3, [⟨"STEEP", false, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩, ⟨"MODER", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩, ⟨"FLAT", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩]⟩,
    ⟨"FLAT", (9 : ℚ) / 4, 3, [⟨"STEEP", false, true, true⟩, ⟨"MODER", false, true, true⟩, ⟨"FLAT", true, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", [2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩, ⟨"MODER", [2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩, ⟨"FLAT", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩]⟩]⟩

end RelCertifier
