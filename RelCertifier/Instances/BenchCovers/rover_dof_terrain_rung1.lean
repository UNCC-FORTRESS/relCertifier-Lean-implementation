/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_dof_terrain_rung1` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_dof_terrain_rung1` (emitted). -/
def rover_dof_terrain_rung1_cover : CoverEmitE :=
  ⟨"rover_dof_terrain_rung1", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1], [0, 1], [0, 1]⟩, ⟨"MODER", [0, 1], [0, 1], [0, 1]⟩, ⟨"FLAT", [0, 1], [0, 1], [0, 1]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [], [0, 1], [0, 1]⟩, ⟨"MODER", [0, 1], [0, 1], [0, 1]⟩, ⟨"FLAT", [0, 1], [0, 1], [0, 1]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", [], [0, 1], [0, 1]⟩, ⟨"MODER", [], [0, 1], [0, 1]⟩, ⟨"FLAT", [0, 1], [0, 1], [0, 1]⟩]⟩]⟩

end RelCertifier
