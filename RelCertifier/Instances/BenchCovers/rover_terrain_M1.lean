/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_terrain_M1` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_terrain_M1` (emitted). -/
def rover_terrain_M1_cover : CoverEmitE :=
  ⟨"rover_terrain_M1", [], [
    ⟨"ROUGH", (1 : ℚ) / 1, 2, [⟨"ROUGH", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩, ⟨"SMOOTH", true, false, false, true, true⟩], ["ROUGH", "FLAT", "SMOOTH"], [⟨"ROUGH", [0], [0], [0]⟩, ⟨"FLAT", [0], [0], [0]⟩, ⟨"SMOOTH", [0], [0], [0]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 2, [⟨"ROUGH", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩, ⟨"SMOOTH", true, false, false, true, true⟩], ["ROUGH", "FLAT", "SMOOTH"], [⟨"ROUGH", [], [0], [0]⟩, ⟨"FLAT", [0], [0], [0]⟩, ⟨"SMOOTH", [0], [0], [0]⟩]⟩,
    ⟨"SMOOTH", (3 : ℚ) / 2, 3, [⟨"ROUGH", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩, ⟨"SMOOTH", true, false, false, true, true⟩], ["ROUGH", "FLAT", "SMOOTH"], [⟨"ROUGH", [], [0], [0]⟩, ⟨"FLAT", [0], [0], [0]⟩, ⟨"SMOOTH", [0], [0], [0]⟩]⟩]⟩

end RelCertifier
