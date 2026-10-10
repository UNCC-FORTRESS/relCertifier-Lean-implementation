/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_attitude_cone_12dof` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_attitude_cone_12dof` (emitted). -/
def rover_attitude_cone_12dof_cover : CoverEmitE :=
  ⟨"rover_attitude_cone_12dof", [], [
    ⟨"STEEP", (17 : ℚ) / 10, 2, [⟨"STEEP", true, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩, ⟨"MODER", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩, ⟨"FLAT", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩]⟩,
    ⟨"MODER", (17 : ℚ) / 10, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩, ⟨"MODER", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩, ⟨"FLAT", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩]⟩,
    ⟨"FLAT", (17 : ℚ) / 10, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", false, true, true⟩, ⟨"FLAT", true, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", [2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩, ⟨"MODER", [2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩, ⟨"FLAT", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩]⟩]⟩

end RelCertifier
