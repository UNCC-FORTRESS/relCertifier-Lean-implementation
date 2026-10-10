/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story2_lateral_rung_a_8dof` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `story2_lateral_rung_a_8dof` (emitted). -/
def story2_lateral_rung_a_8dof_cover : CoverEmitE :=
  ⟨"story2_lateral_rung_a_8dof", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 3, 4, 5, 6, 2], [2], [2]⟩, ⟨"MODER", [0, 1, 3, 4, 5, 6, 2], [2], [2]⟩, ⟨"FLAT", [0, 1, 3, 4, 5, 6, 2], [2], [2]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["MODER", "FLAT"], [⟨"STEEP", [1, 3, 4, 5, 6], [2], [2]⟩, ⟨"MODER", [0, 1, 3, 4, 5, 6, 2], [2], [2]⟩, ⟨"FLAT", [0, 1, 3, 4, 5, 6, 2], [2], [2]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false⟩, ⟨"MODER", false, false, false⟩, ⟨"FLAT", true, false, false⟩], ["FLAT"], [⟨"STEEP", [1, 3, 4, 5, 6], [2], [2]⟩, ⟨"MODER", [1, 3, 4, 5, 6], [2], [2]⟩, ⟨"FLAT", [0, 1, 3, 4, 5, 6, 2], [2], [2]⟩]⟩]⟩

end RelCertifier
