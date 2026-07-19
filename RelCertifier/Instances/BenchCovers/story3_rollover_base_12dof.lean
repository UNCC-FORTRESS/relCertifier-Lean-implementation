/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story3_rollover_base_12dof` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `story3_rollover_base_12dof` (emitted). -/
def story3_rollover_base_12dof_cover : CoverEmitE :=
  ⟨"story3_rollover_base_12dof", [], [
    ⟨"STEEP", (5 : ℚ) / 4, 2, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩, ⟨"MODER", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩, ⟨"FLAT", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩]⟩,
    ⟨"MODER", (5 : ℚ) / 4, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩, ⟨"MODER", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩, ⟨"FLAT", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩]⟩,
    ⟨"FLAT", (5 : ℚ) / 4, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", [4, 2, 3], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩, ⟨"MODER", [4, 2, 3], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩, ⟨"FLAT", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩]⟩]⟩

end RelCertifier
