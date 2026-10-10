/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `endurance_orderlift_1to2` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `endurance_orderlift_1to2` (emitted). -/
def endurance_orderlift_1to2_cover : CoverEmitE :=
  ⟨"endurance_orderlift_1to2", [], [
    ⟨"STEEP", (2 : ℚ) / 1, 4, [⟨"STEEP", false, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [], [0], [0]⟩, ⟨"MODER", [0], [0], [0]⟩, ⟨"FLAT", [0], [0], [0]⟩]⟩,
    ⟨"MODER", (2 : ℚ) / 1, 4, [⟨"STEEP", false, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [], [0], [0]⟩, ⟨"MODER", [0], [0], [0]⟩, ⟨"FLAT", [0], [0], [0]⟩]⟩,
    ⟨"FLAT", (2 : ℚ) / 1, 4, [⟨"STEEP", false, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [], [0], [0]⟩, ⟨"MODER", [0], [0], [0]⟩, ⟨"FLAT", [0], [0], [0]⟩]⟩]⟩

end RelCertifier
