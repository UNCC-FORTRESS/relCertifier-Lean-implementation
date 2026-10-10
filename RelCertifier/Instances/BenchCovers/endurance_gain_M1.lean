/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `endurance_gain_M1` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `endurance_gain_M1` (emitted). -/
def endurance_gain_M1_cover : CoverEmitE :=
  ⟨"endurance_gain_M1", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 2, [⟨"STEEP", true, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0], [0], [0]⟩, ⟨"MODER", [0], [0], [0]⟩, ⟨"FLAT", [0], [0], [0]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [], [0], [0]⟩, ⟨"MODER", [0], [0], [0]⟩, ⟨"FLAT", [0], [0], [0]⟩]⟩,
    ⟨"FLAT", (3 : ℚ) / 2, 3, [⟨"STEEP", false, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [], [0], [0]⟩, ⟨"MODER", [0], [0], [0]⟩, ⟨"FLAT", [0], [0], [0]⟩]⟩]⟩

end RelCertifier
