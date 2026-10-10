/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `arm_chain_rung3` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `arm_chain_rung3` (emitted). -/
def arm_chain_rung3_cover : CoverEmitE :=
  ⟨"arm_chain_rung3", [], [
    ⟨"Accelerate", (1 : ℚ) / 1, 1, [⟨"ApproachA", true, true, true⟩, ⟨"ApproachB", false, true, true⟩, ⟨"ApproachC", false, true, true⟩, ⟨"Hold", true, true, true⟩], ["ApproachA", "ApproachB", "ApproachC", "Hold"], [⟨"ApproachA", [0], [0], [0]⟩, ⟨"ApproachB", [], [0], [0]⟩, ⟨"ApproachC", [], [0], [0]⟩, ⟨"Hold", [0], [0], [0]⟩]⟩,
    ⟨"Brake", (1 : ℚ) / 1, 1, [⟨"ApproachA", true, true, true⟩, ⟨"ApproachB", false, true, true⟩, ⟨"ApproachC", false, true, true⟩, ⟨"Hold", true, true, true⟩], ["ApproachA", "ApproachB", "ApproachC", "Hold"], [⟨"ApproachA", [0], [0], [0]⟩, ⟨"ApproachB", [], [0], [0]⟩, ⟨"ApproachC", [], [0], [0]⟩, ⟨"Hold", [0], [0], [0]⟩]⟩]⟩

end RelCertifier
