/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `arm_chain_rung2` — cut-free emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `RELCERT_NO_CUT=1 relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `arm_chain_rung2` (cut-free emission). -/
def arm_chain_rung2_coverNC : CoverEmitE :=
  ⟨"arm_chain_rung2", [], [
    ⟨"ApproachA", (7 : ℚ) / 4, 2, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, true, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Return"], [⟨"ApproachFast", [0], [0], [0]⟩, ⟨"ApproachSlow", [0], [0], [0]⟩, ⟨"Return", [], [], []⟩]⟩,
    ⟨"ApproachB", (5 : ℚ) / 4, 2, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, true, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Return"], [⟨"ApproachFast", [0], [0], [0]⟩, ⟨"ApproachSlow", [0], [0], [0]⟩, ⟨"Return", [], [], []⟩]⟩,
    ⟨"ApproachC", (1 : ℚ) / 1, 1, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, true, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Return"], [⟨"ApproachFast", [0], [0], [0]⟩, ⟨"ApproachSlow", [0], [0], [0]⟩, ⟨"Return", [], [], []⟩]⟩,
    ⟨"Hold", (1 : ℚ) / 1, 1, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Return"], [⟨"ApproachFast", [0], [0], [0]⟩, ⟨"ApproachSlow", [0], [0], [0]⟩, ⟨"Return", [], [], []⟩]⟩]⟩

end RelCertifier
