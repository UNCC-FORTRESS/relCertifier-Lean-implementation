/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `arm_chain_rung1` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `arm_chain_rung1` (emitted). -/
def arm_chain_rung1_cover : CoverEmitE :=
  ⟨"arm_chain_rung1", [], [
    ⟨"ApproachFast", (5 : ℚ) / 2, 3, [⟨"Approach", true, true, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0], [0], [0]⟩, ⟨"Return", [], [], []⟩]⟩,
    ⟨"ApproachSlow", (3 : ℚ) / 2, 2, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0], [0], [0]⟩, ⟨"Return", [], [], []⟩]⟩,
    ⟨"Return", (1 : ℚ) / 1, 1, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", true, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0], [0], [0]⟩, ⟨"Return", [0], [], []⟩]⟩]⟩

end RelCertifier
