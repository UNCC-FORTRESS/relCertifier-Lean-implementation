/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `attitude_rate` — cut-free emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `RELCERT_NO_CUT=1 relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `attitude_rate` (cut-free emission). -/
def attitude_rate_coverNC : CoverEmitE :=
  ⟨"attitude_rate", [], [
    ⟨"CRUISE", (2 : ℚ) / 1, 2, [⟨"RECOVER", true, false, false, false, false⟩, ⟨"TRACK", true, true, true, false, false⟩], ["RECOVER", "TRACK"], [⟨"RECOVER", [0], [], []⟩, ⟨"TRACK", [0], [], []⟩]⟩]⟩

end RelCertifier
