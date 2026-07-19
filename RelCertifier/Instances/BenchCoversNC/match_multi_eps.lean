/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `match_multi_eps` — cut-free emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `RELCERT_NO_CUT=1 relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `match_multi_eps` (cut-free emission). -/
def match_multi_eps_coverNC : CoverEmitE :=
  ⟨"match_multi_eps", [], [
    ⟨"ACCEL", (1 : ℚ) / 1, 4, [⟨"ACCEL", true, false, false, false, false⟩, ⟨"COAST", false, true, true, false, false⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [0], [], []⟩, ⟨"COAST", [], [], []⟩]⟩,
    ⟨"COAST", (1 : ℚ) / 1, 4, [⟨"ACCEL", true, false, false, false, false⟩, ⟨"COAST", true, true, true, false, false⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [0], [], []⟩, ⟨"COAST", [0], [], []⟩]⟩]⟩

end RelCertifier
