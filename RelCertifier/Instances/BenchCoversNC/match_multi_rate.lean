/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `match_multi_rate` — cut-free emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `RELCERT_NO_CUT=1 relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `match_multi_rate` (cut-free emission). -/
def match_multi_rate_coverNC : CoverEmitE :=
  ⟨"match_multi_rate", [("DRIVE", "STALL")], [
    ⟨"FAST", (3 : ℚ) / 1, 3, [⟨"DRIVE", true, false, false, false, false⟩, ⟨"STALL", false, false, false, false, false⟩], ["DRIVE"], [⟨"DRIVE", [0], [], []⟩, ⟨"STALL", [], [], []⟩]⟩,
    ⟨"MEDIUM", (2 : ℚ) / 1, 2, [⟨"DRIVE", true, false, false, false, false⟩, ⟨"STALL", false, false, false, false, false⟩], ["DRIVE"], [⟨"DRIVE", [0], [], []⟩, ⟨"STALL", [], [], []⟩]⟩,
    ⟨"SLOW", (1 : ℚ) / 1, 1, [⟨"DRIVE", true, false, false, false, false⟩, ⟨"STALL", false, false, false, false, false⟩], ["DRIVE"], [⟨"DRIVE", [0], [], []⟩, ⟨"STALL", [], [], []⟩]⟩,
    ⟨"RESET", (1 : ℚ) / 1, 1, [⟨"DRIVE", true, false, false, false, false⟩, ⟨"STALL", false, false, false, false, false⟩], ["DRIVE"], [⟨"DRIVE", [0], [], []⟩, ⟨"STALL", [], [], []⟩]⟩]⟩

end RelCertifier
