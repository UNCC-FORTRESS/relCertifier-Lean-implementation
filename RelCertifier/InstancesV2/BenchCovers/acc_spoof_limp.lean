/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_spoof_limp` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py acc_spoof_limp`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `acc_spoof_limp` (emitted, suite_v2, widened cut channel on). -/
def acc_spoof_limp_coverV2 : CoverEmitE :=
  ⟨"acc_spoof_limp", [("NORMAL", "DISENGAGE"), ("ECO", "DISENGAGE"), ("SPORT", "DISENGAGE")], [
    ⟨"CRUISE", (5 : ℚ) / 4, 3, [⟨"NORMAL", true, false, false⟩, ⟨"ECO", true, false, false⟩, ⟨"SPORT", true, false, false⟩, ⟨"DISENGAGE", false, false, false⟩], ["NORMAL", "ECO", "SPORT"], [⟨"NORMAL", [0, 1], [], []⟩, ⟨"ECO", [0, 1], [], []⟩, ⟨"SPORT", [0, 1], [], []⟩, ⟨"DISENGAGE", [1], [1], [1]⟩]⟩,
    ⟨"LIMP", (1 : ℚ) / 1, 2, [⟨"NORMAL", true, false, false⟩, ⟨"ECO", true, false, false⟩, ⟨"SPORT", true, false, false⟩, ⟨"DISENGAGE", false, false, false⟩], ["NORMAL", "ECO", "SPORT"], [⟨"NORMAL", [0, 1], [], []⟩, ⟨"ECO", [0, 1], [], []⟩, ⟨"SPORT", [0, 1], [], []⟩, ⟨"DISENGAGE", [1], [1], [1]⟩]⟩]⟩

end RelCertifier
