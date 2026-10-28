/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_latency` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py platoon_latency`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `platoon_latency` (emitted, suite_v2, widened cut channel on). -/
def platoon_latency_coverV2 : CoverEmitE :=
  ⟨"platoon_latency", [("CACC", "AEB")], [
    ⟨"CACC_UP", (1 : ℚ) / 1, 1, [⟨"CACC", true, false, false⟩, ⟨"AEB", false, false, false⟩], ["CACC"], [⟨"CACC", [0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [8, 9], [8, 9], 1, 1⟩, ⟨"AEB", [0, 2, 4, 6, 7, 8, 9], [2, 3, 6, 7, 8, 9], [2, 3, 6, 7, 8, 9], 1, 1⟩]⟩,
    ⟨"CACC_DN", (1 : ℚ) / 1, 1, [⟨"CACC", true, false, false⟩, ⟨"AEB", false, false, false⟩], ["CACC"], [⟨"CACC", [0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [8, 9], [8, 9], 1, 1⟩, ⟨"AEB", [0, 2, 4, 6, 7, 8, 9], [2, 3, 6, 7, 8, 9], [2, 3, 6, 7, 8, 9], 1, 1⟩]⟩,
    ⟨"AEB", (1 : ℚ) / 1, 1, [⟨"CACC", false, false, false⟩, ⟨"AEB", true, false, false⟩], ["AEB"], [⟨"CACC", [3], [], [], 1, 1⟩, ⟨"AEB", [0, 1, 2, 3], [2, 3], [2, 3], 1, 1⟩]⟩]⟩

end RelCertifier
