/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `syringe_relay_prearm` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py syringe_relay_prearm`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `syringe_relay_prearm` (emitted, suite_v2, widened cut channel on). -/
def syringe_relay_prearm_coverV2 : CoverEmitE :=
  ⟨"syringe_relay_prearm", [], [
    ⟨"RUN1", (1 : ℚ) / 1, 1, [⟨"RUN1", true, false, false⟩, ⟨"TAKEUP2", false, true, false⟩, ⟨"RUN2", false, true, false⟩, ⟨"END", true, false, false⟩], ["RUN1"], [⟨"RUN1", [0, 1, 2, 3, 4, 5, 6], [0, 2, 3, 4, 6], [0, 2, 3, 4, 6], 1, 1⟩, ⟨"TAKEUP2", [1, 2, 3, 5], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 5], 1, 1⟩, ⟨"RUN2", [1, 2, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 4, 6], 1, 1⟩, ⟨"END", [1, 2, 3, 4, 5, 6, 0], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6], 1, 1⟩]⟩,
    ⟨"PREARM", (1 : ℚ) / 1, 1, [⟨"RUN1", true, false, false⟩, ⟨"TAKEUP2", false, true, false⟩, ⟨"RUN2", false, true, false⟩, ⟨"END", true, false, false⟩], ["RUN1"], [⟨"RUN1", [0, 1, 2, 3, 4, 5, 6], [0, 2, 3, 4, 6], [0, 2, 3, 4, 6], 1, 1⟩, ⟨"TAKEUP2", [1, 2, 3, 5, 6], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 5], 1, 1⟩, ⟨"RUN2", [1, 2, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 4, 6], 1, 1⟩, ⟨"END", [1, 2, 3, 4, 5, 6, 0], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6], 1, 1⟩]⟩,
    ⟨"READY", (1 : ℚ) / 1, 1, [⟨"RUN1", true, false, false⟩, ⟨"TAKEUP2", false, true, false⟩, ⟨"RUN2", false, true, false⟩, ⟨"END", true, false, false⟩], ["RUN1"], [⟨"RUN1", [0, 1, 2, 3, 4, 5, 6], [0, 2, 3, 4, 6], [0, 2, 3, 4, 6], 1, 1⟩, ⟨"TAKEUP2", [1, 2, 3, 5], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 5], 1, 1⟩, ⟨"RUN2", [1, 2, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 4, 6], 1, 1⟩, ⟨"END", [1, 2, 3, 4, 5, 6, 0], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6], 1, 1⟩]⟩,
    ⟨"TAKEUP2", (1 : ℚ) / 1, 1, [⟨"RUN1", false, false, false⟩, ⟨"TAKEUP2", true, false, false⟩, ⟨"RUN2", false, true, false⟩, ⟨"END", true, false, false⟩], ["TAKEUP2"], [⟨"RUN1", [0, 2, 3, 4, 6], [0, 2, 3, 4, 6], [0, 2, 3, 4, 6], 1, 1⟩, ⟨"TAKEUP2", [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 5], [0, 1, 2, 3, 5], 1, 1⟩, ⟨"RUN2", [0, 1, 2, 4, 6], [0, 1, 2, 4, 6, 3, 5], [0, 1, 2, 4, 6], 1, 1⟩, ⟨"END", [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6], 1, 1⟩]⟩,
    ⟨"RUN2", (1 : ℚ) / 1, 1, [⟨"RUN1", false, false, false⟩, ⟨"TAKEUP2", false, true, true⟩, ⟨"RUN2", true, false, false⟩, ⟨"END", false, false, false⟩], ["TAKEUP2", "RUN2"], [⟨"RUN1", [0, 3, 4], [0, 2, 3], [0, 2, 3], 1, 1⟩, ⟨"TAKEUP2", [0, 1, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 1, 1⟩, ⟨"RUN2", [0, 1, 2, 3, 4], [0, 1, 2], [0, 1, 2], 1, 1⟩, ⟨"END", [0, 1, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 1, 1⟩]⟩,
    ⟨"END", (1 : ℚ) / 1, 1, [⟨"RUN1", true, true, true⟩, ⟨"TAKEUP2", true, true, true⟩, ⟨"RUN2", false, false, false⟩, ⟨"END", true, false, false⟩], ["END"], [⟨"RUN1", [0, 2, 3, 4, 1], [0, 2, 3, 4, 1], [0, 2, 3, 4, 1], 1, 1⟩, ⟨"TAKEUP2", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 1, 1⟩, ⟨"RUN2", [0, 1, 2], [0, 1, 2], [0, 1, 2], 1, 1⟩, ⟨"END", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 1, 1⟩]⟩]⟩

end RelCertifier
