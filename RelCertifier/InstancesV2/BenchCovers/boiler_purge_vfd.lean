/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `boiler_purge_vfd` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py boiler_purge_vfd`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `boiler_purge_vfd` (emitted, suite_v2, widened cut channel on). -/
def boiler_purge_vfd_coverV2 : CoverEmitE :=
  ⟨"boiler_purge_vfd", [], [
    ⟨"PURGE", (1 : ℚ) / 1, 1, [⟨"PURGE", true, false, false⟩, ⟨"FIRE", false, false, false⟩], ["PURGE"], [⟨"PURGE", [0, 1, 2, 3, 4, 5], [0, 1, 3, 4, 5], [0, 1, 3, 4, 5], 1, 1⟩, ⟨"FIRE", [2, 4, 5], [2, 3, 4, 5, 0, 1], [2, 3, 4, 5], 1, 1⟩]⟩,
    ⟨"FIRE", (1 : ℚ) / 1, 1, [⟨"PURGE", false, true, true⟩, ⟨"FIRE", true, false, false⟩], ["PURGE", "FIRE"], [⟨"PURGE", [2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 1, 1⟩, ⟨"FIRE", [1, 2, 3, 4, 0], [2, 3, 4], [2, 3, 4], 1, 1⟩]⟩]⟩

end RelCertifier
