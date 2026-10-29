/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `flaps_slow_approach` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py flaps_slow_approach`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `flaps_slow_approach` (emitted, suite_v2, widened cut channel on). -/
def flaps_slow_approach_coverV2 : CoverEmitE :=
  ⟨"flaps_slow_approach", [], [
    ⟨"EXT", (1 : ℚ) / 2, 1, [⟨"EXT", true, false, false⟩, ⟨"CONF2", false, false, false⟩], ["EXT"], [⟨"EXT", [0, 1, 2, 3], [0], [0], 1, 2⟩, ⟨"CONF2", [1], [0, 1, 2, 3], [0, 1], 1, 2⟩]⟩,
    ⟨"CONF2", (1 : ℚ) / 1, 1, [⟨"EXT", false, false, false⟩, ⟨"CONF2", true, false, false⟩], ["CONF2"], [⟨"EXT", [0, 2, 3], [0], [0], 1, 1⟩, ⟨"CONF2", [0, 1, 2, 3], [0, 1], [0, 1], 1, 1⟩]⟩]⟩

end RelCertifier
