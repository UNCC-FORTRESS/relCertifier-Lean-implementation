/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_nahs25_engine_cooling` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py lit_nahs25_engine_cooling`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `lit_nahs25_engine_cooling` (emitted, suite_v2, widened cut channel on). -/
def lit_nahs25_engine_cooling_coverV2 : CoverEmitE :=
  ⟨"lit_nahs25_engine_cooling", [], [
    ⟨"Cool", (1 : ℚ) / 1, 1, [⟨"Cool", true, false, false⟩, ⟨"Heat", false, false, false⟩], ["Cool", "Heat"], [⟨"Cool", [0, 1], [], [], 1, 1⟩, ⟨"Heat", [0], [], [], 1, 1⟩]⟩,
    ⟨"Heat", (1 : ℚ) / 1, 1, [⟨"Cool", false, false, false⟩, ⟨"Heat", true, false, false⟩], ["Cool", "Heat"], [⟨"Cool", [1], [], [], 1, 1⟩, ⟨"Heat", [0, 1], [], [], 1, 1⟩]⟩]⟩

end RelCertifier
