/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `engine_cooling_prelanding` (prelanding_demo) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_prelanding_demo.py`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `engine_cooling_prelanding` (emitted, suite_v2, widened cut channel on). -/
def engine_cooling_prelanding_coverV2 : CoverEmitE :=
  ⟨"engine_cooling_prelanding", [], [
    ⟨"Cool", (1 : ℚ) / 1, 1, [⟨"Cool", true, false, false⟩, ⟨"Heat", false, false, false⟩], ["Cool", "Heat"], [⟨"Cool", [0, 1], [], [], 1, 1⟩, ⟨"Heat", [0], [], [], 1, 1⟩]⟩,
    ⟨"Heat", (1 : ℚ) / 1, 1, [⟨"Cool", false, false, false⟩, ⟨"Heat", true, false, false⟩], ["Cool", "Heat"], [⟨"Cool", [1], [], [], 1, 1⟩, ⟨"Heat", [0, 1], [], [], 1, 1⟩]⟩]⟩

end RelCertifier
