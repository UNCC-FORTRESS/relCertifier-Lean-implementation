/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `antenna_track_kvretune` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py antenna_track_kvretune`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `antenna_track_kvretune` (emitted, suite_v2, widened cut channel on). -/
def antenna_track_kvretune_coverV2 : CoverEmitE :=
  ⟨"antenna_track_kvretune", [], [
    ⟨"TRACK", (1 : ℚ) / 1, 1, [⟨"TRACK", true, false, false⟩, ⟨"STOW", false, false, false⟩, ⟨"STOWED", true, false, false⟩], ["TRACK"], [⟨"TRACK", [0, 1, 2, 3, 6, 7, 4, 5], [0, 3], [0, 3], 1, 1⟩, ⟨"STOW", [0, 1, 2, 6, 4], [0, 2], [0, 2], 1, 1⟩, ⟨"STOWED", [0, 1, 2, 3, 4, 5, 6, 7], [0, 2, 3, 4, 5, 6, 7, 1], [0, 2, 3, 4, 5, 6, 7, 1], 1, 1⟩]⟩,
    ⟨"STOW", (1 : ℚ) / 1, 1, [⟨"TRACK", false, false, false⟩, ⟨"STOW", true, false, false⟩, ⟨"STOWED", false, false, false⟩], ["STOW"], [⟨"TRACK", [0, 1, 3, 6, 7, 5], [0, 3], [0, 3], 1, 1⟩, ⟨"STOW", [0, 1, 2, 3, 6, 7, 4, 5], [0, 2], [0, 2], 1, 1⟩, ⟨"STOWED", [0, 1, 3, 6, 7, 5], [0, 2, 3, 4, 5, 6, 7, 1], [0, 2, 3], 1, 1⟩]⟩,
    ⟨"STOWED", (1 : ℚ) / 1, 1, [⟨"TRACK", true, false, false⟩, ⟨"STOW", false, false, false⟩, ⟨"STOWED", true, false, false⟩], ["STOWED"], [⟨"TRACK", [0, 1, 2, 3, 4, 5, 6, 7], [0, 3], [0, 3], 1, 1⟩, ⟨"STOW", [0, 1, 2, 6, 7, 4], [0, 2], [0, 2], 1, 1⟩, ⟨"STOWED", [0, 1, 2, 3, 6, 7, 4, 5], [0, 2, 3], [0, 2, 3], 1, 1⟩]⟩]⟩

end RelCertifier
