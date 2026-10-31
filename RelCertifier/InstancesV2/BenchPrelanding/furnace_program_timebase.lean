/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `furnace_program_timebase` (suite_v2) — emitted pre-landing record (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py furnace_program_timebase`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def furnace_program_timebase_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"furnace_program_timebase", [
    ⟨"PREHEAT", "HEAT", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"HEAT", "PREHEAT", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"HEAT", "PREHEAT", false, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"SOAK", "PREHEAT", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"SOAK", "PREHEAT", false, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"SOAK", "HEAT", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"SOAK", "HEAT", false, [0, 1, 2, 3, 4, 5]⟩]⟩

end RelCertifier.Preland
