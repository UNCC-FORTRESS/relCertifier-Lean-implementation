/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_terrain_4to6` (suite_v2) — emitted pre-landing record (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_terrain_4to6`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def rover_terrain_4to6_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"rover_terrain_4to6", [
    ⟨"GRAVEL", "MUD", true, [1, 2, 3, 4, 5, 6, 7, 0]⟩,
    ⟨"GRAVEL", "MUD", false, [1, 2, 3, 4, 5, 6, 7, 0]⟩,
    ⟨"PAVED", "MUD", true, [1, 2, 3, 4, 5, 6, 7, 0]⟩,
    ⟨"PAVED", "MUD", false, [1, 2, 3, 4, 5, 6, 7, 0]⟩,
    ⟨"PAVED", "GRAVEL", true, [1, 2, 3, 4, 5, 6, 7, 0]⟩,
    ⟨"PAVED", "GRAVEL", false, [1, 2, 3, 4, 5, 6, 7, 0]⟩]⟩

end RelCertifier.Preland
