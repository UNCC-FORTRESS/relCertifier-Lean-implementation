/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_terrain_2to4` (suite_v2) — emitted pre-landing record (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_terrain_2to4`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def rover_terrain_2to4_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"rover_terrain_2to4", [
    ⟨"MUD", "MUD", true, [1, 2, 3, 4, 0]⟩,
    ⟨"MUD", "MUD", false, [1, 2, 3, 4, 0]⟩,
    ⟨"MUD", "GRAVEL", true, [1, 2, 3, 4, 0]⟩,
    ⟨"MUD", "GRAVEL", false, [1, 2, 3, 4, 0]⟩,
    ⟨"GRAVEL", "MUD", true, [1, 2, 3, 4, 0]⟩,
    ⟨"GRAVEL", "MUD", false, [1, 2, 3, 4, 0]⟩,
    ⟨"GRAVEL", "GRAVEL", true, [1, 2, 3, 4, 0]⟩,
    ⟨"GRAVEL", "GRAVEL", false, [1, 2, 3, 4, 0]⟩,
    ⟨"PAVED", "MUD", true, [1, 2, 3, 4, 0]⟩,
    ⟨"PAVED", "MUD", false, [1, 2, 3, 4, 0]⟩,
    ⟨"PAVED", "GRAVEL", true, [1, 2, 3, 4, 0]⟩,
    ⟨"PAVED", "GRAVEL", false, [1, 2, 3, 4, 0]⟩]⟩

end RelCertifier.Preland
