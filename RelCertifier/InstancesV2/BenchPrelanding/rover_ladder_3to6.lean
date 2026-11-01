/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_ladder_3to6` (suite_v2) — emitted pre-landing record (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_ladder_3to6`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def rover_ladder_3to6_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"rover_ladder_3to6", [
    ⟨"MODER", "STEEP", true, [1, 2, 3, 4, 5, 0]⟩,
    ⟨"MODER", "STEEP", false, [1, 2, 3, 4, 5, 0]⟩,
    ⟨"FLAT", "STEEP", true, [1, 2, 3, 4, 5, 0]⟩,
    ⟨"FLAT", "STEEP", false, [1, 2, 3, 4, 5, 0]⟩,
    ⟨"FLAT", "MODER", true, [1, 2, 3, 4, 5, 0]⟩,
    ⟨"FLAT", "MODER", false, [1, 2, 3, 4, 5, 0]⟩]⟩

end RelCertifier.Preland
