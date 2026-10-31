/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `tank_dos_3to1` (suite_v2) — emitted pre-landing record (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py tank_dos_3to1`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def tank_dos_3to1_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"tank_dos_3to1", [
    ⟨"P2", "P3", true, [2, 3, 0, 1]⟩,
    ⟨"P2", "P4", true, [2, 3, 0, 1]⟩,
    ⟨"P3", "P2", true, [2, 3, 0, 1]⟩,
    ⟨"P3", "P2", false, [2, 3, 0, 1]⟩,
    ⟨"P3", "P4", true, [2, 3, 0, 1]⟩,
    ⟨"P4", "P2", true, [2, 3, 0, 1]⟩,
    ⟨"P4", "P2", false, [2, 3, 0, 1]⟩,
    ⟨"P4", "P3", true, [2, 3, 0, 1]⟩,
    ⟨"P4", "P3", false, [2, 3, 0, 1]⟩,
    ⟨"P5", "P2", true, [2, 3, 0, 1]⟩,
    ⟨"P5", "P2", false, [2, 3, 0, 1]⟩,
    ⟨"P5", "P3", true, [2, 3, 0, 1]⟩,
    ⟨"P5", "P3", false, [2, 3, 0, 1]⟩,
    ⟨"P5", "P4", true, [2, 3, 0, 1]⟩,
    ⟨"P5", "P4", false, [2, 3, 0, 1]⟩]⟩

end RelCertifier.Preland
