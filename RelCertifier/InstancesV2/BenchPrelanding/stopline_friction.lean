/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_friction` (suite_v2) — emitted pre-landing record (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py stopline_friction`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def stopline_friction_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"stopline_friction", [
    ⟨"CRUISE", "BRAKE", true, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]⟩,
    ⟨"BRAKE", "CRUISE", true, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]⟩,
    ⟨"BRAKE", "CRUISE", false, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]⟩,
    ⟨"STOP", "CRUISE", true, [0, 1, 2, 3, 4, 5, 6, 7, 8]⟩,
    ⟨"STOP", "CRUISE", false, [0, 1, 2, 3, 4, 5, 6, 7, 8]⟩,
    ⟨"STOP", "BRAKE", true, [0, 1, 2, 3, 4, 5, 6, 7, 8]⟩,
    ⟨"STOP", "BRAKE", false, [0, 1, 2, 3, 4, 5, 6, 7, 8]⟩]⟩

end RelCertifier.Preland
