/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_tyre` (suite_v2) — emitted pre-landing record (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py stopline_tyre`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def stopline_tyre_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"stopline_tyre", [
    ⟨"CRUISE", "BRAKE", true, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
    ⟨"BRAKE", "CRUISE", true, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]⟩,
    ⟨"BRAKE", "CRUISE", false, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]⟩,
    ⟨"BRAKE", "BRAKE", true, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]⟩,
    ⟨"BRAKE", "BRAKE", false, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]⟩,
    ⟨"STOP", "CRUISE", true, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]⟩,
    ⟨"STOP", "CRUISE", false, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]⟩,
    ⟨"STOP", "BRAKE", true, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]⟩,
    ⟨"STOP", "BRAKE", false, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]⟩]⟩

end RelCertifier.Preland
