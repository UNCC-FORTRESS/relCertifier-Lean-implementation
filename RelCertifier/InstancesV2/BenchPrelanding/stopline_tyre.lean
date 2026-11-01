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
    ⟨"CRUISE", "BRAKE", true, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]⟩,
    ⟨"BRAKE", "CRUISE", true, [0, 1]⟩,
    ⟨"BRAKE", "CRUISE", false, [0, 1]⟩,
    ⟨"BRAKE", "BRAKE", true, [0, 1]⟩,
    ⟨"BRAKE", "BRAKE", false, [0, 1]⟩,
    ⟨"STOP", "CRUISE", true, [0, 1]⟩,
    ⟨"STOP", "CRUISE", false, [0, 1]⟩,
    ⟨"STOP", "BRAKE", true, [0, 1]⟩,
    ⟨"STOP", "BRAKE", false, [0, 1]⟩]⟩

end RelCertifier.Preland
