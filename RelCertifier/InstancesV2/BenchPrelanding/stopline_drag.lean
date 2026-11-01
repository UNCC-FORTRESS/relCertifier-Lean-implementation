/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_drag` (suite_v2) — emitted pre-landing record (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py stopline_drag`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def stopline_drag_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"stopline_drag", [
    ⟨"CRUISE", "BRAKE", true, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]⟩,
    ⟨"BRAKE", "CRUISE", true, [0, 1, 2, 3]⟩,
    ⟨"BRAKE", "CRUISE", false, [0, 1, 2, 3]⟩,
    ⟨"STOP", "CRUISE", true, [0, 1]⟩,
    ⟨"STOP", "CRUISE", false, [0, 1]⟩]⟩

end RelCertifier.Preland
