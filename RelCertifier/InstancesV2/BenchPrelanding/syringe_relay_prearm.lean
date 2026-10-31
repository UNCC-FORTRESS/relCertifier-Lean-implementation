/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `syringe_relay_prearm` (suite_v2) — emitted pre-landing record (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py syringe_relay_prearm`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def syringe_relay_prearm_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"syringe_relay_prearm", [
    ⟨"RUN1", "TAKEUP2", true, [0, 1, 2, 3, 4, 5, 6]⟩,
    ⟨"RUN1", "RUN2", true, [0, 1, 2, 3, 4, 5, 6]⟩,
    ⟨"PREARM", "TAKEUP2", true, [0, 1, 2, 3, 4, 5, 6]⟩,
    ⟨"PREARM", "RUN2", true, [0, 1, 2, 3, 4, 5, 6]⟩,
    ⟨"READY", "TAKEUP2", true, [0, 1, 2, 3, 4, 5, 6]⟩,
    ⟨"READY", "RUN2", true, [0, 1, 2, 3, 4, 5, 6]⟩,
    ⟨"TAKEUP2", "RUN1", true, [0, 1, 2, 3, 4, 5, 6]⟩,
    ⟨"TAKEUP2", "RUN1", false, [0, 1, 2, 3, 4, 5, 6]⟩,
    ⟨"TAKEUP2", "RUN2", true, [0, 1, 2, 3, 4, 5, 6]⟩,
    ⟨"RUN2", "RUN1", true, [0, 1, 2, 3, 4]⟩,
    ⟨"RUN2", "RUN1", false, [0, 1, 2, 3, 4]⟩,
    ⟨"RUN2", "TAKEUP2", true, [0, 1, 2, 3, 4]⟩,
    ⟨"RUN2", "TAKEUP2", false, [0, 1, 2, 3, 4]⟩,
    ⟨"END", "RUN1", true, [0, 1, 2, 3, 4]⟩,
    ⟨"END", "RUN1", false, [0, 1, 2, 3, 4]⟩,
    ⟨"END", "TAKEUP2", true, [0, 1, 2, 3, 4]⟩,
    ⟨"END", "TAKEUP2", false, [0, 1, 2, 3, 4]⟩,
    ⟨"END", "RUN2", true, [0, 1, 2, 3, 4]⟩,
    ⟨"END", "RUN2", false, [0, 1, 2, 3, 4]⟩]⟩

end RelCertifier.Preland
