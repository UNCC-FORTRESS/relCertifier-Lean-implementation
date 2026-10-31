/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_spoof_limp` (suite_v2) — emitted pre-landing record (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py acc_spoof_limp`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def acc_spoof_limp_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"acc_spoof_limp", [
    ⟨"CRUISE", "NORMAL", true, [0, 1]⟩,
    ⟨"CRUISE", "NORMAL", false, [0, 1]⟩,
    ⟨"CRUISE", "ECO", true, [0, 1]⟩,
    ⟨"CRUISE", "ECO", false, [0, 1]⟩,
    ⟨"CRUISE", "SPORT", true, [0, 1]⟩,
    ⟨"CRUISE", "SPORT", false, [0, 1]⟩,
    ⟨"LIMP", "NORMAL", true, [0, 1]⟩,
    ⟨"LIMP", "NORMAL", false, [0, 1]⟩,
    ⟨"LIMP", "ECO", true, [0, 1]⟩,
    ⟨"LIMP", "ECO", false, [0, 1]⟩,
    ⟨"LIMP", "SPORT", true, [0, 1]⟩,
    ⟨"LIMP", "SPORT", false, [0, 1]⟩]⟩

end RelCertifier.Preland
