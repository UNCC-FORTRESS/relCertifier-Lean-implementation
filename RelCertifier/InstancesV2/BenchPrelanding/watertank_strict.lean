/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank_strict` (strict_demo) — emitted pre-landing record (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_strict_demo.py`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def watertank_strict_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"watertank_strict", [
    ⟨"Low", "High", true, [0, 1]⟩,
    ⟨"High", "Low", true, [0, 1]⟩,
    ⟨"High", "Low", false, [0, 1]⟩,
    ⟨"High", "MidEco", true, [0, 1]⟩,
    ⟨"High", "MidEco", false, [0, 1]⟩,
    ⟨"High", "MidBoost", true, [0, 1]⟩,
    ⟨"High", "MidBoost", false, [0, 1]⟩]⟩

end RelCertifier.Preland
