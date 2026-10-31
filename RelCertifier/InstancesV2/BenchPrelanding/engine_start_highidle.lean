/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `engine_start_highidle` (suite_v2) — emitted pre-landing record (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py engine_start_highidle`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def engine_start_highidle_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"engine_start_highidle", [
    ⟨"STARTER", "LIGHTOFF", true, [0, 1, 2, 3]⟩,
    ⟨"STARTER", "LIGHTOFF", false, [0, 1, 2, 3]⟩,
    ⟨"STARTER", "SELF", true, [0, 1, 2, 3]⟩,
    ⟨"STARTER", "SELF", false, [0, 1, 2, 3]⟩,
    ⟨"STARTER_LOW", "STARTER", true, [0, 2, 3, 1]⟩,
    ⟨"STARTER_LOW", "LIGHTOFF", true, [0, 1, 2, 3]⟩,
    ⟨"STARTER_LOW", "LIGHTOFF", false, [0, 1, 2, 3]⟩,
    ⟨"STARTER_LOW", "SELF", true, [0, 1, 2, 3]⟩,
    ⟨"STARTER_LOW", "SELF", false, [0, 1, 2, 3]⟩,
    ⟨"LIGHTOFF", "STARTER", true, [0]⟩,
    ⟨"LIGHTOFF", "STARTER", false, [0]⟩,
    ⟨"LIGHTOFF", "STARTER_LOW", true, [0]⟩,
    ⟨"LIGHTOFF", "STARTER_LOW", false, [0]⟩,
    ⟨"LIGHTOFF", "LIGHTOFF", true, [0]⟩,
    ⟨"LIGHTOFF", "LIGHTOFF", false, [0]⟩,
    ⟨"LIGHTOFF", "SELF", true, [0]⟩,
    ⟨"LIGHTOFF", "SELF", false, [0]⟩,
    ⟨"SELF", "STARTER", true, [0]⟩,
    ⟨"SELF", "STARTER", false, [0]⟩,
    ⟨"SELF", "STARTER_LOW", true, [0]⟩,
    ⟨"SELF", "STARTER_LOW", false, [0]⟩,
    ⟨"SELF", "LIGHTOFF", true, [0]⟩,
    ⟨"SELF", "LIGHTOFF", false, [0]⟩,
    ⟨"SELF", "SELF", true, [0]⟩,
    ⟨"SELF", "SELF", false, [0]⟩,
    ⟨"IDLE", "STARTER", true, [0]⟩,
    ⟨"IDLE", "STARTER", false, [0]⟩,
    ⟨"IDLE", "STARTER_LOW", true, [0]⟩,
    ⟨"IDLE", "STARTER_LOW", false, [0]⟩,
    ⟨"IDLE", "LIGHTOFF", true, [0]⟩,
    ⟨"IDLE", "LIGHTOFF", false, [0]⟩,
    ⟨"IDLE", "SELF", true, [0]⟩,
    ⟨"IDLE", "SELF", false, [0]⟩,
    ⟨"ABORT", "STARTER", true, [0]⟩,
    ⟨"ABORT", "STARTER", false, [0]⟩,
    ⟨"ABORT", "STARTER_LOW", true, [0]⟩,
    ⟨"ABORT", "STARTER_LOW", false, [0]⟩,
    ⟨"ABORT", "LIGHTOFF", true, [0]⟩,
    ⟨"ABORT", "LIGHTOFF", false, [0]⟩,
    ⟨"ABORT", "SELF", true, [0]⟩,
    ⟨"ABORT", "SELF", false, [0]⟩]⟩

end RelCertifier.Preland
