/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_drl_lane_control` (suite_v2) — emitted pre-landing record (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py lit_drl_lane_control`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def lit_drl_lane_control_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"lit_drl_lane_control", [
    ⟨"AccelLAccel", "AccelLAccel", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"AccelLAccel", "AccelLAccel", false, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"AccelLAccel", "AccelLBrake", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"AccelLAccel", "AccelLBrake", false, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"AccelLAccel", "CoastLAccel", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"AccelLAccel", "CoastLBrake", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"AccelLAccel", "BrakeLAccel", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"AccelLAccel", "BrakeLBrake", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"AccelLBrake", "AccelLAccel", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"AccelLBrake", "AccelLAccel", false, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"AccelLBrake", "AccelLBrake", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"AccelLBrake", "AccelLBrake", false, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"AccelLBrake", "CoastLAccel", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"AccelLBrake", "CoastLBrake", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"AccelLBrake", "BrakeLAccel", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"AccelLBrake", "BrakeLBrake", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"CoastLAccel", "AccelLAccel", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"CoastLAccel", "AccelLAccel", false, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"CoastLAccel", "AccelLBrake", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"CoastLAccel", "AccelLBrake", false, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"CoastLAccel", "CoastLBrake", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"CoastLAccel", "BrakeLAccel", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"CoastLAccel", "BrakeLAccel", false, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"CoastLAccel", "BrakeLBrake", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"CoastLAccel", "BrakeLBrake", false, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"CoastLBrake", "AccelLAccel", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"CoastLBrake", "AccelLAccel", false, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"CoastLBrake", "AccelLBrake", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"CoastLBrake", "AccelLBrake", false, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"CoastLBrake", "CoastLAccel", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"CoastLBrake", "BrakeLAccel", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"CoastLBrake", "BrakeLAccel", false, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"CoastLBrake", "BrakeLBrake", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"CoastLBrake", "BrakeLBrake", false, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"BrakeLAccel", "AccelLAccel", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"BrakeLAccel", "AccelLAccel", false, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"BrakeLAccel", "AccelLBrake", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"BrakeLAccel", "AccelLBrake", false, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"BrakeLAccel", "CoastLAccel", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"BrakeLAccel", "CoastLBrake", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"BrakeLAccel", "BrakeLBrake", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"BrakeLBrake", "AccelLAccel", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"BrakeLBrake", "AccelLAccel", false, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"BrakeLBrake", "AccelLBrake", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"BrakeLBrake", "AccelLBrake", false, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"BrakeLBrake", "CoastLAccel", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"BrakeLBrake", "CoastLBrake", true, [0, 1, 2, 3, 4, 5]⟩,
    ⟨"BrakeLBrake", "BrakeLAccel", true, [0, 1, 2, 3, 4, 5]⟩]⟩

end RelCertifier.Preland
