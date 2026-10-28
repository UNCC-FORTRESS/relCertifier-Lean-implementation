import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def lit_drl_lane_control_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"lit_drl_lane_control", [
    ⟨"AccelLAccel", "AccelLBrake", .hop, true, ["AccelLAccel"]⟩,
    ⟨"AccelLAccel", "CoastLAccel", .hop, true, ["AccelLAccel"]⟩,
    ⟨"AccelLAccel", "CoastLBrake", .hop, true, ["AccelLAccel"]⟩,
    ⟨"AccelLAccel", "BrakeLAccel", .hop, true, ["AccelLAccel"]⟩,
    ⟨"AccelLAccel", "BrakeLBrake", .hop, true, ["AccelLAccel"]⟩,
    ⟨"AccelLBrake", "AccelLAccel", .hop, true, ["AccelLBrake"]⟩,
    ⟨"AccelLBrake", "CoastLAccel", .hop, true, ["AccelLBrake"]⟩,
    ⟨"AccelLBrake", "CoastLBrake", .hop, true, ["AccelLBrake"]⟩,
    ⟨"AccelLBrake", "BrakeLAccel", .hop, true, ["AccelLBrake"]⟩,
    ⟨"AccelLBrake", "BrakeLBrake", .hop, true, ["AccelLBrake"]⟩,
    ⟨"CoastLAccel", "AccelLAccel", .hop, true, ["CoastLAccel"]⟩,
    ⟨"CoastLAccel", "AccelLBrake", .hop, true, ["CoastLAccel"]⟩,
    ⟨"CoastLAccel", "CoastLBrake", .hop, true, ["CoastLAccel"]⟩,
    ⟨"CoastLAccel", "BrakeLAccel", .hop, true, ["CoastLAccel"]⟩,
    ⟨"CoastLAccel", "BrakeLBrake", .hop, true, ["CoastLAccel"]⟩,
    ⟨"CoastLBrake", "AccelLAccel", .hop, true, ["CoastLBrake"]⟩,
    ⟨"CoastLBrake", "AccelLBrake", .hop, true, ["CoastLBrake"]⟩,
    ⟨"CoastLBrake", "CoastLAccel", .hop, true, ["CoastLBrake"]⟩,
    ⟨"CoastLBrake", "BrakeLAccel", .hop, true, ["CoastLBrake"]⟩,
    ⟨"CoastLBrake", "BrakeLBrake", .hop, true, ["CoastLBrake"]⟩,
    ⟨"BrakeLAccel", "AccelLAccel", .hop, true, ["BrakeLAccel"]⟩,
    ⟨"BrakeLAccel", "AccelLBrake", .hop, true, ["BrakeLAccel"]⟩,
    ⟨"BrakeLAccel", "CoastLAccel", .hop, true, ["BrakeLAccel"]⟩,
    ⟨"BrakeLAccel", "CoastLBrake", .hop, true, ["BrakeLAccel"]⟩,
    ⟨"BrakeLAccel", "BrakeLBrake", .hop, true, ["BrakeLAccel"]⟩,
    ⟨"BrakeLBrake", "AccelLAccel", .hop, true, ["BrakeLBrake"]⟩,
    ⟨"BrakeLBrake", "AccelLBrake", .hop, true, ["BrakeLBrake"]⟩,
    ⟨"BrakeLBrake", "CoastLAccel", .hop, true, ["BrakeLBrake"]⟩,
    ⟨"BrakeLBrake", "CoastLBrake", .hop, true, ["BrakeLBrake"]⟩,
    ⟨"BrakeLBrake", "BrakeLAccel", .hop, true, ["BrakeLBrake"]⟩]⟩

end RelCertifier.Choice
