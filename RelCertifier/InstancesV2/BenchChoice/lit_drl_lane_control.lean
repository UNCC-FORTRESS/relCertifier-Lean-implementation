import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def lit_drl_lane_control_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"lit_drl_lane_control", [
    ⟨"AccelLAccel", "BrakeLBrake", .repo, true, ["AccelLAccel"]⟩,
    ⟨"AccelLAccel", "BrakeLAccel", .repo, true, ["AccelLAccel", "BrakeLBrake"]⟩,
    ⟨"AccelLAccel", "CoastLBrake", .repo, true, ["AccelLAccel", "BrakeLAccel", "BrakeLBrake"]⟩,
    ⟨"AccelLAccel", "CoastLAccel", .repo, true, ["AccelLAccel", "CoastLBrake", "BrakeLAccel", "BrakeLBrake"]⟩,
    ⟨"AccelLBrake", "BrakeLBrake", .repo, true, ["AccelLBrake"]⟩,
    ⟨"AccelLBrake", "BrakeLAccel", .repo, true, ["AccelLBrake", "BrakeLBrake"]⟩,
    ⟨"AccelLBrake", "CoastLBrake", .repo, true, ["AccelLBrake", "BrakeLAccel", "BrakeLBrake"]⟩,
    ⟨"AccelLBrake", "CoastLAccel", .repo, true, ["AccelLBrake", "CoastLBrake", "BrakeLAccel", "BrakeLBrake"]⟩,
    ⟨"CoastLAccel", "BrakeLBrake", .repo, true, ["CoastLAccel"]⟩,
    ⟨"CoastLAccel", "BrakeLAccel", .repo, true, ["CoastLAccel", "BrakeLBrake"]⟩,
    ⟨"CoastLAccel", "CoastLBrake", .repo, true, ["CoastLAccel", "BrakeLAccel", "BrakeLBrake"]⟩,
    ⟨"CoastLAccel", "AccelLBrake", .repo, true, ["CoastLAccel", "CoastLBrake", "BrakeLAccel", "BrakeLBrake"]⟩,
    ⟨"CoastLBrake", "BrakeLBrake", .repo, true, ["CoastLBrake"]⟩,
    ⟨"CoastLBrake", "BrakeLAccel", .repo, true, ["CoastLBrake", "BrakeLBrake"]⟩,
    ⟨"CoastLBrake", "CoastLAccel", .repo, true, ["CoastLBrake", "BrakeLAccel", "BrakeLBrake"]⟩,
    ⟨"CoastLBrake", "AccelLBrake", .repo, true, ["CoastLAccel", "CoastLBrake", "BrakeLAccel", "BrakeLBrake"]⟩,
    ⟨"BrakeLAccel", "BrakeLBrake", .repo, true, ["BrakeLAccel"]⟩,
    ⟨"BrakeLAccel", "CoastLBrake", .repo, true, ["BrakeLAccel", "BrakeLBrake"]⟩,
    ⟨"BrakeLAccel", "CoastLAccel", .repo, true, ["CoastLBrake", "BrakeLAccel", "BrakeLBrake"]⟩,
    ⟨"BrakeLAccel", "AccelLBrake", .repo, true, ["CoastLAccel", "CoastLBrake", "BrakeLAccel", "BrakeLBrake"]⟩,
    ⟨"BrakeLBrake", "BrakeLAccel", .repo, true, ["BrakeLBrake"]⟩,
    ⟨"BrakeLBrake", "CoastLBrake", .repo, true, ["BrakeLAccel", "BrakeLBrake"]⟩,
    ⟨"BrakeLBrake", "CoastLAccel", .repo, true, ["CoastLBrake", "BrakeLAccel", "BrakeLBrake"]⟩,
    ⟨"BrakeLBrake", "AccelLBrake", .repo, true, ["CoastLAccel", "CoastLBrake", "BrakeLAccel", "BrakeLBrake"]⟩]⟩

end RelCertifier.Choice
