import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def lit_girard08_robot_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"lit_girard08_robot", [
    ⟨"M1", "M2", .hop, true, ["M1"]⟩,
    ⟨"M1", "M3", .hop, true, ["M1"]⟩,
    ⟨"M1", "M4", .hop, true, ["M1"]⟩,
    ⟨"M1", "M6", .hop, true, ["M1"]⟩,
    ⟨"M2", "M1", .hop, true, ["M2"]⟩,
    ⟨"M2", "M3", .hop, true, ["M2"]⟩,
    ⟨"M3", "M1", .hop, true, ["M3"]⟩,
    ⟨"M3", "M2", .hop, true, ["M3"]⟩,
    ⟨"M3", "M4", .hop, true, ["M3"]⟩,
    ⟨"M3", "M6", .hop, true, ["M3"]⟩,
    ⟨"M4", "M1", .hop, true, ["M4"]⟩,
    ⟨"M4", "M3", .hop, true, ["M4"]⟩,
    ⟨"M4", "M5", .hop, true, ["M4"]⟩,
    ⟨"M4", "M6", .hop, true, ["M4"]⟩,
    ⟨"M5", "M4", .hop, true, ["M5"]⟩,
    ⟨"M5", "M6", .hop, true, ["M5"]⟩,
    ⟨"M6", "M1", .hop, true, ["M6"]⟩,
    ⟨"M6", "M3", .hop, true, ["M6"]⟩,
    ⟨"M6", "M4", .hop, true, ["M6"]⟩,
    ⟨"M6", "M5", .hop, true, ["M6"]⟩]⟩

end RelCertifier.Choice
