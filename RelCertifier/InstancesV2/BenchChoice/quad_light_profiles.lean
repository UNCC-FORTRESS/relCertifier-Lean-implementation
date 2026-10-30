import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def quad_light_profiles_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"quad_light_profiles", [
    ⟨"ECO", "NORMAL", .hop, false, ["ECO"]⟩,
    ⟨"ECO", "SPORT", .hop, false, ["ECO"]⟩,
    ⟨"ECO", "NORMAL", .hop, true, ["ECO"]⟩,
    ⟨"ECO", "SPORT", .hop, true, ["ECO"]⟩,
    ⟨"NORMAL", "ECO", .hop, false, ["NORMAL"]⟩,
    ⟨"NORMAL", "SPORT", .hop, false, ["NORMAL"]⟩,
    ⟨"NORMAL", "ECO", .hop, true, ["NORMAL"]⟩,
    ⟨"NORMAL", "SPORT", .hop, true, ["NORMAL"]⟩,
    ⟨"SPORT", "NORMAL", .hop, false, ["SPORT"]⟩,
    ⟨"SPORT", "ECO", .hop, false, ["SPORT"]⟩,
    ⟨"SPORT", "NORMAL", .hop, true, ["SPORT"]⟩,
    ⟨"SPORT", "ECO", .hop, true, ["SPORT"]⟩]⟩

end RelCertifier.Choice
