import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def quad_light_profiles_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"quad_light_profiles", [
    ⟨"CLIMB", "ECO", .hop, false, ["NORMAL"]⟩,
    ⟨"CLIMB", "SPORT", .hop, false, ["NORMAL"]⟩,
    ⟨"CLIMB", "ECO", .hop, true, ["NORMAL"]⟩,
    ⟨"CLIMB", "SPORT", .hop, true, ["NORMAL"]⟩]⟩

end RelCertifier.Choice
