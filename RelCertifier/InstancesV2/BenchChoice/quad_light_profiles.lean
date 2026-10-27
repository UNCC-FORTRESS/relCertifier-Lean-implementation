import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def quad_light_profiles_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"quad_light_profiles", [
    ⟨"CLIMB", "NORMAL", .hop, true, ["SPORT"]⟩,
    ⟨"CLIMB", "ECO", .hop, true, ["SPORT"]⟩]⟩

end RelCertifier.Choice
