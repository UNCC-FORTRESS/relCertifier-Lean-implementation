import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def quad_light_profiles_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"quad_light_profiles", [
    ⟨"ECO", "SPORT", .repo, false, ["ECO"]⟩,
    ⟨"ECO", "SPORT", .repo, true, ["ECO"]⟩,
    ⟨"NORMAL", "SPORT", .repo, false, ["NORMAL"]⟩,
    ⟨"NORMAL", "SPORT", .repo, true, ["NORMAL"]⟩,
    ⟨"SPORT", "ECO", .repo, false, ["SPORT"]⟩,
    ⟨"SPORT", "ECO", .repo, true, ["SPORT"]⟩]⟩

end RelCertifier.Choice
