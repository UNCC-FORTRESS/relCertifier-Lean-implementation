import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def lit_lz21_vehicle_position_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"lit_lz21_vehicle_position", [
    ⟨"Um", "Up", .repo, true, ["Um"]⟩,
    ⟨"U0", "Up", .repo, true, ["U0"]⟩,
    ⟨"Up", "U0", .repo, true, ["Up"]⟩]⟩

end RelCertifier.Choice
