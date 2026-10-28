import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def lit_lz21_vehicle_position_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"lit_lz21_vehicle_position", [
    ⟨"Um", "U0", .hop, true, ["Um"]⟩,
    ⟨"Um", "Up", .hop, true, ["Um"]⟩,
    ⟨"U0", "Um", .hop, true, ["U0"]⟩,
    ⟨"U0", "Up", .hop, true, ["U0"]⟩,
    ⟨"Up", "Um", .hop, true, ["Up"]⟩,
    ⟨"Up", "U0", .hop, true, ["Up"]⟩]⟩

end RelCertifier.Choice
