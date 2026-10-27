import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def rover_rollover_payload_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"rover_rollover_payload", [
    ⟨"STEEP", "MODER", .hop, true, ["STEEP"]⟩,
    ⟨"MODER", "STEEP", .hop, true, ["MODER"]⟩,
    ⟨"MODER", "FLAT", .hop, true, ["MODER"]⟩,
    ⟨"FLAT", "MODER", .hop, true, ["FLAT"]⟩]⟩

end RelCertifier.Choice
