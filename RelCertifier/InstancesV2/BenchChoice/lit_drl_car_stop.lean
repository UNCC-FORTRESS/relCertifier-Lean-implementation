import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def lit_drl_car_stop_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"lit_drl_car_stop", [
    ⟨"Accel", "Coast", .hop, true, ["Accel"]⟩,
    ⟨"Accel", "Brake", .hop, true, ["Accel"]⟩,
    ⟨"Coast", "Accel", .hop, true, ["Coast"]⟩,
    ⟨"Coast", "Brake", .hop, true, ["Coast"]⟩,
    ⟨"Brake", "Accel", .hop, true, ["Brake"]⟩,
    ⟨"Brake", "Coast", .hop, true, ["Brake"]⟩]⟩

end RelCertifier.Choice
