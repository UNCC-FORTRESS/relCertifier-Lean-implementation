import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def vehicle_accel_copy_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"vehicle_accel_copy", [
    ⟨"Accel", "Coast", .repo, true, ["Accel"]⟩,
    ⟨"Accel", "Brake", .hop, true, ["Accel", "Coast"]⟩,
    ⟨"Coast", "Accel", .hop, true, ["Coast"]⟩,
    ⟨"Coast", "Brake", .hop, true, ["Coast"]⟩,
    ⟨"Brake", "Coast", .repo, true, ["Brake"]⟩,
    ⟨"Brake", "Accel", .hop, true, ["Coast", "Brake"]⟩]⟩

end RelCertifier.Choice
