import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def vehicle_hypercert_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"vehicle_hypercert", [
    ⟨"Am4", "Ap2", .hop, true, ["Am4"]⟩,
    ⟨"Am4", "Ap4", .hop, true, ["Am4"]⟩,
    ⟨"Am4", "A0", .repo, true, ["Am4", "Ap2", "Ap4"]⟩,
    ⟨"Am4", "Am2", .hop, true, ["Am4", "A0"]⟩,
    ⟨"Am2", "Ap2", .hop, true, ["Am2"]⟩,
    ⟨"Am2", "Ap4", .hop, true, ["Am2"]⟩,
    ⟨"Am2", "A0", .repo, true, ["Am2", "Ap2", "Ap4"]⟩,
    ⟨"Am2", "Am4", .hop, true, ["Am2", "A0"]⟩,
    ⟨"A0", "Am4", .hop, true, ["A0"]⟩,
    ⟨"A0", "Am2", .hop, true, ["A0"]⟩,
    ⟨"A0", "Ap2", .hop, true, ["A0"]⟩,
    ⟨"A0", "Ap4", .hop, true, ["A0"]⟩,
    ⟨"Ap2", "Am2", .hop, true, ["Ap2"]⟩,
    ⟨"Ap2", "Ap4", .hop, true, ["Ap2"]⟩,
    ⟨"Ap2", "A0", .repo, true, ["Am2", "Ap2", "Ap4"]⟩,
    ⟨"Ap2", "Am4", .hop, true, ["A0", "Ap2"]⟩,
    ⟨"Ap4", "Am2", .hop, true, ["Ap4"]⟩,
    ⟨"Ap4", "Ap2", .hop, true, ["Ap4"]⟩,
    ⟨"Ap4", "A0", .repo, true, ["Am2", "Ap2", "Ap4"]⟩,
    ⟨"Ap4", "Am4", .hop, true, ["A0", "Ap4"]⟩]⟩

end RelCertifier.Choice
