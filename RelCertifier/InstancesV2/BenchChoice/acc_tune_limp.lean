import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def acc_tune_limp_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"acc_tune_limp", [
    ⟨"CRUISE", "COMFORT", .hop, false, ["NORMAL"]⟩,
    ⟨"CRUISE", "SPORT", .hop, false, ["NORMAL"]⟩,
    ⟨"CRUISE", "COMFORT", .hop, false, ["NORMAL"]⟩,
    ⟨"CRUISE", "SPORT", .hop, false, ["NORMAL"]⟩,
    ⟨"CRUISE", "COMFORT", .hop, true, ["NORMAL"]⟩,
    ⟨"CRUISE", "SPORT", .hop, true, ["NORMAL"]⟩]⟩

end RelCertifier.Choice
