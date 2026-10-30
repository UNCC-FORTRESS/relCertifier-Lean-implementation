import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def acc_spoof_limp_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"acc_spoof_limp", [
    ⟨"LIMP", "ECO", .hop, false, ["NORMAL"]⟩,
    ⟨"LIMP", "ECO", .hop, true, ["NORMAL"]⟩]⟩

end RelCertifier.Choice
