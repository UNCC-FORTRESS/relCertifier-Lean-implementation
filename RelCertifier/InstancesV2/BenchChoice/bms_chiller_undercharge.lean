import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def bms_chiller_undercharge_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"bms_chiller_undercharge", [
    ⟨"COAST", "CHILL_LO", .hop, true, ["COAST"]⟩,
    ⟨"COAST", "CHILL_HI", .hop, true, ["COAST"]⟩,
    ⟨"CHILL", "COAST", .hop, true, ["CHILL_LO"]⟩,
    ⟨"CHILL", "CHILL_HI", .hop, true, ["CHILL_LO"]⟩]⟩

end RelCertifier.Choice
