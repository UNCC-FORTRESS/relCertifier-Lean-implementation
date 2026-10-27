import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def sat3w_detumble_phases_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"sat3w_detumble_phases", [
    ⟨"DETUMBLE", "FINE", .hop, true, ["DETUMBLE"]⟩,
    ⟨"FINE", "DETUMBLE", .hop, true, ["FINE"]⟩]⟩

end RelCertifier.Choice
