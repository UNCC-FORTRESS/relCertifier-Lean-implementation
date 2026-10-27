import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def sat_detumble_weak_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"sat_detumble_weak", [
    ⟨"DETUMBLE", "NOMINAL", .hop, true, ["ECONOMY", "SURVIVAL"]⟩]⟩

end RelCertifier.Choice
