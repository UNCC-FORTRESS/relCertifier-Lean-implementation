import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def sat_detumble_weak_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"sat_detumble_weak", [
    ⟨"DETUMBLE", "ECONOMY", .hop, false, ["NOMINAL"]⟩,
    ⟨"DETUMBLE", "SURVIVAL", .hop, false, ["NOMINAL"]⟩,
    ⟨"DETUMBLE", "ECONOMY", .hop, true, ["NOMINAL"]⟩,
    ⟨"DETUMBLE", "SURVIVAL", .hop, true, ["NOMINAL"]⟩]⟩

end RelCertifier.Choice
