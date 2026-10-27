import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def canal_gate_notches_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"canal_gate_notches", [
    ⟨"RAISE", "N75", .hop, true, ["N100"]⟩,
    ⟨"RAISE", "N50", .hop, true, ["N100"]⟩,
    ⟨"HOLD", "N100", .hop, true, ["N75", "N50"]⟩,
    ⟨"HOLD", "N25", .hop, true, ["N75", "N50"]⟩,
    ⟨"LOWER", "N75", .hop, true, ["N25"]⟩,
    ⟨"LOWER", "N50", .hop, true, ["N25"]⟩]⟩

end RelCertifier.Choice
