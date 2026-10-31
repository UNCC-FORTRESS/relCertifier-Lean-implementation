import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def canal_gate_notches_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"canal_gate_notches", [
    ⟨"RAISE", "N25", .repo, true, ["N100"]⟩,
    ⟨"RAISE", "N50", .repo, true, ["N100", "N25"]⟩,
    ⟨"HOLD", "N25", .repo, true, ["N75", "N50"]⟩,
    ⟨"LOWER", "N50", .repo, true, ["N25"]⟩,
    ⟨"LOWER", "N100", .repo, true, ["N50", "N25"]⟩]⟩

end RelCertifier.Choice
