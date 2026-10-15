import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def watertank_choice_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"watertank_choice", [
    ⟨"Mid", "MidEco", .hop, true, ["MidBoost", "High"]⟩]⟩

end RelCertifier.Choice
