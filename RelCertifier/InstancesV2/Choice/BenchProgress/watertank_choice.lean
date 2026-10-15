import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def watertank_choice_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"watertank_choice", [
    ⟨"Low", "High", true, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "MidBoost"]⟩,
    ⟨"High", "Low", true, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "MidBoost"]⟩,
    ⟨"High", "Low", false, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "MidBoost"]⟩,
    ⟨"High", "MidBoost", true, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "High"]⟩,
    ⟨"High", "MidBoost", false, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "High"]⟩]⟩

end RelCertifier.Progress
