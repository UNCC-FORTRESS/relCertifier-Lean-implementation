import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def watertank_twospeed_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"watertank_twospeed", [
    ⟨"Low", "High", true, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "MidBoost"]⟩,
    ⟨"High", "Fast", true, [⟨"x", (7 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Slow", "MidEco", "MidBoost"]⟩,
    ⟨"High", "Fast", false, [⟨"x", (7 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Slow", "MidEco", "MidBoost"]⟩,
    ⟨"High", "Slow", true, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "MidBoost"]⟩,
    ⟨"High", "Slow", false, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "MidBoost"]⟩,
    ⟨"High", "MidEco", true, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidBoost", "High"]⟩,
    ⟨"High", "MidEco", false, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidBoost", "High"]⟩,
    ⟨"High", "MidBoost", true, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "High"]⟩,
    ⟨"High", "MidBoost", false, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "High"]⟩]⟩

end RelCertifier.Progress
