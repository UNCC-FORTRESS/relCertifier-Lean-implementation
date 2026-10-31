import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def watertank_twospeed_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"watertank_twospeed", [
    ⟨"Low", "MidEco", true, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidBoost", "High"]⟩,
    ⟨"Low", "MidEco", false, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidBoost", "High"]⟩,
    ⟨"Low", "MidBoost", true, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "High"]⟩,
    ⟨"Low", "MidBoost", false, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "High"]⟩,
    ⟨"Low", "High", true, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "MidBoost"]⟩,
    ⟨"Mid", "Fast", true, [⟨"x", (7 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Slow", "MidEco", "MidBoost"]⟩,
    ⟨"Mid", "Fast", false, [⟨"x", (7 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Slow", "MidEco", "MidBoost"]⟩,
    ⟨"Mid", "Slow", true, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "MidBoost"]⟩,
    ⟨"Mid", "Slow", false, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "MidBoost"]⟩,
    ⟨"Mid", "MidEco", true, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidBoost", "High"]⟩,
    ⟨"Mid", "MidEco", false, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidBoost", "High"]⟩,
    ⟨"Mid", "MidBoost", true, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "High"]⟩,
    ⟨"Mid", "MidBoost", false, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "High"]⟩,
    ⟨"High", "Fast", true, [⟨"x", (7 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Slow", "MidEco", "MidBoost"]⟩,
    ⟨"High", "Fast", false, [⟨"x", (7 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Slow", "MidEco", "MidBoost"]⟩,
    ⟨"High", "Slow", true, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "MidBoost"]⟩,
    ⟨"High", "Slow", false, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "MidBoost"]⟩,
    ⟨"High", "MidEco", true, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidBoost", "High"]⟩,
    ⟨"High", "MidEco", false, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidBoost", "High"]⟩,
    ⟨"High", "MidBoost", true, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "High"]⟩,
    ⟨"High", "MidBoost", false, [⟨"x", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MidEco", "High"]⟩]⟩

end RelCertifier.Progress
