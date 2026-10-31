import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def quad_light_profiles_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"quad_light_profiles", [
    ⟨"ECO", "NORMAL", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ECO", "SPORT"]⟩,
    ⟨"ECO", "NORMAL", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ECO", "SPORT"]⟩,
    ⟨"ECO", "ECO", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL", "SPORT"]⟩,
    ⟨"ECO", "ECO", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL", "SPORT"]⟩,
    ⟨"ECO", "SPORT", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL", "ECO"]⟩,
    ⟨"ECO", "SPORT", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL", "ECO"]⟩,
    ⟨"NORMAL", "NORMAL", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ECO", "SPORT"]⟩,
    ⟨"NORMAL", "NORMAL", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ECO", "SPORT"]⟩,
    ⟨"NORMAL", "ECO", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL", "SPORT"]⟩,
    ⟨"NORMAL", "ECO", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL", "SPORT"]⟩,
    ⟨"NORMAL", "SPORT", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL", "ECO"]⟩,
    ⟨"NORMAL", "SPORT", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL", "ECO"]⟩,
    ⟨"SPORT", "NORMAL", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ECO", "SPORT"]⟩,
    ⟨"SPORT", "NORMAL", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ECO", "SPORT"]⟩,
    ⟨"SPORT", "ECO", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL", "SPORT"]⟩,
    ⟨"SPORT", "ECO", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL", "SPORT"]⟩,
    ⟨"SPORT", "SPORT", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL", "ECO"]⟩,
    ⟨"SPORT", "SPORT", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL", "ECO"]⟩]⟩

end RelCertifier.Progress
