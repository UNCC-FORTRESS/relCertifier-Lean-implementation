import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def rover_patrol_lag_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"rover_patrol_lag", [
    ⟨"SLOW", "SLOW", true, [⟨"v", (1 : ℚ) / 2, true, (1 : ℚ) / 16⟩, ⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 2⟩], ["MEDIUM_ECO", "MEDIUM_BRISK"]⟩,
    ⟨"SLOW", "SLOW", false, [⟨"v", (1 : ℚ) / 2, true, (1 : ℚ) / 16⟩, ⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 2⟩], ["MEDIUM_ECO", "MEDIUM_BRISK"]⟩,
    ⟨"SLOW", "MEDIUM_ECO", true, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_BRISK", "FAST"]⟩,
    ⟨"SLOW", "MEDIUM_ECO", false, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_BRISK", "FAST"]⟩,
    ⟨"SLOW", "MEDIUM_BRISK", true, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_ECO", "FAST"]⟩,
    ⟨"SLOW", "MEDIUM_BRISK", false, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_ECO", "FAST"]⟩,
    ⟨"MEDIUM_ECO", "SLOW", true, [⟨"v", (1 : ℚ) / 2, true, (1 : ℚ) / 16⟩, ⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 2⟩], ["MEDIUM_ECO", "MEDIUM_BRISK"]⟩,
    ⟨"MEDIUM_ECO", "SLOW", false, [⟨"v", (1 : ℚ) / 2, true, (1 : ℚ) / 16⟩, ⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 2⟩], ["MEDIUM_ECO", "MEDIUM_BRISK"]⟩,
    ⟨"MEDIUM_ECO", "MEDIUM_ECO", true, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_BRISK", "FAST"]⟩,
    ⟨"MEDIUM_ECO", "MEDIUM_ECO", false, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_BRISK", "FAST"]⟩,
    ⟨"MEDIUM_ECO", "MEDIUM_BRISK", true, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_ECO", "FAST"]⟩,
    ⟨"MEDIUM_ECO", "MEDIUM_BRISK", false, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_ECO", "FAST"]⟩,
    ⟨"MEDIUM_BRISK", "SLOW", true, [⟨"v", (1 : ℚ) / 2, true, (1 : ℚ) / 16⟩, ⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 2⟩], ["MEDIUM_ECO", "MEDIUM_BRISK"]⟩,
    ⟨"MEDIUM_BRISK", "SLOW", false, [⟨"v", (1 : ℚ) / 2, true, (1 : ℚ) / 16⟩, ⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 2⟩], ["MEDIUM_ECO", "MEDIUM_BRISK"]⟩,
    ⟨"MEDIUM_BRISK", "MEDIUM_ECO", true, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_BRISK", "FAST"]⟩,
    ⟨"MEDIUM_BRISK", "MEDIUM_ECO", false, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_BRISK", "FAST"]⟩,
    ⟨"MEDIUM_BRISK", "MEDIUM_BRISK", true, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_ECO", "FAST"]⟩,
    ⟨"MEDIUM_BRISK", "MEDIUM_BRISK", false, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_ECO", "FAST"]⟩,
    ⟨"FAST", "SLOW", true, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_ECO", "MEDIUM_BRISK"]⟩,
    ⟨"FAST", "SLOW", false, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_ECO", "MEDIUM_BRISK"]⟩,
    ⟨"FAST", "MEDIUM_ECO", true, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_BRISK", "FAST"]⟩,
    ⟨"FAST", "MEDIUM_ECO", false, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_BRISK", "FAST"]⟩,
    ⟨"FAST", "MEDIUM_BRISK", true, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_ECO", "FAST"]⟩,
    ⟨"FAST", "MEDIUM_BRISK", false, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_ECO", "FAST"]⟩]⟩

end RelCertifier.Progress
