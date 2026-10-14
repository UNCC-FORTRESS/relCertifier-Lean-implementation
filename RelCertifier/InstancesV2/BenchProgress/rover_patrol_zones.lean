import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def rover_patrol_zones_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"rover_patrol_zones", [
    ⟨"SLOW", "SLOW", true, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["MEDIUM_ECO", "MEDIUM_BRISK"]⟩,
    ⟨"SLOW", "SLOW", false, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["MEDIUM_ECO", "MEDIUM_BRISK"]⟩,
    ⟨"SLOW", "MEDIUM_ECO", true, [⟨"s", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["FAST"]⟩,
    ⟨"SLOW", "MEDIUM_ECO", false, [⟨"s", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["FAST"]⟩,
    ⟨"SLOW", "MEDIUM_BRISK", true, [⟨"s", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["FAST"]⟩,
    ⟨"SLOW", "MEDIUM_BRISK", false, [⟨"s", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["FAST"]⟩,
    ⟨"MEDIUM_ECO", "SLOW", true, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["MEDIUM_ECO", "MEDIUM_BRISK"]⟩,
    ⟨"MEDIUM_ECO", "SLOW", false, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["MEDIUM_ECO", "MEDIUM_BRISK"]⟩,
    ⟨"MEDIUM_ECO", "MEDIUM_ECO", true, [⟨"s", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["FAST"]⟩,
    ⟨"MEDIUM_ECO", "MEDIUM_ECO", false, [⟨"s", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["FAST"]⟩,
    ⟨"MEDIUM_ECO", "MEDIUM_BRISK", true, [⟨"s", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["FAST"]⟩,
    ⟨"MEDIUM_ECO", "MEDIUM_BRISK", false, [⟨"s", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["FAST"]⟩,
    ⟨"MEDIUM_BRISK", "SLOW", true, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["MEDIUM_ECO", "MEDIUM_BRISK"]⟩,
    ⟨"MEDIUM_BRISK", "SLOW", false, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["MEDIUM_ECO", "MEDIUM_BRISK"]⟩,
    ⟨"MEDIUM_BRISK", "MEDIUM_ECO", true, [⟨"s", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["FAST"]⟩,
    ⟨"MEDIUM_BRISK", "MEDIUM_ECO", false, [⟨"s", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["FAST"]⟩,
    ⟨"MEDIUM_BRISK", "MEDIUM_BRISK", true, [⟨"s", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["FAST"]⟩,
    ⟨"MEDIUM_BRISK", "MEDIUM_BRISK", false, [⟨"s", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["FAST"]⟩,
    ⟨"FAST", "SLOW", true, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_ECO", "MEDIUM_BRISK"]⟩,
    ⟨"FAST", "SLOW", false, [⟨"s", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MEDIUM_ECO", "MEDIUM_BRISK"]⟩,
    ⟨"FAST", "MEDIUM_ECO", true, [⟨"s", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["FAST"]⟩,
    ⟨"FAST", "MEDIUM_ECO", false, [⟨"s", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["FAST"]⟩,
    ⟨"FAST", "MEDIUM_BRISK", true, [⟨"s", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["FAST"]⟩,
    ⟨"FAST", "MEDIUM_BRISK", false, [⟨"s", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["FAST"]⟩]⟩

end RelCertifier.Progress
