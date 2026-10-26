import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def rover_tier_1to2_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"rover_tier_1to2", [
    ⟨"ACCEL", "ACCEL", true, [⟨"v", (3 : ℚ) / 5, true, (1 : ℚ) / 2⟩], ["COAST"]⟩,
    ⟨"ACCEL", "ACCEL", false, [⟨"v", (3 : ℚ) / 5, true, (1 : ℚ) / 2⟩], ["COAST"]⟩,
    ⟨"COAST", "ACCEL", true, [⟨"v", (3 : ℚ) / 5, true, (1 : ℚ) / 2⟩], ["COAST"]⟩,
    ⟨"COAST", "ACCEL", false, [⟨"v", (3 : ℚ) / 5, true, (1 : ℚ) / 2⟩], ["COAST"]⟩]⟩

end RelCertifier.Progress
