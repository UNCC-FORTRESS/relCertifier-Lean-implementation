import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def train_ato_odometry_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"train_ato_odometry", [
    ⟨"PL1", "PL1", true, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PL2", "PL3"]⟩,
    ⟨"PL1", "PL1", false, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PL2", "PL3"]⟩,
    ⟨"PL1", "PL2", true, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PL1", "PL3"]⟩,
    ⟨"PL1", "PL2", false, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PL1", "PL3"]⟩,
    ⟨"PL1", "PL3", true, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PL1", "PL2"]⟩,
    ⟨"PL1", "PL3", false, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PL1", "PL2"]⟩,
    ⟨"PL2", "PL1", true, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PL2", "PL3"]⟩,
    ⟨"PL2", "PL1", false, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PL2", "PL3"]⟩,
    ⟨"PL2", "PL2", true, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PL1", "PL3"]⟩,
    ⟨"PL2", "PL2", false, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PL1", "PL3"]⟩,
    ⟨"PL2", "PL3", true, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PL1", "PL2"]⟩,
    ⟨"PL2", "PL3", false, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PL1", "PL2"]⟩,
    ⟨"PL3", "PL1", true, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PL2", "PL3"]⟩,
    ⟨"PL3", "PL1", false, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PL2", "PL3"]⟩,
    ⟨"PL3", "PL2", true, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PL1", "PL3"]⟩,
    ⟨"PL3", "PL2", false, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PL1", "PL3"]⟩,
    ⟨"PL3", "PL3", true, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PL1", "PL2"]⟩,
    ⟨"PL3", "PL3", false, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PL1", "PL2"]⟩]⟩

end RelCertifier.Progress
