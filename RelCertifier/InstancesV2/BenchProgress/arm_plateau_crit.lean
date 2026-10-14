import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def arm_plateau_crit_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"arm_plateau_crit", [
    ⟨"Accelerate", "ApproachA", true, [⟨"theta", (7 : ℚ) / 20, true, (1 : ℚ) / 2⟩], ["ApproachB", "ApproachC", "Hold"]⟩,
    ⟨"Accelerate", "ApproachA", false, [⟨"theta", (7 : ℚ) / 20, true, (1 : ℚ) / 2⟩], ["ApproachB", "ApproachC", "Hold"]⟩,
    ⟨"Accelerate", "ApproachB", true, [⟨"theta", (1 : ℚ) / 2, true, (1 : ℚ) / 4⟩], ["ApproachC", "Hold"]⟩,
    ⟨"Accelerate", "ApproachB", false, [⟨"theta", (1 : ℚ) / 2, true, (1 : ℚ) / 4⟩], ["ApproachC", "Hold"]⟩,
    ⟨"Accelerate", "ApproachC", true, [⟨"theta", (3 : ℚ) / 5, true, (1 : ℚ) / 8⟩], ["Hold"]⟩,
    ⟨"Accelerate", "ApproachC", false, [⟨"theta", (3 : ℚ) / 5, true, (1 : ℚ) / 8⟩], ["Hold"]⟩,
    ⟨"Brake", "ApproachA", true, [⟨"theta", (7 : ℚ) / 20, true, (1 : ℚ) / 2⟩], ["ApproachB", "ApproachC", "Hold"]⟩,
    ⟨"Brake", "ApproachA", false, [⟨"theta", (7 : ℚ) / 20, true, (1 : ℚ) / 2⟩], ["ApproachB", "ApproachC", "Hold"]⟩,
    ⟨"Brake", "ApproachB", true, [⟨"theta", (1 : ℚ) / 2, true, (1 : ℚ) / 4⟩], ["ApproachC", "Hold"]⟩,
    ⟨"Brake", "ApproachB", false, [⟨"theta", (1 : ℚ) / 2, true, (1 : ℚ) / 4⟩], ["ApproachC", "Hold"]⟩,
    ⟨"Brake", "ApproachC", true, [⟨"theta", (3 : ℚ) / 5, true, (1 : ℚ) / 8⟩], ["Hold"]⟩,
    ⟨"Brake", "ApproachC", false, [⟨"theta", (3 : ℚ) / 5, true, (1 : ℚ) / 8⟩], ["Hold"]⟩]⟩

end RelCertifier.Progress
