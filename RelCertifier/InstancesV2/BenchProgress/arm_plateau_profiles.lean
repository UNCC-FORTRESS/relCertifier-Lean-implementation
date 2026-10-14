import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def arm_plateau_profiles_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"arm_plateau_profiles", [
    ⟨"Accelerate", "ApproachA", true, [⟨"theta", (7 : ℚ) / 20, true, (1 : ℚ) / 2⟩], ["ApproachB", "ApproachCfast", "ApproachCslow", "Hold"]⟩,
    ⟨"Accelerate", "ApproachA", false, [⟨"theta", (7 : ℚ) / 20, true, (1 : ℚ) / 2⟩], ["ApproachB", "ApproachCfast", "ApproachCslow", "Hold"]⟩,
    ⟨"Accelerate", "ApproachB", true, [⟨"theta", (1 : ℚ) / 2, true, (1 : ℚ) / 4⟩], ["ApproachCfast", "ApproachCslow", "Hold"]⟩,
    ⟨"Accelerate", "ApproachB", false, [⟨"theta", (1 : ℚ) / 2, true, (1 : ℚ) / 4⟩], ["ApproachCfast", "ApproachCslow", "Hold"]⟩,
    ⟨"Accelerate", "ApproachCfast", true, [⟨"theta", (3 : ℚ) / 5, true, (1 : ℚ) / 4⟩], ["Hold"]⟩,
    ⟨"Accelerate", "ApproachCfast", false, [⟨"theta", (3 : ℚ) / 5, true, (1 : ℚ) / 4⟩], ["Hold"]⟩,
    ⟨"Accelerate", "ApproachCslow", true, [⟨"theta", (3 : ℚ) / 5, true, (1 : ℚ) / 8⟩], ["Hold"]⟩,
    ⟨"Accelerate", "ApproachCslow", false, [⟨"theta", (3 : ℚ) / 5, true, (1 : ℚ) / 8⟩], ["Hold"]⟩,
    ⟨"Brake", "ApproachA", true, [⟨"theta", (7 : ℚ) / 20, true, (1 : ℚ) / 2⟩], ["ApproachB", "ApproachCfast", "ApproachCslow", "Hold"]⟩,
    ⟨"Brake", "ApproachA", false, [⟨"theta", (7 : ℚ) / 20, true, (1 : ℚ) / 2⟩], ["ApproachB", "ApproachCfast", "ApproachCslow", "Hold"]⟩,
    ⟨"Brake", "ApproachB", true, [⟨"theta", (1 : ℚ) / 2, true, (1 : ℚ) / 4⟩], ["ApproachCfast", "ApproachCslow", "Hold"]⟩,
    ⟨"Brake", "ApproachB", false, [⟨"theta", (1 : ℚ) / 2, true, (1 : ℚ) / 4⟩], ["ApproachCfast", "ApproachCslow", "Hold"]⟩,
    ⟨"Brake", "ApproachCfast", true, [⟨"theta", (3 : ℚ) / 5, true, (1 : ℚ) / 4⟩], ["Hold"]⟩,
    ⟨"Brake", "ApproachCfast", false, [⟨"theta", (3 : ℚ) / 5, true, (1 : ℚ) / 4⟩], ["Hold"]⟩,
    ⟨"Brake", "ApproachCslow", true, [⟨"theta", (3 : ℚ) / 5, true, (1 : ℚ) / 8⟩], ["Hold"]⟩,
    ⟨"Brake", "ApproachCslow", false, [⟨"theta", (3 : ℚ) / 5, true, (1 : ℚ) / 8⟩], ["Hold"]⟩]⟩

end RelCertifier.Progress
