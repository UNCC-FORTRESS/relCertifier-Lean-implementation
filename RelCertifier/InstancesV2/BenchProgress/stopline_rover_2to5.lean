import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def stopline_rover_2to5_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"stopline_rover_2to5", [
    ⟨"BRAKE", "CRUISE", true, [⟨"p", (100 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BRAKE"]⟩,
    ⟨"BRAKE", "CRUISE", false, [⟨"p", (100 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BRAKE"]⟩,
    ⟨"BRAKE", "BRAKE", true, [⟨"v", (7 : ℚ) / 20, false, (1 : ℚ) / 1⟩], ["STOP"]⟩,
    ⟨"BRAKE", "BRAKE", false, [⟨"v", (7 : ℚ) / 20, false, (1 : ℚ) / 1⟩], ["STOP"]⟩,
    ⟨"STOP", "CRUISE", true, [⟨"p", (100 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BRAKE"]⟩,
    ⟨"STOP", "CRUISE", false, [⟨"p", (100 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BRAKE"]⟩,
    ⟨"STOP", "BRAKE", true, [⟨"v", (7 : ℚ) / 20, false, (1 : ℚ) / 1⟩], ["STOP"]⟩,
    ⟨"STOP", "BRAKE", false, [⟨"v", (7 : ℚ) / 20, false, (1 : ℚ) / 1⟩], ["STOP"]⟩]⟩

end RelCertifier.Progress
