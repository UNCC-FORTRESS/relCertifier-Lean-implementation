import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def stopline_friction_mixed_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"stopline_friction_mixed", [
    ⟨"CRUISE", "BRAKE", true, [⟨"p", (100 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STOP"]⟩,
    ⟨"BRAKE", "CRUISE", true, [⟨"p", (100 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BRAKE"]⟩,
    ⟨"BRAKE", "CRUISE", false, [⟨"p", (100 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BRAKE"]⟩,
    ⟨"BRAKE", "BRAKE", true, [⟨"b", (2 : ℚ) / 1, true, (1 : ℚ) / 1⟩, ⟨"v", (7 : ℚ) / 20, false, (1 : ℚ) / 1⟩], ["STOP"]⟩,
    ⟨"BRAKE", "BRAKE", false, [⟨"b", (2 : ℚ) / 1, true, (1 : ℚ) / 1⟩, ⟨"v", (7 : ℚ) / 20, false, (1 : ℚ) / 1⟩], ["STOP"]⟩,
    ⟨"STOP", "CRUISE", true, [⟨"p", (100 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BRAKE"]⟩,
    ⟨"STOP", "CRUISE", false, [⟨"p", (100 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BRAKE"]⟩,
    ⟨"STOP", "BRAKE", true, [⟨"b", (2 : ℚ) / 1, true, (1 : ℚ) / 1⟩, ⟨"v", (7 : ℚ) / 20, false, (1 : ℚ) / 1⟩], ["STOP"]⟩,
    ⟨"STOP", "BRAKE", false, [⟨"b", (2 : ℚ) / 1, true, (1 : ℚ) / 1⟩, ⟨"v", (7 : ℚ) / 20, false, (1 : ℚ) / 1⟩], ["STOP"]⟩]⟩

end RelCertifier.Progress
