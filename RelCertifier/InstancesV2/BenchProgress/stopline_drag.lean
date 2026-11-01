import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def stopline_drag_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"stopline_drag", [
    ⟨"CRUISE", "BRAKE", true, [⟨"p", (100 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STOP"]⟩,
    ⟨"BRAKE", "CRUISE", true, [⟨"p", (100 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BRAKE"]⟩,
    ⟨"BRAKE", "CRUISE", false, [⟨"p", (100 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BRAKE"]⟩,
    ⟨"STOP", "CRUISE", true, [⟨"p", (100 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BRAKE"]⟩,
    ⟨"STOP", "CRUISE", false, [⟨"p", (100 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BRAKE"]⟩]⟩

end RelCertifier.Progress
