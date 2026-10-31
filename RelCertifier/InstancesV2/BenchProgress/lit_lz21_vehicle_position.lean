import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def lit_lz21_vehicle_position_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"lit_lz21_vehicle_position", [
    ⟨"Um", "Um", true, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["U0", "Up"]⟩,
    ⟨"Um", "Um", false, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["U0", "Up"]⟩,
    ⟨"Um", "U0", true, [⟨"v", (1 : ℚ) / 20, true, (1 : ℚ) / 1⟩], ["Um", "Up"]⟩,
    ⟨"Um", "U0", false, [⟨"v", (1 : ℚ) / 10, false, (1 : ℚ) / 1⟩], ["Um", "Up"]⟩,
    ⟨"Um", "Up", true, [⟨"v", (1 : ℚ) / 20, true, (1 : ℚ) / 1⟩], ["Um", "U0"]⟩,
    ⟨"Um", "Up", false, [⟨"v", (1 : ℚ) / 10, false, (1 : ℚ) / 1⟩], ["Um", "U0"]⟩,
    ⟨"U0", "Um", true, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["U0", "Up"]⟩,
    ⟨"U0", "Um", false, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["U0", "Up"]⟩,
    ⟨"U0", "U0", true, [⟨"v", (1 : ℚ) / 10, false, (1 : ℚ) / 1⟩], ["Um", "Up"]⟩,
    ⟨"U0", "U0", false, [⟨"v", (1 : ℚ) / 10, false, (1 : ℚ) / 1⟩], ["Um", "Up"]⟩,
    ⟨"U0", "Up", true, [⟨"v", (1 : ℚ) / 10, false, (1 : ℚ) / 1⟩], ["Um", "U0"]⟩,
    ⟨"U0", "Up", false, [⟨"v", (1 : ℚ) / 10, false, (1 : ℚ) / 1⟩], ["Um", "U0"]⟩,
    ⟨"Up", "Um", true, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["U0", "Up"]⟩,
    ⟨"Up", "Um", false, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["U0", "Up"]⟩,
    ⟨"Up", "U0", true, [⟨"v", (1 : ℚ) / 10, false, (1 : ℚ) / 1⟩], ["Um", "Up"]⟩,
    ⟨"Up", "U0", false, [⟨"v", (1 : ℚ) / 10, false, (1 : ℚ) / 1⟩], ["Um", "Up"]⟩,
    ⟨"Up", "Up", true, [⟨"v", (1 : ℚ) / 10, false, (1 : ℚ) / 1⟩], ["Um", "U0"]⟩,
    ⟨"Up", "Up", false, [⟨"v", (1 : ℚ) / 10, false, (1 : ℚ) / 1⟩], ["Um", "U0"]⟩]⟩

end RelCertifier.Progress
