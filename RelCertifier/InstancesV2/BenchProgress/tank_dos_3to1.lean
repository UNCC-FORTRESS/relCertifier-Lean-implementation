import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def tank_dos_3to1_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"tank_dos_3to1", [
    ⟨"P2", "P3", true, [⟨"w", (14 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["P4"]⟩,
    ⟨"P2", "P4", true, [⟨"w", (18 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["P5"]⟩,
    ⟨"P3", "P2", true, [⟨"w", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["P3"]⟩,
    ⟨"P3", "P2", false, [⟨"w", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["P3"]⟩,
    ⟨"P3", "P4", true, [⟨"w", (18 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["P5"]⟩,
    ⟨"P4", "P2", true, [⟨"w", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["P3"]⟩,
    ⟨"P4", "P2", false, [⟨"w", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["P3"]⟩,
    ⟨"P4", "P3", true, [⟨"w", (14 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["P4"]⟩,
    ⟨"P4", "P3", false, [⟨"w", (14 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["P4"]⟩,
    ⟨"P5", "P2", true, [⟨"w", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["P3"]⟩,
    ⟨"P5", "P2", false, [⟨"w", (10 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["P3"]⟩,
    ⟨"P5", "P3", true, [⟨"w", (14 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["P4"]⟩,
    ⟨"P5", "P3", false, [⟨"w", (14 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["P4"]⟩,
    ⟨"P5", "P4", true, [⟨"w", (18 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["P5"]⟩,
    ⟨"P5", "P4", false, [⟨"w", (18 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["P5"]⟩]⟩

end RelCertifier.Progress
