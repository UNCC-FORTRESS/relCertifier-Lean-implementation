import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def charger_fast_setpoints_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"charger_fast_setpoints", [
    ⟨"BULK", "BULK", true, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB"]⟩,
    ⟨"BULK", "BULK", false, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB"]⟩,
    ⟨"BULK", "ABSORB", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"BULK", "ABSORB", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"ABSORB", "BULK", true, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB"]⟩,
    ⟨"ABSORB", "BULK", false, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB"]⟩,
    ⟨"ABSORB", "ABSORB", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"ABSORB", "ABSORB", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"FULL", "BULK", true, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB"]⟩,
    ⟨"FULL", "BULK", false, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB"]⟩,
    ⟨"FULL", "ABSORB", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"FULL", "ABSORB", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩]⟩

end RelCertifier.Progress
