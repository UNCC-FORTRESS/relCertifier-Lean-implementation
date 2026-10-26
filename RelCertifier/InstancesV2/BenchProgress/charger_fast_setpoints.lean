import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def charger_fast_setpoints_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"charger_fast_setpoints", [
    ⟨"PRECHARGE", "PRECHARGE", true, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"PRECHARGE", "PRECHARGE", false, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"PRECHARGE", "BULK", true, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB"]⟩,
    ⟨"PRECHARGE", "BULK", false, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB"]⟩,
    ⟨"PRECHARGE", "ABSORB", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"PRECHARGE", "ABSORB", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"BULK", "PRECHARGE", true, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"BULK", "PRECHARGE", false, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"BULK", "BULK", true, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB"]⟩,
    ⟨"BULK", "BULK", false, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB"]⟩,
    ⟨"BULK", "ABSORB", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"BULK", "ABSORB", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"ABSORB", "PRECHARGE", true, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"ABSORB", "PRECHARGE", false, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"ABSORB", "BULK", true, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB"]⟩,
    ⟨"ABSORB", "BULK", false, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB"]⟩,
    ⟨"ABSORB", "ABSORB", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"ABSORB", "ABSORB", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"FULL", "PRECHARGE", true, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"FULL", "PRECHARGE", false, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"FULL", "BULK", true, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB"]⟩,
    ⟨"FULL", "BULK", false, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB"]⟩,
    ⟨"FULL", "ABSORB", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"FULL", "ABSORB", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"FAULT", "PRECHARGE", true, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"FAULT", "PRECHARGE", false, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"FAULT", "BULK", true, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB"]⟩,
    ⟨"FAULT", "BULK", false, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB"]⟩,
    ⟨"FAULT", "ABSORB", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"FAULT", "ABSORB", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩]⟩

end RelCertifier.Progress
