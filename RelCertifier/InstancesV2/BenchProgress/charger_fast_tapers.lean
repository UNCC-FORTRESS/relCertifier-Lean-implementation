import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def charger_fast_tapers_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"charger_fast_tapers", [
    ⟨"PRECHARGE", "PRECHARGE", true, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"PRECHARGE", "PRECHARGE", false, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"PRECHARGE", "BULK", true, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB_SLOW", "ABSORB_FAST"]⟩,
    ⟨"PRECHARGE", "BULK", false, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB_SLOW", "ABSORB_FAST"]⟩,
    ⟨"PRECHARGE", "ABSORB_SLOW", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"PRECHARGE", "ABSORB_SLOW", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"PRECHARGE", "ABSORB_FAST", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["FULL"]⟩,
    ⟨"PRECHARGE", "ABSORB_FAST", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["FULL"]⟩,
    ⟨"BULK", "PRECHARGE", true, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"BULK", "PRECHARGE", false, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"BULK", "BULK", true, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB_SLOW", "ABSORB_FAST"]⟩,
    ⟨"BULK", "BULK", false, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB_SLOW", "ABSORB_FAST"]⟩,
    ⟨"BULK", "ABSORB_SLOW", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"BULK", "ABSORB_SLOW", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"BULK", "ABSORB_FAST", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["FULL"]⟩,
    ⟨"BULK", "ABSORB_FAST", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["FULL"]⟩,
    ⟨"ABSORB", "PRECHARGE", true, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"ABSORB", "PRECHARGE", false, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"ABSORB", "BULK", true, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB_SLOW", "ABSORB_FAST"]⟩,
    ⟨"ABSORB", "BULK", false, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB_SLOW", "ABSORB_FAST"]⟩,
    ⟨"ABSORB", "ABSORB_SLOW", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"ABSORB", "ABSORB_SLOW", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"ABSORB", "ABSORB_FAST", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["FULL"]⟩,
    ⟨"ABSORB", "ABSORB_FAST", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["FULL"]⟩,
    ⟨"FULL", "PRECHARGE", true, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"FULL", "PRECHARGE", false, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"FULL", "BULK", true, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB_SLOW", "ABSORB_FAST"]⟩,
    ⟨"FULL", "BULK", false, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB_SLOW", "ABSORB_FAST"]⟩,
    ⟨"FULL", "ABSORB_SLOW", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"FULL", "ABSORB_SLOW", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"FULL", "ABSORB_FAST", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["FULL"]⟩,
    ⟨"FULL", "ABSORB_FAST", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["FULL"]⟩,
    ⟨"FAULT", "PRECHARGE", true, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"FAULT", "PRECHARGE", false, [⟨"x", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["BULK"]⟩,
    ⟨"FAULT", "BULK", true, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB_SLOW", "ABSORB_FAST"]⟩,
    ⟨"FAULT", "BULK", false, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB_SLOW", "ABSORB_FAST"]⟩,
    ⟨"FAULT", "ABSORB_SLOW", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"FAULT", "ABSORB_SLOW", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"FAULT", "ABSORB_FAST", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["FULL"]⟩,
    ⟨"FAULT", "ABSORB_FAST", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["FULL"]⟩]⟩

end RelCertifier.Progress
