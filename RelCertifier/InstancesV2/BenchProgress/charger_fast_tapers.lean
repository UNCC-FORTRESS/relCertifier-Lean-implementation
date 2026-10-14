import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def charger_fast_tapers_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"charger_fast_tapers", [
    ⟨"BULK", "BULK", true, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB_SLOW", "ABSORB_FAST"]⟩,
    ⟨"BULK", "BULK", false, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB_SLOW", "ABSORB_FAST"]⟩,
    ⟨"BULK", "ABSORB_SLOW", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"BULK", "ABSORB_SLOW", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"BULK", "ABSORB_FAST", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["FULL"]⟩,
    ⟨"BULK", "ABSORB_FAST", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["FULL"]⟩,
    ⟨"ABSORB", "BULK", true, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB_SLOW", "ABSORB_FAST"]⟩,
    ⟨"ABSORB", "BULK", false, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB_SLOW", "ABSORB_FAST"]⟩,
    ⟨"ABSORB", "ABSORB_SLOW", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"ABSORB", "ABSORB_SLOW", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"ABSORB", "ABSORB_FAST", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["FULL"]⟩,
    ⟨"ABSORB", "ABSORB_FAST", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["FULL"]⟩,
    ⟨"FULL", "BULK", true, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB_SLOW", "ABSORB_FAST"]⟩,
    ⟨"FULL", "BULK", false, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB_SLOW", "ABSORB_FAST"]⟩,
    ⟨"FULL", "ABSORB_SLOW", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"FULL", "ABSORB_SLOW", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["FULL"]⟩,
    ⟨"FULL", "ABSORB_FAST", true, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["FULL"]⟩,
    ⟨"FULL", "ABSORB_FAST", false, [⟨"x", (99 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["FULL"]⟩]⟩

end RelCertifier.Progress
