import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def flaps_slow_approach_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"flaps_slow_approach", [
    ⟨"CONF2", "EXT", true, [⟨"f", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["CONF2"]⟩,
    ⟨"CONF2", "EXT", false, [⟨"f", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["CONF2"]⟩]⟩

end RelCertifier.Progress
