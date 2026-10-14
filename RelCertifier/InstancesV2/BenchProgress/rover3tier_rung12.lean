import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def rover3tier_rung12_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"rover3tier_rung12", [
    ⟨"ACCEL", "ACCEL", true, [⟨"v", (3 : ℚ) / 5, true, (1 : ℚ) / 2⟩], ["COAST"]⟩,
    ⟨"ACCEL", "ACCEL", false, [⟨"v", (3 : ℚ) / 5, true, (1 : ℚ) / 2⟩], ["COAST"]⟩,
    ⟨"COAST", "ACCEL", true, [⟨"v", (3 : ℚ) / 5, true, (1 : ℚ) / 2⟩], ["COAST"]⟩,
    ⟨"COAST", "ACCEL", false, [⟨"v", (3 : ℚ) / 5, true, (1 : ℚ) / 2⟩], ["COAST"]⟩]⟩

end RelCertifier.Progress
