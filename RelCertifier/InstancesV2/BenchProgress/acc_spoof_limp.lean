import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def acc_spoof_limp_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"acc_spoof_limp", [
    ⟨"CRUISE", "NORMAL", true, [⟨"v", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ECO", "SPORT"]⟩,
    ⟨"CRUISE", "NORMAL", false, [⟨"v", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ECO", "SPORT"]⟩,
    ⟨"CRUISE", "ECO", true, [⟨"v", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL"]⟩,
    ⟨"CRUISE", "ECO", false, [⟨"v", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL"]⟩,
    ⟨"CRUISE", "SPORT", true, [⟨"v", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL"]⟩,
    ⟨"CRUISE", "SPORT", false, [⟨"v", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL"]⟩,
    ⟨"LIMP", "NORMAL", true, [⟨"v", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ECO", "SPORT"]⟩,
    ⟨"LIMP", "NORMAL", false, [⟨"v", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ECO", "SPORT"]⟩,
    ⟨"LIMP", "ECO", true, [⟨"v", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL"]⟩,
    ⟨"LIMP", "ECO", false, [⟨"v", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL"]⟩,
    ⟨"LIMP", "SPORT", true, [⟨"v", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL"]⟩,
    ⟨"LIMP", "SPORT", false, [⟨"v", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["NORMAL"]⟩]⟩

end RelCertifier.Progress
