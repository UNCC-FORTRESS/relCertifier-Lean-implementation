import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def autoclave_liquid_steambank_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"autoclave_liquid_steambank", [
    ⟨"HEAT", "EQUIL", true, [⟨"c", (122 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["EXPOSE"]⟩,
    ⟨"HEAT", "EXPOSE", true, [⟨"t", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["EXHAUST"]⟩,
    ⟨"EQUIL", "HEAT", true, [⟨"c", (122 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["EQUIL", "EXPOSE"]⟩,
    ⟨"EQUIL", "HEAT", false, [⟨"c", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["EQUIL", "EXPOSE"]⟩,
    ⟨"EQUIL", "EXPOSE", true, [⟨"c", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["EXHAUST"]⟩,
    ⟨"EXPOSE", "HEAT", true, [⟨"c", (122 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["EQUIL", "EXPOSE"]⟩,
    ⟨"EXPOSE", "HEAT", false, [⟨"c", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["EQUIL", "EXPOSE"]⟩,
    ⟨"EXPOSE", "EQUIL", true, [⟨"T", (121 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["EXPOSE"]⟩,
    ⟨"EXHAUST", "HEAT", true, [⟨"t", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["EQUIL", "EXPOSE"]⟩,
    ⟨"EXHAUST", "HEAT", false, [⟨"t", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["EQUIL", "EXPOSE"]⟩,
    ⟨"EXHAUST", "EQUIL", true, [⟨"c", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["EXPOSE"]⟩,
    ⟨"EXHAUST", "EQUIL", false, [⟨"c", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["EXPOSE"]⟩,
    ⟨"EXHAUST", "EXPOSE", true, [⟨"t", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["EXHAUST"]⟩,
    ⟨"EXHAUST", "EXPOSE", false, [⟨"t", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["EXHAUST"]⟩]⟩

end RelCertifier.Progress
