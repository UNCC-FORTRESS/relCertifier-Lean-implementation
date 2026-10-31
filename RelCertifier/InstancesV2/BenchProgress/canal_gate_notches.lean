import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def canal_gate_notches_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"canal_gate_notches", [
    ⟨"RAISE", "N100", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N75", "N50", "N25"]⟩,
    ⟨"RAISE", "N100", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N75", "N50", "N25"]⟩,
    ⟨"RAISE", "N75", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N100", "N50", "N25"]⟩,
    ⟨"RAISE", "N75", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N100", "N50", "N25"]⟩,
    ⟨"RAISE", "N50", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N100", "N75", "N25"]⟩,
    ⟨"RAISE", "N50", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N100", "N75", "N25"]⟩,
    ⟨"RAISE", "N25", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N100", "N75", "N50"]⟩,
    ⟨"RAISE", "N25", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N100", "N75", "N50"]⟩,
    ⟨"HOLD", "N100", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N75", "N50", "N25"]⟩,
    ⟨"HOLD", "N100", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N75", "N50", "N25"]⟩,
    ⟨"HOLD", "N75", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N100", "N50", "N25"]⟩,
    ⟨"HOLD", "N75", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N100", "N50", "N25"]⟩,
    ⟨"HOLD", "N50", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N100", "N75", "N25"]⟩,
    ⟨"HOLD", "N50", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N100", "N75", "N25"]⟩,
    ⟨"HOLD", "N25", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N100", "N75", "N50"]⟩,
    ⟨"HOLD", "N25", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N100", "N75", "N50"]⟩,
    ⟨"LOWER", "N100", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N75", "N50", "N25"]⟩,
    ⟨"LOWER", "N100", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N75", "N50", "N25"]⟩,
    ⟨"LOWER", "N75", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N100", "N50", "N25"]⟩,
    ⟨"LOWER", "N75", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N100", "N50", "N25"]⟩,
    ⟨"LOWER", "N50", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N100", "N75", "N25"]⟩,
    ⟨"LOWER", "N50", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N100", "N75", "N25"]⟩,
    ⟨"LOWER", "N25", true, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N100", "N75", "N50"]⟩,
    ⟨"LOWER", "N25", false, [⟨"h", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N100", "N75", "N50"]⟩]⟩

end RelCertifier.Progress
