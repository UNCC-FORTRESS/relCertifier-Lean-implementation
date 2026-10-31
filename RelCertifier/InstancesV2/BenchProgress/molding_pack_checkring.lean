import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def molding_pack_checkring_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"molding_pack_checkring", [
    ⟨"COOL", "HOLD", true, [⟨"t", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["COOL"]⟩,
    ⟨"COOL", "HOLD", false, [⟨"t", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["COOL"]⟩]⟩

end RelCertifier.Progress
