import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def engine_cooling_prelanding_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"engine_cooling_prelanding", [
    ⟨"Cool", "Heat", true, [⟨"temp", (100 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Cool"]⟩,
    ⟨"Heat", "Cool", true, [⟨"temp", (100 : ℚ) / 1, false, (1 : ℚ) / 2⟩], ["Heat"]⟩]⟩

end RelCertifier.Progress
