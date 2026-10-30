import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def boiler_purge_vfd_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"boiler_purge_vfd", [
    ⟨"FIRE", "PURGE", true, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 128⟩], ["FIRE"]⟩,
    ⟨"FIRE", "PURGE", false, [⟨"v", (5 : ℚ) / 1, true, (1 : ℚ) / 128⟩], ["FIRE"]⟩]⟩

end RelCertifier.Progress
