import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def ventilator_vc_cuffleak_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"ventilator_vc_cuffleak", [
    ⟨"EXP", "INSP", true, [⟨"s", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["EXP"]⟩]⟩

end RelCertifier.Progress
