import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def lit_csf25_salt_tank_hold_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"lit_csf25_salt_tank_hold", [
    ⟨"HoldDec", "Inc", true, [⟨"xp", (35 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Dec"]⟩]⟩

end RelCertifier.Progress
