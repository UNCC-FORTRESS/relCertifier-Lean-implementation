import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def turbine_startup_gearratio_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"turbine_startup_gearratio", [
    ⟨"SPINUP", "GUST", .hop, true, ["REG"]⟩,
    ⟨"RAMP", "GUST", .hop, true, ["REG"]⟩,
    ⟨"GEN", "GUST", .hop, true, ["REG"]⟩,
    ⟨"REG", "GUST", .hop, true, ["REG"]⟩,
    ⟨"GUST", "REG", .hop, true, ["GUST"]⟩]⟩

end RelCertifier.Choice
