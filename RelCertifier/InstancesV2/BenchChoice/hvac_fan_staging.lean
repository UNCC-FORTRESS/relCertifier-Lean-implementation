import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def hvac_fan_staging_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"hvac_fan_staging", [
    ⟨"LOW", "MED", .hop, true, ["LOW"]⟩,
    ⟨"LOW", "HIGH", .hop, true, ["LOW"]⟩,
    ⟨"MED", "LOW", .hop, true, ["MED"]⟩,
    ⟨"MED", "HIGH", .hop, true, ["MED"]⟩,
    ⟨"HIGH", "LOW", .hop, true, ["HIGH"]⟩,
    ⟨"HIGH", "MED", .hop, true, ["HIGH"]⟩]⟩

end RelCertifier.Choice
