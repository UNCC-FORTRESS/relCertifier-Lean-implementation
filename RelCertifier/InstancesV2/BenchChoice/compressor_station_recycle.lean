import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def compressor_station_recycle_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"compressor_station_recycle", [
    ⟨"HIGH", "LOW", .hop, true, ["MED"]⟩,
    ⟨"HIGH", "HIGH", .hop, true, ["MED"]⟩,
    ⟨"MED", "LOW", .hop, true, ["MED"]⟩,
    ⟨"MED", "HIGH", .hop, true, ["MED"]⟩,
    ⟨"LOW", "MED", .hop, true, ["LOW"]⟩,
    ⟨"LOW", "HIGH", .hop, true, ["LOW"]⟩]⟩

end RelCertifier.Choice
