import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def zone_lightmass_schedule_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"zone_lightmass_schedule", [
    ⟨"COMFORT", "STANDBY", .hop, false, ["COMFORT"]⟩,
    ⟨"COMFORT", "ECONOMY", .hop, false, ["COMFORT"]⟩,
    ⟨"COMFORT", "STANDBY", .hop, true, ["COMFORT"]⟩,
    ⟨"COMFORT", "ECONOMY", .hop, true, ["COMFORT"]⟩,
    ⟨"ECONOMY", "COMFORT", .hop, false, ["ECONOMY"]⟩,
    ⟨"ECONOMY", "STANDBY", .hop, false, ["ECONOMY"]⟩,
    ⟨"ECONOMY", "COMFORT", .hop, true, ["ECONOMY"]⟩,
    ⟨"ECONOMY", "STANDBY", .hop, true, ["ECONOMY"]⟩]⟩

end RelCertifier.Choice
