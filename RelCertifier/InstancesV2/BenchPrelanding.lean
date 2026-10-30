/- suite_v2 pre-landing-record aggregator (GENERATED — `scripts/gen_v2_data.py`): the
pre-landing records of the benchmarks with the opt-in `prelanding = true`
(`docs/PRELANDING.md`); a benchmark without the key has none. -/
import RelCertifier.Trusted.PrelandEmit
import RelCertifier.InstancesV2.BenchPrelanding.lit_nahs25_engine_cooling

namespace RelCertifier.Preland

def prelandTableV2 : List (String × PrelandEmitE) := [
  ("lit_nahs25_engine_cooling", lit_nahs25_engine_cooling_coverV2_prelanding) ]

end RelCertifier.Preland
