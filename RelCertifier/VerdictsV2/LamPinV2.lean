/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The stretch pin: emitted cover ↔ verdict pack, per pairing

Each benchmark's instance assumes its flow obligations as `Verd l q` hypotheses, and
`VerdictsV2/PinsV2.lean` ties every such hypothesis to a `packsV2` row, whose stretch
`lamN / lamD` is the one the runner rebuilds the Z3 query at. The tool's emitted cover
(`InstancesV2/BenchCovers/*.lean`, `--emit-cover`) carries the stretch at which it certified
each pairing (`PairStrataE.lamN / lamD`). This file closes the remaining gap by kernel
computation: for every pack row, the row's left index names the emitted window, its right index
names the strata entry of the right mode of that index, and the row's stretch is that entry's
stretch. So the stretch the instance replays IS the stretch the tool certified the pairing at.
With the per-pairing fallback (`Trusted/OracleAPI.lean`, `coverMode`) the stretch may differ
between the right modes of one window; the pin is per pairing and does not care.
-/
import RelCertifier.VerdictsV2.RunV2
import RelCertifier.InstancesV2.BenchCovers

set_option maxRecDepth 100000

namespace RelCertifier.VerdictsV2

open RelCertifier RelCertifier.Parse

/-- A pack row is pinned to its cover: the row's indices name the window and the right mode,
and the row's stretch is the stretch the cover certified that pairing at. -/
def packLamPinned (c : CoverEmitE) (p : Parse.PProblem) (r : PackV2) : Bool :=
  match c.covers[r.l]?, p.L.modes[r.l]?, p.R.modes[r.m]? with
  | some lc, some ml, some mr =>
    lc.mL == ml.name &&
    (match lc.strata[r.m]? with
     | some ps => ps.mR == mr.name && ps.lamN == r.lamN && ps.lamD == r.lamD
     | none => false)
  | _, _, _ => false

/-- Every pack row of the suite is pinned to the emitted cover of its benchmark. -/
def lamPinnedV2 : Bool :=
  packsV2.all (fun r =>
    match coverTableV2.find? (·.1 == r.bench), benchIRTableV2.find? (·.1 == r.bench) with
    | some (_, c), some (_, p) => packLamPinned c p r
    | _, _ => false)

theorem lamPinnedV2_true : lamPinnedV2 = true := by decide

end RelCertifier.VerdictsV2
