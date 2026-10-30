/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `RelCertifier`: library root

Importing this module builds the whole development: the generic soundness layer, the
suite_v2 well-formedness battery with its axiom audit, the generic-bridge instances and the
refutation instances. The standalone (pre-bridge) route is archived on branch
`archive/legacy-2026-10` (`docs/CLEANUP-SCOPE.md`, planning record, last present at commit 29663d8).

* `Core/`: the per-segment flow certificate (Lie derivative ⟹ `DI`, `flow_certified`),
  rational reification.
* `Checker/`: the verified cover checker (`decideCovered`, `cover_sound`, `check_sound`),
  the cover-emission data types, the checked-cut certificates (`EvolStrengthening`, and
  `EvolStrengtheningX` for the widened channel), the non-connection certificate.
* `Proofs/`: the soundness development. `Flow/`: flow certificates, stratified barriers,
  viability faces. `Encoding/`: the dL-rel ∀∃ encoding of Theorem 3 (CSF/NFM'25 bridge,
  joint segments, the dynamic right-only reposition prefixes, envelope/window chains,
  mode handoffs, sink regions, the non-connection bridge). `Soundness/`: the cut channel
  lifted to the kernel (`CutLift`, and `CutLiftX` for the widened channel). `Transfer/`:
  the scaled-model transfer lemmas.
* `Trusted/`: the IO shell the proofs do not cover (parser, lowering, SMT printer, Z3
  session, the certifier `OracleAPI.certify`, emitters); its single proof-facing interface
  is `z3_unsat_sound`.
* `InstancesV2/Bridge`: **the headline**, Theorem 3 of every `benchmarks/suite_v2`
  benchmark (and the two choice exhibits) through the generic bridge
  (`Proofs/Encoding/Emitted/`): structural bundles decided in the kernel, Assumption 1
  transported from the well-formedness battery, the Z3 verdicts assumed as the groups
  `relcert-bridge-verdicts` discharges (`docs/BRIDGE.md`).
* `InstancesV2/WellFormedBattery`: the paper's Assumption 1 (Well-Formedness) of each right
  model as a separate, axiom-audited result (`WellFormedR`, `Proofs/Encoding/WellFormedR`),
  one self-contained `InstancesV2/WellFormed/<B>.lean` per right model (`docs/WELLFORMED.md`).
* `InstancesV2/Refute`: the kernel refutations of the known-false invariant variants
  (`docs/REFUTATION-RESULTS.md`).
* `VerdictsV2/` and `Verdicts/`: the runner tables (`relcert --check-quick-v2`, the bridge,
  refutation and progress runners) and the shared verdict combinators and pins.
  `InstancesV2/AxiomCheck` is the axiom audit of the generic theorems.

Checking recipe: `docs/CERTIFICATION-CHECK.md`.
-/
import RelCertifier.Checker.AffineChecker
import RelCertifier.Checker.Checker
import RelCertifier.Checker.Cover
import RelCertifier.Checker.Cover.Coexec
import RelCertifier.Checker.Cover.Encoding
import RelCertifier.Checker.CoverEmit
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.Checker.Faithful
import RelCertifier.Checker.NonConn
import RelCertifier.Checker.TerrainChecker
import RelCertifier.Checker.WellFormedChecker
import RelCertifier.Core.FlowCert
import RelCertifier.Core.QFrac
import RelCertifier.Core.Reify
import RelCertifier.Proofs.Encoding.BridgeDischarge
import RelCertifier.Proofs.Encoding.BridgeFinish
import RelCertifier.Proofs.Encoding.BridgeReposition
import RelCertifier.Proofs.Encoding.BridgeUnit1
import RelCertifier.Proofs.Encoding.BridgeUnit2
import RelCertifier.Proofs.Encoding.BridgeUnit3
import RelCertifier.Proofs.Encoding.CSFBridge
import RelCertifier.Proofs.Encoding.CanonicalInv
import RelCertifier.Proofs.Encoding.ClockReduce
import RelCertifier.Proofs.Encoding.ClockedTop
import RelCertifier.Proofs.Encoding.CoverExtract
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Proofs.Encoding.CoverMulti
import RelCertifier.Proofs.Encoding.CutComposition
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.EncodingBridge
import RelCertifier.Proofs.Encoding.EnvelopeChain
import RelCertifier.Proofs.Encoding.EnvelopeChainM
import RelCertifier.Proofs.Encoding.EnvelopeChainR
import RelCertifier.Proofs.Encoding.FvDischarge
import RelCertifier.Proofs.Encoding.JointBridge
import RelCertifier.Proofs.Encoding.LoweringSide
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.Proofs.Encoding.LeftAutUniform
import RelCertifier.Proofs.Encoding.ModeHandoff
import RelCertifier.Proofs.Encoding.MultiSeg
import RelCertifier.Proofs.Encoding.NonConnBridge
import RelCertifier.Proofs.Encoding.Reification
import RelCertifier.Proofs.Encoding.Reparam
import RelCertifier.Proofs.Encoding.Stretching
import RelCertifier.Proofs.Encoding.RepoPrefix
import RelCertifier.Proofs.Encoding.RepoPrefixR
import RelCertifier.Proofs.Encoding.RepositionDischarge
import RelCertifier.Proofs.Encoding.RepositionEndToEnd
import RelCertifier.Proofs.Encoding.RepositionFinish
import RelCertifier.Proofs.Encoding.ReplayDyn
import RelCertifier.Proofs.Encoding.ReplayEngine
import RelCertifier.Proofs.Encoding.SplitCoupling
import RelCertifier.Proofs.Encoding.StrictInv
import RelCertifier.Proofs.Encoding.StrictCouple
import RelCertifier.Proofs.Encoding.Emitted.StrictAnchor
import RelCertifier.Proofs.Encoding.Emitted.StrictKeyed
import RelCertifier.Proofs.Encoding.Emitted.StrictRun
import RelCertifier.Proofs.Encoding.Theorem3GeneralS
import RelCertifier.Proofs.Encoding.ModeHandoffStrict
import RelCertifier.Proofs.Encoding.ToolLevel
import RelCertifier.Proofs.Encoding.UniformFvDischarge
import RelCertifier.Proofs.Encoding.UniformMultiflow
import RelCertifier.Proofs.Encoding.WellFormedLadder
import RelCertifier.Proofs.Encoding.WellFormedTerrain
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Encoding.WindowGrowth
import RelCertifier.Proofs.Encoding.WindowRF
import RelCertifier.Proofs.Flow.BoxViability
import RelCertifier.Proofs.Flow.BoxViabilityBounded
import RelCertifier.Proofs.Flow.DIStrictOpen
import RelCertifier.Proofs.Flow.DISuperlevel
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.Proofs.Flow.MultisegLanding
import RelCertifier.Proofs.Flow.MultisegLandingBridge
import RelCertifier.Proofs.Flow.PicardBridge
import RelCertifier.Proofs.Flow.StratifiedBarrier
import RelCertifier.Proofs.Flow.StratifiedBarrierStrict
import RelCertifier.Proofs.Flow.StrictAtoms
import RelCertifier.Proofs.Flow.StratifiedFaces
import RelCertifier.Proofs.Flow.ViabilityWiring
import RelCertifier.Proofs.Flow.WFBoundary
import RelCertifier.Proofs.Flow.WellFormedFlow
import RelCertifier.Proofs.Soundness.CutChannel
import RelCertifier.Proofs.Soundness.CutCover
import RelCertifier.Proofs.Soundness.CutCoverDischarge
import RelCertifier.Proofs.Soundness.CutLift
import RelCertifier.Proofs.Soundness.CutLiftX
import RelCertifier.Proofs.Soundness.GuardThreaded
import RelCertifier.Proofs.Soundness.StrictCover
import RelCertifier.Proofs.Soundness.UniformEvol
import RelCertifier.Proofs.Transfer.FaithfulBridge
import RelCertifier.Proofs.Transfer.Rescale
import RelCertifier.Trusted.EmitIR
import RelCertifier.Trusted.Handoff
import RelCertifier.Trusted.HandoffStrict
import RelCertifier.Trusted.InvComponents
import RelCertifier.Trusted.InvStrictFlags
import RelCertifier.Trusted.JointVars
import RelCertifier.Trusted.KeyAudit
import RelCertifier.Trusted.NonConnQuery
import RelCertifier.Trusted.Oracle
import RelCertifier.Trusted.OracleAPI
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.Run
import RelCertifier.Trusted.Smt
import RelCertifier.Trusted.ViabilityEmit
import RelCertifier.Trusted.WellFormedCheck
import RelCertifier.Trusted.Z3
import RelCertifier.InstancesV2.AxiomCheck
import RelCertifier.VerdictsV2.ModalDynX
import RelCertifier.VerdictsV2.ModalXStrict
import RelCertifier.InstancesV2.WellFormedBattery
import RelCertifier.InstancesV2.Bridge
import RelCertifier.Proofs.Encoding.Emitted.Refute
import RelCertifier.Proofs.Encoding.Emitted.RefuteFlow
import RelCertifier.VerdictsV2.RunRefute
import RelCertifier.InstancesV2.Refute
