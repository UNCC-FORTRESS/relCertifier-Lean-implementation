/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `RelCertifier` — library root

Re-exports the whole verified certifier. Import this to get the pipeline in one module.

Reading order (bottom-up, matching the paper's stages):
* `FlowCert` / `DISuperlevel` — Stage 1, the per-segment flow certificate (Lie derivative ⟹ `DI`).
* `NonConn` — Stage 2, the non-connection (Nagumo barrier) edge-pruning certificate.
* `Cover` / `Cover.Encoding` / `Cover.Coexec` — Stage 3, the cover (Definition 4) ⟹ Theorem 3,
  and its dL-rel ∀∃ encoding.
* `Checker` — the verified `decideCovered` that gates a sound `CERTIFIED`.
* `PicardBridge` / `CSFBridge` / `EncodingBridge` / `Reify` / `Reification`
  / `MultiSeg` / `ClockReduce` — the ∀∃ witness (`hExist`) and the CSF→NFM'25 modality chain.
* `EnvelopeChain{,M,R}` / `RepoPrefixR` / `WindowRF` / `Reparam` / `SplitCoupling` /
  `WindowGrowth` — the response layers the per-benchmark instances are built from
  (envelope, list-valued and mode-region loop invariants; right-only hop prefixes;
  k > 1 windows; λ-reparametrization; intra-window switching; the catch-up bound).
* `Instances.ModalBattery` — **the headline**: every certified benchmark's Theorem 3,
  with its axiom audit re-emitted on each build. Checking recipe:
  `docs/CERTIFICATION-CHECK.md`.
* `Smt` / `Oracle` / `Z3` / `OracleAPI` / `Parse` / `Run` — the trusted IO shell + runnable tool.

Note on retired routes: the settling/cadenced chain (`ClockedTop`, `GuardThreaded`'s
`GBoxAll` forms) is kept compiled but is **not** a live route — see `docs/READING-GUIDE.md`
§4 before citing anything from it. Superseded instances live in `RelCertifier/Archive/`.
-/
import RelCertifier.Core.FlowCert
import RelCertifier.Trusted.Smt
import RelCertifier.Trusted.Oracle
import RelCertifier.Checker.NonConn
import RelCertifier.Checker.Cover
import RelCertifier.Checker.Cover.Encoding
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.Run
import RelCertifier.Trusted.Z3
import RelCertifier.Trusted.OracleAPI
import RelCertifier.Proofs.Flow.DISuperlevel
import RelCertifier.Checker.Cover.Coexec
import RelCertifier.Checker.Checker
import RelCertifier.Proofs.Flow.PicardBridge
import RelCertifier.Archive.HExistDischarge
import RelCertifier.Proofs.Encoding.JointBridge
import RelCertifier.Archive.OdeProject
import RelCertifier.Archive.RightReachProject
import RelCertifier.Proofs.Encoding.BridgeUnit1
import RelCertifier.Proofs.Encoding.BridgeUnit2
import RelCertifier.Proofs.Encoding.BridgeUnit3
import RelCertifier.Proofs.Encoding.BridgeFinish
import RelCertifier.Proofs.Encoding.BridgeDischarge
import RelCertifier.Proofs.Encoding.BridgeReposition
import RelCertifier.Proofs.Encoding.RepositionFinish
import RelCertifier.Proofs.Encoding.RepositionDischarge
import RelCertifier.Proofs.Encoding.RepositionEndToEnd
import RelCertifier.Proofs.Encoding.UniformMultiflow
import RelCertifier.Archive.GapTwo
import RelCertifier.Archive.GapThreeFoundation
import RelCertifier.Archive.GapThreeTask2
import RelCertifier.Archive.GapThreeTask3
import RelCertifier.Archive.GapThreeRoverDemo
import RelCertifier.Archive.ProbeMvHd
import RelCertifier.Archive.GapThreeRoverTooling
import RelCertifier.Archive.GuardLegality
import RelCertifier.Proofs.Flow.WellFormedFlow
import RelCertifier.Proofs.Flow.WFBoundary
import RelCertifier.Proofs.Flow.MultisegLanding
import RelCertifier.Proofs.Flow.MultisegLandingBridge
import RelCertifier.Archive.RoverLandingInstance
import RelCertifier.Archive.DecayDischarge
import RelCertifier.Proofs.Soundness.UniformEvol
import RelCertifier.Proofs.Soundness.GuardThreaded
import RelCertifier.Proofs.Soundness.CutChannel
import RelCertifier.Checker.WellFormedChecker
import RelCertifier.Instances.SettlingInstances
import RelCertifier.Checker.TerrainChecker
import RelCertifier.Instances.TerrainInstances
import RelCertifier.Checker.AffineChecker
import RelCertifier.Instances.AffineInstances
import RelCertifier.Instances.AxiomCheck
import RelCertifier.Instances.BenchIR
import RelCertifier.Trusted.EmitIR
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Proofs.Soundness.CutLift
import RelCertifier.Proofs.Soundness.CutCover
import RelCertifier.Proofs.Soundness.CutCoverDischarge
import RelCertifier.Proofs.Soundness.CutLiftX
import RelCertifier.Instances.CutThroughoutBattery
import RelCertifier.Instances.EvolStrengthenings
import RelCertifier.Checker.Faithful
import RelCertifier.Proofs.Transfer.FaithfulBridge
import RelCertifier.Proofs.Transfer.FaithfulBridgeGuards
import RelCertifier.Proofs.Transfer.RealEndToEnd
import RelCertifier.Proofs.Transfer.FaithfulBridgePad
import RelCertifier.Instances.FaithfulCerts
import RelCertifier.Proofs.Transfer.Rescale
import RelCertifier.Proofs.Encoding.FvDischarge
import RelCertifier.Instances.RealInstances
import RelCertifier.Proofs.Encoding.ClockedTop
import RelCertifier.Proofs.Encoding.ClockReduce
import RelCertifier.Core.QFrac
import RelCertifier.Core.Reify
import RelCertifier.Archive.EndToEnd
import RelCertifier.Proofs.Encoding.CSFBridge
import RelCertifier.Proofs.Encoding.EncodingBridge
import RelCertifier.Proofs.Encoding.MultiSeg
import RelCertifier.Proofs.Encoding.Reification
import RelCertifier.Proofs.Encoding.ToolLevel
import RelCertifier.Proofs.Flow.StratifiedBarrier
import RelCertifier.Proofs.Flow.BoxViability
import RelCertifier.Proofs.Flow.BoxViabilityBounded
import RelCertifier.Proofs.Flow.ViabilityWiring
import RelCertifier.Instances.BenchCovers
import RelCertifier.Instances.BenchViability2
import RelCertifier.Instances.BenchCoverReplay
import RelCertifier.Proofs.Encoding.CoverMulti
import RelCertifier.Proofs.Encoding.RepoPrefix
import RelCertifier.Proofs.Encoding.EnvelopeChain
import RelCertifier.Verdicts.Coverage
import RelCertifier.Verdicts.RunModal
import RelCertifier.Verdicts.ModalPinTable
import RelCertifier.Verdicts.ModalTablePins
import RelCertifier.Verdicts.ModalCodePins
import RelCertifier.Verdicts.CoveragePins
import RelCertifier.Verdicts.RunNonConn
import RelCertifier.Verdicts.NonConnPins
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC
import RelCertifier.Archive.ThroughoutPilot
import RelCertifier.Instances.UniformPilot
import RelCertifier.Instances.ThroughoutBattery

-- The modal battery: every benchmark's Theorem 3 + its axiom audit (docs/CERTIFICATION-CHECK.md)
import RelCertifier.Instances.ModalBattery
import RelCertifier.InstancesV2.BatteryV2
