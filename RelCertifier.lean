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
* `PicardBridge` / `HExistDischarge` / `CSFBridge` / `EncodingBridge` / `Reify` / `Reification`
  / `MultiSeg` / `ClockReduce` — the ∀∃ witness (`hExist`) and the CSF→NFM'25 modality chain.
* `Smt` / `Oracle` / `Z3` / `OracleAPI` / `Parse` / `Run` — the trusted IO shell + runnable tool.
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
import RelCertifier.Proofs.Flow.HExistDischarge
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
import RelCertifier.Instances.EvolStrengthenings
import RelCertifier.Checker.Faithful
import RelCertifier.Proofs.Transfer.FaithfulBridge
import RelCertifier.Proofs.Transfer.FaithfulBridgeGuards
import RelCertifier.Proofs.Transfer.RealEndToEnd
import RelCertifier.Proofs.Transfer.FaithfulBridgePad
import RelCertifier.Instances.FaithfulCerts
import RelCertifier.Proofs.Transfer.Rescale
import RelCertifier.Proofs.Encoding.FvDischarge
import RelCertifier.Instances.Mega
import RelCertifier.Instances.RealInstances
import RelCertifier.Proofs.Encoding.ClockedTop
import RelCertifier.Proofs.Encoding.ClockReduce
import RelCertifier.Core.QFrac
import RelCertifier.Core.Reify
import RelCertifier.Instances.EndToEnd
import RelCertifier.Proofs.Encoding.CSFBridge
import RelCertifier.Proofs.Encoding.EncodingBridge
import RelCertifier.Proofs.Encoding.MultiSeg
import RelCertifier.Proofs.Encoding.Reification
import RelCertifier.Proofs.Encoding.ToolLevel
import RelCertifier.Proofs.Flow.StratifiedBarrier
import RelCertifier.Proofs.Flow.BoxViability
import RelCertifier.Instances.BenchCovers
import RelCertifier.Instances.BenchCoverReplay
import RelCertifier.Proofs.Encoding.CoverMulti
import RelCertifier.Proofs.Encoding.RepoPrefix
import RelCertifier.Proofs.Encoding.EnvelopeChain
import RelCertifier.Instances.WatertankModal
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC
import RelCertifier.Instances.ThroughoutPilot
import RelCertifier.Instances.UniformPilot
import RelCertifier.Instances.WatertankThroughout
import RelCertifier.Instances.ThroughoutBattery
