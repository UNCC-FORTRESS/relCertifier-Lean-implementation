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
import RelCertifier.FlowCert
import RelCertifier.Smt
import RelCertifier.Oracle
import RelCertifier.NonConn
import RelCertifier.Cover
import RelCertifier.Cover.Encoding
import RelCertifier.Parse
import RelCertifier.Run
import RelCertifier.Z3
import RelCertifier.OracleAPI
import RelCertifier.DISuperlevel
import RelCertifier.Cover.Coexec
import RelCertifier.Checker
import RelCertifier.PicardBridge
import RelCertifier.HExistDischarge
import RelCertifier.JointBridge
import RelCertifier.OdeProject
import RelCertifier.RightReachProject
import RelCertifier.BridgeUnit1
import RelCertifier.BridgeUnit2
import RelCertifier.BridgeUnit3
import RelCertifier.BridgeFinish
import RelCertifier.BridgeDischarge
import RelCertifier.BridgeReposition
import RelCertifier.RepositionFinish
import RelCertifier.RepositionDischarge
import RelCertifier.RepositionEndToEnd
import RelCertifier.GapTwo
import RelCertifier.GapThreeFoundation
import RelCertifier.GapThreeTask2
import RelCertifier.GapThreeTask3
import RelCertifier.GapThreeRoverDemo
import RelCertifier.ProbeMvHd
import RelCertifier.GapThreeRoverTooling
import RelCertifier.AxiomCheck
