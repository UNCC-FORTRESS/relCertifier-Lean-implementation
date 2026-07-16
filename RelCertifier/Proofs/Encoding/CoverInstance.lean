/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# R5 — the generic throughout-instance layer

Per benchmark, per left window, the instances need: the REAL cover graph (lowered
systems at the emitted λ, flags from the emitted cover), the component list (lowered
`invComponents`, now total), and the `CoverCertM` bundle assembled from named Z3
verdicts whose query domains are EXACTLY the tool's stratified, cut-free queries
(`strataDomIR` over the emitted per-pair orders — the 33-benchmark battery scope;
the 13 cut-reliant benchmarks take the guard-threaded cut lift, follow-up).

Everything here is generic; the generated instances supply only literals and `decide`.
-/
import RelCertifier.Proofs.Encoding.CoverMulti
import RelCertifier.Proofs.Encoding.LoweringSide
import RelCertifier.Instances.BenchCovers
import RelCertifier.Trusted.OracleAPI

namespace RelCertifier
open DL Run

variable {n : ℕ}

/-! ## Host-level lowering pipelines (the pilot's, generalized) -/

/-- Lowered field of a mode (coordinate-wise; absent/failed ⟹ inert 0). -/
noncomputable def hostDyn (vars : List String) (n : ℕ) (s : Side) (m : Parse.PMode) :
    Fin n → Term (Var n) := fun i =>
  (((Run.dynOf vars n s m).map (fun f => ITerm.toHost (f i)))).getD (Term.const 0)

/-- Lowered evolution domain of a mode. -/
noncomputable def hostEvolve (vars : List String) (n : ℕ) (s : Side) (m : Parse.PMode) :
    Formula (Var n) :=
  ((Run.lowerF vars n s m.evolve).map IForm.toHost).getD Formula.tt

/-- Lowered guard of a mode. -/
noncomputable def hostGuard (vars : List String) (n : ℕ) (s : Side) (m : Parse.PMode) :
    Formula (Var n) :=
  ((Run.lowerF vars n s m.guard).map IForm.toHost).getD Formula.tt

/-- Lowered invariant components of a window. -/
noncomputable def hostComps (vars : List String) (n : ℕ) (f : Parse.PForm) :
    List (Term (Var n)) :=
  ((Oracle.invComponents vars n f).map (·.map ITerm.toHost)).getD []

/-! ## The real cover graph at the emitted flags -/

/-- The real mode for a flag row: joint system at λ, evolve domains; frozen-left dyn
system with σ-matched domains; σ-matched reposition regions. Mirrors `coverMode`'s
semantic content for the structural `cgReal` node. -/
noncomputable def realModeOf (vars : List String) (n : ℕ) (mL : Parse.PMode)
    (lam : ℚ) (f : ModeFlagsE) (mR : Parse.PMode) : RMode (Var n) :=
  let domLR := Formula.and (hostEvolve vars n Side.L mL) (hostEvolve vars n Side.R mR)
  { sys := jointSys (hostDyn vars n Side.L mL) (hostDyn vars n Side.R mR)
      (Term.const (lam : ℝ))
    dom := domLR
    weight := 1
    jointOK := f.jointOK
    region := Formula.and (Formula.and (hostGuard vars n Side.L mL)
        (hostGuard vars n Side.R mR)) domLR
    repoPreOK := f.repoPre
    regionPost := Formula.and (hostGuard vars n Side.R mR) domLR
    repoPostOK := f.repoPost
    dynSys := jointSys (fun _ => Term.const 0) (hostDyn vars n Side.R mR) (Term.const 1)
    dynDomPre := Formula.and domLR (hostGuard vars n Side.L mL)
    dynDomPost := domLR
    repoDynPreOK := f.dynPre
    repoDynPostOK := f.dynPost }

theorem realModeOf_sys (vars : List String) (n : ℕ) (mL : Parse.PMode) (lam : ℚ)
    (f : ModeFlagsE) (mR : Parse.PMode) :
    (realModeOf vars n mL lam f mR).sys =
      jointSys (hostDyn vars n Side.L mL) (hostDyn vars n Side.R mR)
        (Term.const (lam : ℝ)) := rfl

theorem realModeOf_dom (vars : List String) (n : ℕ) (mL : Parse.PMode) (lam : ℚ)
    (f : ModeFlagsE) (mR : Parse.PMode) :
    (realModeOf vars n mL lam f mR).dom =
      Formula.and (hostEvolve vars n Side.L mL) (hostEvolve vars n Side.R mR) := rfl

/-- The real cover graph: nodes = certificated flag rows paired with their IR modes,
edges = the structural builder's (same indices, same prunes). -/
noncomputable def realGraphOf (vars : List String) (n : ℕ) (p : Parse.PProblem)
    (mL : Parse.PMode) (lam : ℚ) (flags : List ModeFlagsE)
    (pruned : String → String → Bool) : SearchGraph (Var n) :=
  let nodes := flags.filter (·.isNode)
  let kSentinel := nodes.length
  let idxOf := fun (nm : String) => ((nodes.findIdx? (·.name == nm)).getD kSentinel)
  { modes := nodes.map (fun f =>
      match p.R.modes.find? (·.name == f.name) with
      | some mR => realModeOf vars n mL lam f mR
      | none => { sys := [], dom := Formula.tt, weight := 1, jointOK := false })
    edges := nodes.flatMap (fun f => (Run.succOf p f.name).map (fun tgt =>
      { src := idxOf f.name, tgt := idxOf tgt, guard := Formula.tt,
        pruned := pruned f.name tgt })) }

/-! ## Permutation transport (per-pair strata orders vs. the global component list) -/

theorem invAll_of_mem_equiv {gs gs' : List (Term (Var n))}
    (h : ∀ g, g ∈ gs ↔ g ∈ gs') {ω : State (Var n)}
    (hall : InvAllHolds gs ω) : InvAllHolds gs' ω :=
  fun g hg => hall g ((h g).mpr hg)

theorem segPresAll_of_mem_equiv {gs gs' : List (Term (Var n))}
    (h : ∀ g, g ∈ gs ↔ g ∈ gs') {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    (hp : SegPreservesAllOn gs sys dom) : SegPreservesAllOn gs' sys dom :=
  fun ν hν ω hsem g hg =>
    hp ν (fun g' hg' => hν g' ((h g').mp hg')) ω hsem g ((h g).mpr hg)

/-- Reindexing a list by a permutation of its index range is membership-equivalent. -/
theorem mem_equiv_of_index_perm (gs : List (Term (Var n))) (order : List Nat)
    (hperm : order.Perm (List.range gs.length)) :
    ∀ g, g ∈ order.map (fun j => gs.getD j (Term.const 0)) ↔ g ∈ gs := by
  intro g
  have hmap : (order.map (fun j => gs.getD j (Term.const 0))).Perm
      ((List.range gs.length).map (fun j => gs.getD j (Term.const 0))) :=
    hperm.map _
  rw [hmap.mem_iff]
  constructor
  · intro hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
    rw [List.mem_range] at hj
    rw [List.getD_eq_getElem gs _ hj]
    exact List.getElem_mem hj
  · intro hg
    obtain ⟨j, hj, hjg⟩ := List.getElem_of_mem hg
    refine List.mem_map.mpr ⟨j, List.mem_range.mpr hj, ?_⟩
    rw [List.getD_eq_getElem gs _ hj, hjg]

end RelCertifier
