/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The queries of the generic bridge

The Z3 queries a benchmark's generic instance rests on besides the flow packs
(`modalVerdXQueries`), the reposition packs, the handoff queries (`Handoff.queryOf`), the
non-connection pairs (`NonConn.queries`) and the progress queries (`Progress.progressQueries`):

* `stayQueryOf`: the O2 query of one kept atom of a mode, by the route its certificate
  records (`checkedCutX`'s `diRoutes`: route B `dom ∧ g = 0 ∧ ġ ≥ 0`, route A `dom ∧ ġ > 0`,
  route C `dom ∧ g ≥ 0 ∧ ġ > 0`, over the mode's evolve domain narrowed by the atom's `given`
  forms; the one-sided Lie derivative of the atom's own side at stretch 1). A rational route
  (shape, frozen, linear, derived) is re-checked by route C, which each of them implies.
* `admQueryOf`: the admissibility query of a (left, right) start, `guardL ∧ guardR ∧ ⋀ gᵢ ≤ 0`
  (`OracleAPI.admissible`); `unsat` means no admissible start.

Pure builders; the runner issues them, the bridge's pins read their `unsat`.
-/
import RelCertifier.Trusted.Run
import RelCertifier.Trusted.InvComponents
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Checker.EvolStrengtheningX

namespace RelCertifier.Bridge

open RelCertifier RelCertifier.Parse RelCertifier.Run RelCertifier.Oracle

/-- The one-sided Lie derivative of an atom term under its own side's field at stretch 1. -/
def ownLie {n : ℕ} (side : Side) (g : ITerm n) (f : Fin n → ITerm n) : ITerm n :=
  match side with
  | Side.L => ilieDeriv g f (fun _ => ITerm.rat 0) (ITerm.rat 1)
  | _ => ilieDeriv g (fun _ => ITerm.rat 0) f (ITerm.rat 1)

/-- The route query over the domain `dom` for the atom term `g` with derivative `gdot`:
route B `dom ∧ g = 0 ∧ ġ ≥ 0`, route A `dom ∧ ġ > 0`, route C `dom ∧ g ≥ 0 ∧ ġ > 0` (every
other route is re-checked by route C). -/
def routeQuery {n : ℕ} (route : CutRouteX) (dom : IForm n) (g gdot : ITerm n) : IForm n :=
  match route with
  | .diStrict => IForm.and dom (IForm.and (IForm.cmp .eq g (.rat 0)) (IForm.cmp .ge gdot (.rat 0)))
  | .diNonstrict => IForm.and dom (IForm.cmp .gt gdot (.rat 0))
  | _ => IForm.and dom (IForm.and (IForm.cmp .ge g (.rat 0)) (IForm.cmp .gt gdot (.rat 0)))

/-- The route query of kept atom `i` of mode `m` on `side`. -/
def stayQueryOf (vars : List String) (n : ℕ) (side : Side) (m : PMode) (atoms : List CutAtomX)
    (i : ℕ) : Option (IForm n) := do
  let x ← atoms[i]?
  let f ← dynOf vars n side m
  let g ← cutAtomG vars n side x.atom
  let ev ← lowerF vars n side m.evolve
  let givens ← x.given.mapM (lowerF vars n side)
  pure (routeQuery x.route (givens.foldl IForm.and ev) g (ownLie side g f))

/-- The admissibility query of the start `(mL, mR)` at the row `row`. -/
def admQueryOf (vars : List String) (n : ℕ) (row : PForm) (mL mR : PMode) : Option (IForm n) := do
  let comps ← invComponents vars n row
  let gL ← lowerF vars n Side.L mL.guard
  let gR ← lowerF vars n Side.R mR.guard
  pure (comps.foldl (fun d g => IForm.and d (IForm.cmp .le g (.rat 0))) (IForm.and gL gR))

end RelCertifier.Bridge
