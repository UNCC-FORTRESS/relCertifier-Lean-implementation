/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The widened cut channel, lifted: `EvolStrengtheningX` is sound

`Checker/EvolStrengtheningX.lean` (tool side, `RELCERT_IMPLIED_CUT=1`) keeps, per mode,
cut atoms of five KINDS, each with its O1 (entry) justification and its O2 (invariance)
route, and the conditioning list `given` of the stratified kinds. The legacy lift
(`CutLift.lean`, `CutCover.lean`) covers only `guardConj` atoms with O1 by membership and
O2 unconditioned per atom. This file lifts the rest. The 23 new suite_v2 instances with
verdict packs (`InstancesV2/Modal/`; the three Z3-free `arm_plateau_*` instances need no
coupling) consume it through `couple_cutX` (`Proofs/Encoding/CutRespond.lean`) against
their emitted extended certificate (`InstancesV2/Cuts/<b>.lean`); 12 of the 45 suite_v2
benchmarks are certified only with the widened channel on.

**O1 — entry** (the mode's guard implies the atom), one lemma per `CutEntry`, stated over
the very lowerings the tool uses (`Run.lowerF` of the guard and of the atom):

* `membership` — `entry_membership` (the legacy `cutAtoms_sat`);
* `weakening` — `entry_weakening`: a strict guard conjunct `e < k` implies its closure
  `e ≤ k` (`strictAtoms`, `closureOf`);
* `rational` (threshold atoms: implied-contraction and derived bounds) —
  `entry_rational`: `guardImpliesRational` found a threshold conjunct on the same
  variable at least as tight; the rational comparison is re-read as a real one
  (`qLt_val`, `qLt_false_val`);
* `rational` (linear forms) — `entry_linear`: the guard box bounds `x` and `y`
  (`guardBox`, soundness by a fold invariant), the root is positive (`pairRootOK`), so
  `y + r (x − c)` is bounded by the box `sup` / `inf` (`linearEntryRational`);
* `z3` — `entry_z3`: `UNSAT(guard ∧ g > 0)` for the atom's safe-side term `g`, the exact
  `IForm` the tool's `entryZ3` sends (`entryZ3Query`), through `z3_unsat_sound`.

`atomWFX_entry` / `modeCutWFX_entry` assemble them: from the kernel-decided
`modeCutWFX m [] atoms = true` (`evolStrengtheningWFX` re-checked by `decide`), every kept
atom's lowering holds wherever the guard's lowering holds; the only hypotheses are the Z3
verdicts of the `z3`-entry atoms.

**O2 — invariance**, as superlevel Lie conditions on the atom's OWN-side field (other side
frozen, stretch 1 — the shape every O2 probe of the tool has), then transported to the
λ-stretched joint flow (`ownSuper_boxle_R` / `_L`, via `lieDeriv_one_sided_*`):

* `linearShape` — `ownSuper_linear_le` / `_ge`: for `q = y + r (x − c)` with
  `x' = y`, `y' = −a (x − c) − b y` and `r² − b r + a = 0` (the root re-checked by
  multiplication, `pairRootOK`), the Lie derivative is `−(b − r) q` (a ring identity), so
  on `{q ≥ K}`, `K ≥ 0`, it is `≤ 0`;
* `derivedShape` — `ownSuper_derived_le` / `_ge`: on `{x ≥ K'} ∩ {q ≤ K}` with
  `r (K' − c) ≥ K`, `x' = y = q − r (x − c) ≤ K − r (K' − c) ≤ 0`; the domain carries the
  GIVEN linear-form atom;
* the DI routes A / B / C — the legacy `atom_boxle_{R,L}_{nonstrict,strict,superlevel}`
  (`CutLift`, `CutCoverDischarge`), unchanged, over the bare evolve domain or the evolve
  domain narrowed by the given atom.

**Stratification** (`given`): a derived bound's O2 holds only inside its round-1
linear-form atom. `stay_given` composes the two sequentially (a differential-cut chain):
the given atom stays along every bare-domain run (its own unconditioned O2), so the run is
a run of the narrowed domain, where the derived bound's O2 applies. The threading below
therefore carries CONDITIONAL staying (`AtomsStayC`: an atom stays from every base where
ALL atoms of its family hold), which `CoverCertMCX` / `pres_multi_cutX` /
`check_sound_multi_cutX` consume exactly as the legacy `CoverCertMC` / `pres_multi_cut` /
`check_sound_multi_cut` consume unconditional staying; the legacy certificate embeds
(`CoverCertMC.toX`).

**Modal packaging.** `cut_hcertX` is `cut_hcert`'s conditional-staying form: from the
NARROWED joint verdict and the atom facts, the bare-domain `BoxLe` at every base where the
atoms hold — the per-piece shape the modal (Theorem 3) instances consume.

Axioms: the standard three, plus `z3_unsat_sound` only in the two Z3-route wrappers
(`entry_z3`, and the legacy DI-route adapters this file calls through).
-/
import RelCertifier.Proofs.Soundness.CutCoverDischarge
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.Proofs.Transfer.FaithfulBridge

namespace RelCertifier

open DL Parse Set RelCertifier.Oracle

variable {n : ℕ}

/-! ## 1. Rational comparisons, numerals, threshold atoms -/

/-- A `false` strict comparison is a real non-strict one. -/
theorem qLt_false_val {a b : QF} (ha : a.pos) (hb : b.pos) (h : qLt a b = false) :
    b.val ≤ a.val := by
  unfold qLt at h
  have hz : ¬ (a.n * b.d < b.n * a.d) := by simpa using h
  unfold QF.val
  rw [div_le_div_iff₀ hb.dR_pos ha.dR_pos]
  exact_mod_cast not_lt.mp hz

/-- The lowering of a numeral denotes its parsed rational. -/
theorem lowerE_num {vars : List String} {side : Side} {s : String} {t : ITerm n}
    (h : Run.lowerE vars n side (.num s) = some t) :
    ∃ q, parseQ s = some q ∧ q.pos ∧ ∀ ν, Term.eval t.toHost ν = q.val := by
  simp only [Run.lowerE, Run.parseRat, Option.map_map, Option.map_eq_some_iff,
    Function.comp_def] at h
  obtain ⟨q, hq, rfl⟩ := h
  refine ⟨q, hq, parseQ_pos hq, fun ν => ?_⟩
  simp only [ITerm.toHost, Term.eval, QF.val]
  push_cast
  rfl

/-- The lowering of a variable is the resolved host variable. -/
theorem lowerE_var {vars : List String} {side : Side} {v : String} {t : ITerm n}
    (h : Run.lowerE vars n side (.var v) = some t) :
    ∃ w, Run.resolveVar vars n side v = some w ∧ t = ITerm.var w := by
  simp only [Run.lowerE, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  exact ⟨w, hw, rfl⟩

/-- The comparison operator a lowered atom carries. -/
def opOfStr : String → Option CompOp
  | "<=" => some CompOp.le
  | ">=" => some CompOp.ge
  | "<" => some CompOp.lt
  | ">" => some CompOp.gt
  | "=" => some CompOp.eq
  | _ => none

/-- Decomposition of a lowered comparison. -/
theorem lowerF_cmp {vars : List String} {side : Side} {op : String} {a b : PExpr}
    {fI : IForm n} (h : Run.lowerF vars n side (.cmp op a b) = some fI) :
    ∃ ea eb c, Run.lowerE vars n side a = some ea ∧ Run.lowerE vars n side b = some eb ∧
      opOfStr op = some c ∧ fI = IForm.cmp c ea eb := by
  unfold Run.lowerF at h
  rcases hea : Run.lowerE vars n side a with _ | ea <;> rw [hea] at h
  · simp at h
  rcases heb : Run.lowerE vars n side b with _ | eb <;> rw [heb] at h
  · simp at h
  refine ⟨ea, eb, ?_⟩
  simp only [Option.bind_eq_bind, Option.bind] at h
  unfold opOfStr
  split at h <;> simp_all

/-- Semantics of a lowered threshold atom `v op s`. -/
theorem lowerF_thr {vars : List String} {side : Side} {op v s : String} {fI : IForm n}
    (h : Run.lowerF vars n side (.cmp op (.var v) (.num s)) = some fI) :
    ∃ w q c, Run.resolveVar vars n side v = some w ∧ parseQ s = some q ∧ q.pos ∧
      opOfStr op = some c ∧ ∀ ν, (Formula.sat fI.toHost ν ↔ c.interp (ν w) q.val) := by
  obtain ⟨ea, eb, c, hea, heb, hc, rfl⟩ := lowerF_cmp h
  obtain ⟨w, hw, rfl⟩ := lowerE_var hea
  obtain ⟨q, hq, hqp, hqv⟩ := lowerE_num heb
  refine ⟨w, q, c, hw, hq, hqp, hc, fun ν => ?_⟩
  simp only [IForm.toHost, Formula.sat, ITerm.toHost, Term.eval] at hqv ⊢
  rw [hqv ν]

/-! ## 2. Guard conjuncts: strict atoms, and lowering of conjuncts -/

/-- Every conjunct the cut channel reads off a guard lowers, and holds, where the
guard's lowering holds (closed conjuncts `cutAtoms`, strict ones `strictAtoms`). -/
theorem conj_sat {vars : List String} {side : Side} {f t : PForm}
    (ht : t ∈ cutAtoms f ++ strictAtoms f) :
    ∀ {fI : IForm n}, Run.lowerF vars n side f = some fI →
      ∀ ν, Formula.sat fI.toHost ν →
        ∃ tI, Run.lowerF vars n side t = some tI ∧ Formula.sat tI.toHost ν := by
  induction f with
  | and p q ihp ihq =>
      intro fI hf ν hsat
      unfold Run.lowerF at hf
      rcases hp : Run.lowerF vars n side p with _ | pI <;> rw [hp] at hf
      · simp at hf
      rcases hq : Run.lowerF vars n side q with _ | qI <;> rw [hq] at hf
      · simp at hf
      injection hf with hf'
      subst hf'
      obtain ⟨hsp, hsq⟩ := hsat
      simp only [cutAtoms, strictAtoms, List.mem_append] at ht
      rcases ht with (h | h) | (h | h)
      · exact ihp (List.mem_append_left _ h) hp ν hsp
      · exact ihq (List.mem_append_left _ h) hq ν hsq
      · exact ihp (List.mem_append_right _ h) hp ν hsp
      · exact ihq (List.mem_append_right _ h) hq ν hsq
  | cmp op x y =>
      intro fI hf ν hsat
      have hteq : t = PForm.cmp op x y := by
        simp only [cutAtoms, strictAtoms, List.mem_append] at ht
        rcases ht with h | h
        · split at h
          · exact List.mem_singleton.mp h
          · exact absurd h (by simp)
        · split at h
          · exact List.mem_singleton.mp h
          · exact absurd h (by simp)
      subst hteq
      exact ⟨fI, hf, hsat⟩
  | tt => intro fI hf ν hsat; simp [cutAtoms, strictAtoms] at ht
  | or p q _ _ => intro fI hf ν hsat; simp [cutAtoms, strictAtoms] at ht
  | not p _ => intro fI hf ν hsat; simp [cutAtoms, strictAtoms] at ht

/-- Every `strictAtoms` element is a strict comparison. -/
theorem strictAtoms_strict {f a : PForm} (ha : a ∈ strictAtoms f) :
    ∃ op x y, a = PForm.cmp op x y ∧ (op = "<" ∨ op = ">") := by
  induction f with
  | and p q ihp ihq =>
      unfold strictAtoms at ha
      rcases List.mem_append.mp ha with h | h
      · exact ihp h
      · exact ihq h
  | cmp op x y =>
      unfold strictAtoms at ha
      split at ha
      · rename_i hop
        rw [List.mem_singleton.mp ha]
        rcases Bool.or_eq_true .. |>.mp hop with h | h
        · exact ⟨op, x, y, rfl, Or.inl (by simpa using h)⟩
        · exact ⟨op, x, y, rfl, Or.inr (by simpa using h)⟩
      · exact absurd ha (by simp)
  | tt => exact absurd ha (by simp [strictAtoms])
  | or p q _ _ => exact absurd ha (by simp [strictAtoms])
  | not p _ => exact absurd ha (by simp [strictAtoms])

/-! ## 3. O1 — entry, one lemma per `CutEntry` -/

/-- `membership`: a closed guard conjunct (the legacy channel). -/
theorem entry_membership {vars : List String} {side : Side} {guard a : PForm}
    (ha : a ∈ cutAtoms guard) {gI aI : IForm n}
    (hg : Run.lowerF vars n side guard = some gI) (haI : Run.lowerF vars n side a = some aI)
    (ν : DL.State (Var n)) (hsat : Formula.sat gI.toHost ν) : Formula.sat aI.toHost ν :=
  cutAtoms_sat ha hg haI ν hsat

/-- `weakening`: a strict guard conjunct implies its closure. -/
theorem entry_weakening {vars : List String} {side : Side} {guard s a : PForm}
    (hs : s ∈ strictAtoms guard) (hcl : closureOf s = some a) {gI aI : IForm n}
    (hg : Run.lowerF vars n side guard = some gI) (haI : Run.lowerF vars n side a = some aI)
    (ν : DL.State (Var n)) (hsat : Formula.sat gI.toHost ν) : Formula.sat aI.toHost ν := by
  obtain ⟨sI, hsI, hssat⟩ := conj_sat (List.mem_append_right _ hs) hg ν hsat
  obtain ⟨op, x, y, rfl, hop⟩ := strictAtoms_strict hs
  obtain ⟨ex, ey, c, hex, hey, hc, rfl⟩ := lowerF_cmp hsI
  rcases hop with rfl | rfl
  · simp only [closureOf, Option.some.injEq] at hcl
    subst hcl
    obtain ⟨ex', ey', c', hex', hey', hc', rfl⟩ := lowerF_cmp haI
    rw [hex] at hex'; rw [hey] at hey'
    injection hex' with hx; injection hey' with hy
    subst hx; subst hy
    simp only [opOfStr, Option.some.injEq] at hc hc'
    subst hc; subst hc'
    simp only [IForm.toHost, Formula.sat, CompOp.interp] at hssat ⊢
    exact le_of_lt hssat
  · simp only [closureOf, Option.some.injEq] at hcl
    subst hcl
    obtain ⟨ex', ey', c', hex', hey', hc', rfl⟩ := lowerF_cmp haI
    rw [hex] at hex'; rw [hey] at hey'
    injection hex' with hx; injection hey' with hy
    subst hx; subst hy
    simp only [opOfStr, Option.some.injEq] at hc hc'
    subst hc; subst hc'
    simp only [IForm.toHost, Formula.sat, CompOp.interp] at hssat ⊢
    exact le_of_lt hssat

/-- `rational` (threshold atoms): `guardImpliesRational` found a threshold conjunct on
the same variable at least as tight; its rational comparison is a real one. -/
theorem entry_rational {vars : List String} {side : Side} {guard a : PForm}
    (h : guardImpliesRational guard a = true) {gI aI : IForm n}
    (hg : Run.lowerF vars n side guard = some gI) (haI : Run.lowerF vars n side a = some aI)
    (ν : DL.State (Var n)) (hsat : Formula.sat gI.toHost ν) : Formula.sat aI.toHost ν := by
  unfold guardImpliesRational at h
  split at h
  case h_2 => exact absurd h (by simp)
  rename_i op v cs
  rcases hc : parseQ cs with _ | c
  · simp [hc] at h
  rw [hc] at h
  simp only [List.any_eq_true] at h
  obtain ⟨t, ht, htrue⟩ := h
  split at htrue
  case h_2 => exact absurd htrue (by simp)
  rename_i top w ks
  obtain ⟨tI, htI, htsat⟩ := conj_sat ht hg ν hsat
  obtain ⟨w', k, ct, hw', hk, hkp, hct, htiff⟩ := lowerF_thr htI
  obtain ⟨v', c', ca, hv', hc', hcp, hca, haiff⟩ := lowerF_thr haI
  rw [hc] at hc'
  injection hc' with hcc
  subst hcc
  rw [hk] at htrue
  simp only [Bool.and_eq_true, beq_iff_eq] at htrue
  obtain ⟨hwv, hrest⟩ := htrue
  subst hwv
  rw [hw'] at hv'
  injection hv' with hvv
  subst hvv
  have htv := (htiff ν).mp htsat
  rw [haiff ν]
  by_cases hle : op = "<="
  · subst hle
    simp at hrest
    obtain ⟨htop, hlt⟩ := hrest
    have hkc := qLt_false_val hcp hkp hlt
    simp only [opOfStr, Option.some.injEq] at hca
    subst hca
    simp only [CompOp.interp]
    rcases htop with rfl | rfl
    · simp only [opOfStr, Option.some.injEq] at hct; subst hct
      simp only [CompOp.interp] at htv; linarith
    · simp only [opOfStr, Option.some.injEq] at hct; subst hct
      simp only [CompOp.interp] at htv; linarith
  · by_cases hge : op = ">="
    · subst hge
      simp at hrest
      obtain ⟨htop, hlt⟩ := hrest
      have hkc := qLt_false_val hkp hcp hlt
      simp only [opOfStr, Option.some.injEq] at hca
      subst hca
      simp only [CompOp.interp, ge_iff_le]
      rcases htop with rfl | rfl
      · simp only [opOfStr, Option.some.injEq] at hct; subst hct
        simp only [CompOp.interp, ge_iff_le] at htv; linarith
      · simp only [opOfStr, Option.some.injEq] at hct; subst hct
        simp only [CompOp.interp, gt_iff_lt] at htv; linarith
    · simp [hle, hge] at hrest

/-- `z3`: the tool's entry query `UNSAT(guard ∧ g > 0)` (`checkedCutX.entryZ3`). -/
def entryZ3Query (gI : IForm n) (g : ITerm n) : IForm n :=
  IForm.and gI (IForm.cmp .gt g (.rat 0))

/-- `z3`: the entry query's UNSAT verdict gives the implication `guard → g ≤ 0`, through
the single trust leaf `z3_unsat_sound`. -/
theorem entry_z3 {gI : IForm n} {g : ITerm n}
    (hz3 : z3solve (entryZ3Query gI g).toHost = Verdict.unsat)
    (ν : DL.State (Var n)) (hsat : Formula.sat gI.toHost ν) :
    Term.eval g.toHost ν ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  exact z3_unsat_sound hz3 ν ⟨hsat, by
    simpa [entryZ3Query, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp,
      Term.eval] using hpos⟩

/-! ### Linear forms: the guard box, the recognized pair, interval arithmetic -/

/-- A threshold conjunct of the guard bounds its variable's value (both directions). -/
theorem thr_conj_fact {vars : List String} {side : Side} {guard : PForm} {gI : IForm n}
    (hg : Run.lowerF vars n side guard = some gI) {v : String} {w : Var n}
    (hw : Run.resolveVar vars n side v = some w) (ν : DL.State (Var n))
    (hsat : Formula.sat gI.toHost ν) {op ks : String} {k : QF}
    (ht : PForm.cmp op (.var v) (.num ks) ∈ cutAtoms guard ++ strictAtoms guard)
    (hk : parseQ ks = some k) :
    k.pos ∧ ((op = "<=" ∨ op = "<") → ν w ≤ k.val) ∧
      ((op = ">=" ∨ op = ">") → k.val ≤ ν w) := by
  obtain ⟨tI, htI, htsat⟩ := conj_sat ht hg ν hsat
  obtain ⟨w', k', c, hw', hk', hkp, hc, hiff⟩ := lowerF_thr htI
  rw [hw] at hw'; injection hw' with hww; subst hww
  rw [hk] at hk'; injection hk' with hkk; subst hkk
  have hv := (hiff ν).mp htsat
  refine ⟨hkp, ?_, ?_⟩
  · rintro (rfl | rfl)
    · simp only [opOfStr, Option.some.injEq] at hc; subst hc
      simpa [CompOp.interp] using hv
    · simp only [opOfStr, Option.some.injEq] at hc; subst hc
      exact le_of_lt (by simpa [CompOp.interp] using hv)
  · rintro (rfl | rfl)
    · simp only [opOfStr, Option.some.injEq] at hc; subst hc
      simpa [CompOp.interp] using hv
    · simp only [opOfStr, Option.some.injEq] at hc; subst hc
      exact le_of_lt (by simpa [CompOp.interp] using hv)

/-- **Guard-box soundness**: the bounds `guardBox` reads off the guard's threshold
conjuncts hold wherever the guard's lowering holds. -/
theorem guardBox_sound {vars : List String} {side : Side} {guard : PForm} {gI : IForm n}
    (hg : Run.lowerF vars n side guard = some gI) {v : String} {w : Var n}
    (hw : Run.resolveVar vars n side v = some w) (ν : DL.State (Var n))
    (hsat : Formula.sat gI.toHost ν) :
    (∀ l, (guardBox guard v).1 = some l → l.pos ∧ l.val ≤ ν w) ∧
    (∀ h, (guardBox guard v).2 = some h → h.pos ∧ ν w ≤ h.val) := by
  unfold guardBox
  suffices key : ∀ (L : List PForm), (∀ t ∈ L, t ∈ cutAtoms guard ++ strictAtoms guard) →
      ∀ (acc : Option QF × Option QF),
        ((∀ l, acc.1 = some l → l.pos ∧ l.val ≤ ν w) ∧
          (∀ h, acc.2 = some h → h.pos ∧ ν w ≤ h.val)) →
        (∀ l, (L.foldl (fun acc t =>
            match t with
            | .cmp op (.var w') (.num ks) =>
                if w' != v then acc else
                match parseQ ks with
                | none => acc
                | some k =>
                    if op == "<=" || op == "<" then
                      (acc.1, match acc.2 with
                        | none => some k
                        | some h => some (if qLt k h then k else h))
                    else if op == ">=" || op == ">" then
                      (match acc.1 with
                        | none => some k
                        | some l => some (if qLt l k then k else l), acc.2)
                    else acc
            | _ => acc) acc).1 = some l → l.pos ∧ l.val ≤ ν w) ∧
        (∀ h, (L.foldl (fun acc t =>
            match t with
            | .cmp op (.var w') (.num ks) =>
                if w' != v then acc else
                match parseQ ks with
                | none => acc
                | some k =>
                    if op == "<=" || op == "<" then
                      (acc.1, match acc.2 with
                        | none => some k
                        | some h => some (if qLt k h then k else h))
                    else if op == ">=" || op == ">" then
                      (match acc.1 with
                        | none => some k
                        | some l => some (if qLt l k then k else l), acc.2)
                    else acc
            | _ => acc) acc).2 = some h → h.pos ∧ ν w ≤ h.val) by
    exact key _ (fun t ht => ht) (none, none) ⟨by simp, by simp⟩
  intro L
  induction L with
  | nil => intro _ acc hacc; simpa using hacc
  | cons t L ih =>
      intro hL acc hacc
      simp only [List.foldl_cons]
      refine ih (fun t' ht' => hL t' (List.mem_cons_of_mem _ ht')) _ ?_
      have htmem := hL t List.mem_cons_self
      obtain ⟨hlo, hhi⟩ := hacc
      split
      · rename_i op w' ks
        by_cases hwv : w' = v
        · subst hwv
          simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
          rcases hk : parseQ ks with _ | k
          · simpa using ⟨hlo, hhi⟩
          · simp only
            obtain ⟨hkp, hup, hdn⟩ := thr_conj_fact hg hw ν hsat htmem hk
            by_cases hu : (op == "<=" || op == "<") = true
            · rw [if_pos hu]
              have hu' : op = "<=" ∨ op = "<" := by simpa using hu
              refine ⟨hlo, ?_⟩
              intro h hh
              rcases hacc2 : acc.2 with _ | h0
              · rw [hacc2] at hh; injection hh with hh; subst hh
                exact ⟨hkp, hup hu'⟩
              · rw [hacc2] at hh
                obtain ⟨h0p, h0v⟩ := hhi h0 hacc2
                injection hh with hh; subst hh
                split
                · exact ⟨hkp, hup hu'⟩
                · exact ⟨h0p, h0v⟩
            · rw [if_neg hu]
              by_cases hd : (op == ">=" || op == ">") = true
              · rw [if_pos hd]
                have hd' : op = ">=" ∨ op = ">" := by simpa using hd
                refine ⟨?_, hhi⟩
                intro l hl
                rcases hacc1 : acc.1 with _ | l0
                · rw [hacc1] at hl; injection hl with hl; subst hl
                  exact ⟨hkp, hdn hd'⟩
                · rw [hacc1] at hl
                  obtain ⟨l0p, l0v⟩ := hlo l0 hacc1
                  injection hl with hl; subst hl
                  split
                  · exact ⟨hkp, hdn hd'⟩
                  · exact ⟨l0p, l0v⟩
              · rw [if_neg hd]
                exact ⟨hlo, hhi⟩
        · have : (w' != v) = true := by simpa using hwv
          simp only [this, if_true]
          exact ⟨hlo, hhi⟩
      · exact ⟨hlo, hhi⟩

/-- `affineOf` builds fractions with positive denominators. -/
theorem affineOf_pos : ∀ {e : PExpr} {cs : List (String × QF)} {k : QF},
    affineOf e = some (cs, k) → (∀ vc ∈ cs, vc.2.pos) ∧ k.pos := by
  intro e
  induction e with
  | num s =>
      intro cs k h
      simp only [affineOf, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, h⟩ := h
      injection h with h1 h2
      subst h1; subst h2
      exact ⟨by simp, parseQ_pos hq⟩
  | var v =>
      intro cs k h
      simp only [affineOf, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp [qOfInt_pos], qOfInt_pos 0⟩
  | neg a iha =>
      intro cs k h
      simp only [affineOf] at h
      rcases ha : affineOf a with _ | ⟨ca, ka⟩ <;> rw [ha] at h
      · simp at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hca, hka⟩ := iha ha
      refine ⟨?_, qNeg_pos hka⟩
      intro vc hvc
      obtain ⟨vc', hvc', rfl⟩ := List.mem_map.mp hvc
      exact qNeg_pos (hca vc' hvc')
  | bin op a b iha ihb =>
      intro cs k h
      simp only [affineOf] at h
      rcases ha : affineOf a with _ | ⟨ca, ka⟩ <;> rw [ha] at h
      · simp at h
      rcases hb : affineOf b with _ | ⟨cb, kb⟩ <;> rw [hb] at h
      · simp at h
      obtain ⟨hca, hka⟩ := iha ha
      obtain ⟨hcb, hkb⟩ := ihb hb
      simp only at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨?_, qAdd_pos hka hkb⟩
        intro vc hvc
        rcases List.mem_append.mp hvc with h | h
        · exact hca vc h
        · exact hcb vc h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨?_, qSub_pos hka hkb⟩
          intro vc hvc
          rcases List.mem_append.mp hvc with h | h
          · exact hca vc h
          · obtain ⟨vc', hvc', rfl⟩ := List.mem_map.mp h
            exact qNeg_pos (hcb vc' hvc')
        · split at h
          · split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨?_, qMul_pos hka hkb⟩
              intro vc hvc
              obtain ⟨vc', hvc', rfl⟩ := List.mem_map.mp hvc
              exact qMul_pos hka (hcb vc' hvc')
            · split at h
              · simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                refine ⟨?_, qMul_pos hka hkb⟩
                intro vc hvc
                obtain ⟨vc', hvc', rfl⟩ := List.mem_map.mp hvc
                exact qMul_pos hkb (hca vc' hvc')
              · simp at h
          · simp at h

/-- Summed coefficients keep positive denominators. -/
theorem coeffOf_pos' {cs : List (String × QF)} (hcs : ∀ vc ∈ cs, vc.2.pos) (v : String) :
    (Oracle.coeffOf cs v).pos := by
  unfold Oracle.coeffOf
  suffices key : ∀ (L : List (String × QF)), (∀ vc ∈ L, vc.2.pos) → ∀ acc : QF, acc.pos →
      (L.foldl (fun acc vc => if vc.1 == v then qAdd acc vc.2 else acc) acc).pos by
    exact key cs hcs _ (qOfInt_pos 0)
  intro L
  induction L with
  | nil => intro _ acc hacc; simpa using hacc
  | cons vc L ih =>
      intro hL acc hacc
      simp only [List.foldl_cons]
      refine ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) _ ?_
      split
      · exact qAdd_pos hacc (hL vc List.mem_cons_self)
      · exact hacc

/-- The equilibrium of a recognized pair has a positive denominator. -/
theorem secondOrderPairs_c_pos {m : PMode} {p : SOPair} (hp : p ∈ secondOrderPairs m) :
    p.c.pos := by
  unfold secondOrderPairs at hp
  obtain ⟨xe, -, hxe⟩ := List.mem_flatMap.mp hp
  split at hxe
  · rename_i y _
    split at hxe
    · simp at hxe
    · split at hxe
      · simp at hxe
      · rename_i fy _
        split at hxe
        · simp at hxe
        · rename_i cs γ hcsγ
          obtain ⟨hcs, hγ⟩ := affineOf_pos hcsγ
          dsimp only at hxe
          split at hxe
          · split at hxe
            · rename_i hneg
              rw [List.mem_singleton] at hxe
              subst hxe
              simp only [Bool.and_eq_true] at hneg
              obtain ⟨hα, -⟩ := hneg
              have hαp := coeffOf_pos' hcs xe.1
              refine qDiv_pos hγ ?_
              have hlt : (Oracle.coeffOf cs xe.1).n * 1 < 0 * (Oracle.coeffOf cs xe.1).d := by
                simpa [qLt, qOfInt] using hα
              simp only [qNeg]
              omega
            · simp at hxe
          · simp at hxe
  · simp at hxe

/-- Decomposition of `linearAtomPair`: the atom's syntax, its parsed constants, the
recognized pair it belongs to, and the root re-check. -/
theorem linearAtomPair_spec {m : PMode} {a : PForm} {op : String} {p : SOPair} {r k : QF}
    (h : linearAtomPair m a = some (op, p, r, k)) :
    ∃ rS cS kS c, a = .cmp op (.bin "+" (.var p.y) (.bin "*" (.num rS)
        (.bin "-" (.var p.x) (.num cS)))) (.num kS) ∧
      parseQ rS = some r ∧ parseQ cS = some c ∧ parseQ kS = some k ∧
      (op = "<=" ∨ op = ">=") ∧ p ∈ secondOrderPairs m ∧ qEq p.c c = true ∧
      pairRootOK p r = true := by
  unfold linearAtomPair at h
  split at h
  · simp at h
  rename_i op' y r' x c' k' hparts
  unfold linearAtomParts at hparts
  split at hparts
  · rename_i op0 y0 rS x0 cS kS
    split at hparts
    · rename_i hop
      split at hparts
      · rename_i r0 c0 k0 hr hc hk
        simp only [Option.some.injEq, Prod.mk.injEq] at hparts
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hparts
        split at h
        · rename_i p0 hfind
          split at h
          · rename_i hok
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            have hp := List.mem_of_find?_eq_some hfind
            have hpred := List.find?_some hfind
            simp only [Bool.and_eq_true, beq_iff_eq] at hpred
            obtain ⟨⟨hx, hy⟩, hcq⟩ := hpred
            refine ⟨rS, cS, kS, c0, ?_, hr, hc, hk, by simpa using hop, hp, hcq, hok⟩
            rw [hx, hy]
          · simp at h
        · simp at h
      · simp at hparts
    · simp at hparts
  · simp at hparts

/-- Semantics of a lowered linear-form atom `y + r (x − c) op K`. -/
theorem lowerF_lin {vars : List String} {side : Side} {op x y rS cS kS : String}
    {r c k : QF} (hr : parseQ rS = some r) (hc : parseQ cS = some c)
    (hk : parseQ kS = some k) {aI : IForm n}
    (h : Run.lowerF vars n side (.cmp op (.bin "+" (.var y) (.bin "*" (.num rS)
        (.bin "-" (.var x) (.num cS)))) (.num kS)) = some aI) :
    ∃ wx wy ca, Run.resolveVar vars n side x = some wx ∧
      Run.resolveVar vars n side y = some wy ∧ opOfStr op = some ca ∧
      ∀ ν, (Formula.sat aI.toHost ν ↔
        ca.interp (ν wy + r.val * (ν wx - c.val)) k.val) := by
  obtain ⟨ea, eb, ca, hea, heb, hca, rfl⟩ := lowerF_cmp h
  obtain ⟨q, hq, -, hqv⟩ := lowerE_num heb
  rw [hk] at hq; injection hq with hq; subst hq
  simp only [Run.lowerE, Option.bind_eq_bind] at hea
  rcases hy : Run.resolveVar vars n side y with _ | wy
  · simp [hy] at hea
  rcases hx : Run.resolveVar vars n side x with _ | wx
  · simp [hy, hx] at hea
  simp only [hy, hx, Run.parseRat, hr, hc, Option.map_some, Option.bind_some,
    Option.some.injEq] at hea
  subst hea
  refine ⟨wx, wy, ca, rfl, rfl, hca, fun ν => ?_⟩
  simp only [IForm.toHost, ITerm.toHost, Formula.sat, Term.eval, AOp.interp] at hqv ⊢
  rw [hqv ν]
  simp only [QF.val]
  push_cast
  rfl

/-- `rational` (linear forms): `linearEntryRational` — the guard box bounds the pair's
coordinates, the root is positive, so the linear form is bounded by the box `sup`
(resp. `inf`) and the atom's constant is on the far side of it. -/
theorem entry_linear {vars : List String} {side : Side} {m : PMode} {a : PForm}
    (h : linearEntryRational m a = true) {gI aI : IForm n}
    (hg : Run.lowerF vars n side m.guard = some gI)
    (haI : Run.lowerF vars n side a = some aI)
    (ν : DL.State (Var n)) (hsat : Formula.sat gI.toHost ν) : Formula.sat aI.toHost ν := by
  unfold linearEntryRational at h
  rcases hpair : linearAtomPair m a with _ | ⟨op, p, r, k⟩ <;> rw [hpair] at h
  · simp at h
  obtain ⟨rS, cS, kS, c, rfl, hr, hc, hk, hop, hp, hcq, hroot⟩ := linearAtomPair_spec hpair
  obtain ⟨wx, wy, ca, hwx, hwy, hca, hiff⟩ := lowerF_lin hr hc hk haI
  have hrp := parseQ_pos hr
  have hcp := parseQ_pos hc
  have hkp := parseQ_pos hk
  have hpc := secondOrderPairs_c_pos hp
  have hcv : p.c.val = c.val := qEq_val hpc hcp hcq
  have hr0 : 0 < r.val := by
    unfold pairRootOK at hroot
    simp only [Bool.and_eq_true] at hroot
    have := qLt_val (qOfInt_pos 0) hrp hroot.1.2
    simpa using this
  obtain ⟨hxlo, hxhi⟩ := guardBox_sound hg hwx ν hsat
  obtain ⟨hylo, hyhi⟩ := guardBox_sound hg hwy ν hsat
  rw [hiff ν]
  rcases hop with rfl | rfl
  · simp only [beq_self_eq_true, if_true] at h
    unfold linFormSup at h
    rcases hxh : (guardBox m.guard p.x).2 with _ | xh <;> rw [hxh] at h
    · simp at h
    rcases hyh : (guardBox m.guard p.y).2 with _ | yh <;> rw [hyh] at h
    · simp at h
    simp only [Bool.not_eq_true'] at h
    obtain ⟨xhp, hxv⟩ := hxhi xh hxh
    obtain ⟨yhp, hyv⟩ := hyhi yh hyh
    have hs := qLt_false_val hkp (qAdd_pos yhp (qMul_pos hrp (qSub_pos xhp hpc))) h
    rw [qAdd_val yhp (qMul_pos hrp (qSub_pos xhp hpc)), qMul_val,
      qSub_val xhp hpc, hcv] at hs
    simp only [opOfStr, Option.some.injEq] at hca; subst hca
    simp only [CompOp.interp]
    nlinarith [mul_le_mul_of_nonneg_left hxv (le_of_lt hr0)]
  · simp only [show ((">=" : String) == "<=") = false from rfl, Bool.false_eq_true,
      if_false] at h
    unfold linFormInf at h
    rcases hxl : (guardBox m.guard p.x).1 with _ | xl <;> rw [hxl] at h
    · simp at h
    rcases hyl : (guardBox m.guard p.y).1 with _ | yl <;> rw [hyl] at h
    · simp at h
    simp only [Bool.not_eq_true'] at h
    obtain ⟨xlp, hxv⟩ := hxlo xl hxl
    obtain ⟨ylp, hyv⟩ := hylo yl hyl
    have hs := qLt_false_val (qAdd_pos ylp (qMul_pos hrp (qSub_pos xlp hpc))) hkp h
    rw [qAdd_val ylp (qMul_pos hrp (qSub_pos xlp hpc)), qMul_val,
      qSub_val xlp hpc, hcv] at hs
    simp only [opOfStr, Option.some.injEq] at hca; subst hca
    simp only [CompOp.interp, ge_iff_le]
    nlinarith [mul_le_mul_of_nonneg_left hxv (le_of_lt hr0)]

/-! ### O1 at the certificate level -/

/-- Every atom of a well-formed mode entry is checked against its predecessors. -/
theorem modeCutWFX_mem {m : PMode} : ∀ {prev xs : List CutAtomX},
    modeCutWFX m prev xs = true → ∀ x ∈ xs, ∃ prev', atomWFX m prev' x = true := by
  intro prev xs
  induction xs generalizing prev with
  | nil => intro _ x hx; exact absurd hx List.not_mem_nil
  | cons y ys ih =>
      intro h x hx
      simp only [modeCutWFX, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨prev, h.1⟩
      · exact ih h.2 x hx

/-- The Z3 entry fact of one atom, semantically: its safe-side term is `≤ 0` wherever the
guard's lowering holds. Supplied from the tool's counted entry query by
`entryZ3Fact_of_unsat` (the only place the oracle enters O1), so the assembly below is
axiom-free for certificates without `z3` entries. -/
def EntryZ3Fact (vars : List String) (n : ℕ) (side : Side) (gI : IForm n)
    (a : PForm) : Prop :=
  ∃ g, cutAtomG vars n side a = some g ∧
    ∀ ν, Formula.sat gI.toHost ν → Term.eval g.toHost ν ≤ 0

/-- The entry query's `unsat` verdict gives the entry fact (`z3_unsat_sound`). -/
theorem entryZ3Fact_of_unsat {vars : List String} {side : Side} {gI : IForm n} {a : PForm}
    {g : ITerm n} (hg : cutAtomG vars n side a = some g)
    (hz3 : z3solve (entryZ3Query gI g).toHost = Verdict.unsat) :
    EntryZ3Fact vars n side gI a :=
  ⟨g, hg, fun ν hsat => entry_z3 hz3 ν hsat⟩

/-- A nonstrict threshold or linear atom's lowering is `g ≤ 0` for its `cutAtomG` term. -/
theorem atom_sat_of_g {vars : List String} {side : Side} {op : String} {x y : PExpr}
    (hop : op = "<=" ∨ op = ">=") {aI : IForm n}
    (haI : Run.lowerF vars n side (.cmp op x y) = some aI)
    {g : ITerm n} (hg : cutAtomG vars n side (.cmp op x y) = some g) (ν : DL.State (Var n))
    (hle : Term.eval g.toHost ν ≤ 0) : Formula.sat aI.toHost ν :=
  (cutAtomG_sat hop haI hg ν).mpr hle


/-- A derived bound accepted by `derivedShapeWF` is a nonstrict threshold atom. -/
theorem derivedShapeWF_shape {m : PMode} {g0 a : PForm} (h : derivedShapeWF m g0 a = true) :
    ∃ op e1 e2, a = .cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  cases a with
  | cmp op e1 e2 =>
      cases e1 with
      | var w =>
          cases e2 with
          | num k'S =>
              unfold derivedShapeWF at h
              dsimp only at h
              rcases hl : linearAtomPair m g0 with _ | ⟨gop, p, r, k⟩ <;> rw [hl] at h
              · simp at h
              rcases hq : parseQ k'S with _ | k' <;> rw [hq] at h
              · simp at h
              simp only [Bool.and_eq_true, beq_iff_eq] at h
              obtain ⟨-, hopeq⟩ := h
              obtain ⟨_, _, _, _, _, _, _, _, hgop, _⟩ := linearAtomPair_spec hl
              subst hopeq
              exact ⟨op, _, _, rfl, hgop⟩
          | _ => simp [derivedShapeWF] at h
      | _ => simp [derivedShapeWF] at h
  | _ => simp [derivedShapeWF] at h

/-- **O1 for one kept atom** (every `CutKind`, every `CutEntry`): if the extended
certificate's kernel check accepts the atom (`atomWFX`), the mode guard's lowering
implies the atom's lowering. The `z3`-entry atoms need their counted entry verdict. -/
theorem atomWFX_entry {vars : List String} {side : Side} {m : PMode} {prev : List CutAtomX}
    {x : CutAtomX} (h : atomWFX m prev x = true) {gI aI : IForm n}
    (hg : Run.lowerF vars n side m.guard = some gI)
    (haI : Run.lowerF vars n side x.atom = some aI)
    (hz3 : x.entry = CutEntry.z3 → EntryZ3Fact vars n side gI x.atom)
    (ν : DL.State (Var n)) (hsat : Formula.sat gI.toHost ν) : Formula.sat aI.toHost ν := by
  -- the `z3` branch, shared by the two kinds that admit it
  have hz3case : x.entry = CutEntry.z3 →
      (∃ op e1 e2, x.atom = .cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=")) →
      Formula.sat aI.toHost ν := by
    intro he ⟨op, e1, e2, hat, hop⟩
    obtain ⟨g, hgdef, hv⟩ := hz3 he
    rw [hat] at haI hgdef
    exact atom_sat_of_g hop haI hgdef ν (hv ν hsat)
  unfold atomWFX at h
  split at h
  · -- guardConj: membership
    rename_i hk
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨_, _⟩, hroute⟩ := h
    have hmem : (cutAtoms m.guard).contains x.atom = true := by
      split at hroute <;> simp_all [modeCutWF, List.all_cons, List.all_nil, Bool.and_eq_true]
    exact entry_membership (List.elem_iff.mp hmem) hg haI ν hsat
  · -- closure: weakening
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨_, _⟩, hany⟩, _⟩ := h
    obtain ⟨sa, hsa, hcl⟩ := List.any_eq_true.mp hany
    exact entry_weakening hsa (by simpa using hcl) hg haI ν hsat
  · -- impliedContract: rational or z3
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨_, hcand⟩, hent⟩, _⟩ := h
    have hshape : ∃ op e1 e2, x.atom = .cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
      have hm := List.elem_iff.mp hcand
      unfold impliedCandidates at hm
      obtain ⟨ve, -, hve⟩ := List.mem_flatMap.mp hm
      split at hve
      · rcases List.mem_cons.mp hve with h1 | h1
        · exact ⟨_, _, _, h1, Or.inl rfl⟩
        · rcases List.mem_cons.mp h1 with h2 | h2
          · exact ⟨_, _, _, h2, Or.inr rfl⟩
          · exact absurd h2 List.not_mem_nil
      · exact absurd hve List.not_mem_nil
    split at hent
    · exact entry_rational hent hg haI ν hsat
    · rename_i he; exact hz3case he hshape
    · exact absurd hent (by simp)
  · -- linearForm: rational (guard box)
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨_, _⟩, hlin⟩, _⟩ := h
    exact entry_linear hlin hg haI ν hsat
  · -- derivedBound: rational or z3
    split at h
    · rename_i g0 hgiven
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨_, hshapeWF⟩, hent⟩, _⟩ := h
      have hshape : ∃ op e1 e2, x.atom = .cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") :=
        derivedShapeWF_shape hshapeWF
      split at hent
      · exact entry_rational hent hg haI ν hsat
      · rename_i he; exact hz3case he hshape
      · exact absurd hent (by simp)
    · exact absurd h (by simp)

/-- **O1 for a whole mode entry**: from the kernel-checked `modeCutWFX m [] atoms`, every
kept atom holds wherever the mode guard's lowering holds (given the `z3`-entry verdicts). -/
theorem modeCutWFX_entry {vars : List String} {side : Side} {m : PMode}
    {atoms : List CutAtomX} (h : modeCutWFX m [] atoms = true) {gI : IForm n}
    (hg : Run.lowerF vars n side m.guard = some gI)
    (hz3 : ∀ x ∈ atoms, x.entry = CutEntry.z3 → EntryZ3Fact vars n side gI x.atom)
    (ν : DL.State (Var n)) (hsat : Formula.sat gI.toHost ν) :
    ∀ x ∈ atoms, ∀ aI, Run.lowerF vars n side x.atom = some aI →
      Formula.sat aI.toHost ν := by
  intro x hx aI haI
  obtain ⟨prev, hwf⟩ := modeCutWFX_mem h x hx
  exact atomWFX_entry hwf hg haI (hz3 x hx) ν hsat

/-! ## 4. O2 — invariance along the atom's own field -/

/-- The one-sided Lie derivative of a RIGHT atom (left frozen, stretch 1) — the shape of
every right O2 probe the tool sends. -/
def lie1R (g : Term (Var n)) (f : Fin n → Term (Var n)) : Term (Var n) :=
  lieDeriv g (fun _ => Term.const 0) f (Term.const 1)

/-- The one-sided Lie derivative of a LEFT atom (right frozen, stretch 1). -/
def lie1L (g : Term (Var n)) (f : Fin n → Term (Var n)) : Term (Var n) :=
  lieDeriv g f (fun _ => Term.const 0) (Term.const 1)

theorem eval_lie1R (g : Term (Var n)) (f : Fin n → Term (Var n)) (z : DL.State (Var n)) :
    Term.eval (lie1R g f) z
      = ∑ i : Fin n, Term.eval (tderiv g (Rv i)) z * Term.eval (f i) z := by
  unfold lie1R lieDeriv
  rw [eval_sumTerm, List.map_map, ← Fin.sum_univ_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Term.eval, AOp.interp]

theorem eval_lie1L (g : Term (Var n)) (f : Fin n → Term (Var n)) (z : DL.State (Var n)) :
    Term.eval (lie1L g f) z
      = ∑ i : Fin n, Term.eval (tderiv g (Lv i)) z * Term.eval (f i) z := by
  unfold lie1L lieDeriv
  rw [eval_sumTerm, List.map_map, ← Fin.sum_univ_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Term.eval, AOp.interp]

/-- **Superlevel O2, right atom → joint flow.** A superlevel Lie condition on the atom's
own (right) field gives its invariance along the λ-stretched joint flow, `λ ≥ 0`, over any
domain inside the one where the condition was established. -/
theorem boxle_R_of_super (g : Term (Var n)) (fL fR : Fin n → Term (Var n)) (c : ℝ)
    (hc : 0 ≤ c) (dom D : Formula (Var n)) (hfv : ∀ i : Fin n, Lv i ∉ g.fv)
    (hdomImp : ∀ x, Formula.sat dom x → Formula.sat D x)
    (hsup : ∀ z, Formula.sat D z → 0 ≤ Term.eval g z → Term.eval (lie1R g fR) z ≤ 0)
    {ν : DL.State (Var n)} (hinit : Term.eval g ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR (Term.const c)) dom) (fun ω => Term.eval g ω) ν := by
  refine DI_nonstrict_superlevel (jointSys_wellFormed fL fR (Term.const c))
    (term_differentiable g) ?_ hinit
  intro x hx hge
  rw [← lieDeriv_correct, lieDeriv_one_sided_R g fL fR c hfv]
  exact mul_nonpos_of_nonneg_of_nonpos hc (hsup x (hdomImp x hx) hge)

/-- **Superlevel O2, left atom → joint flow** (the stretch is immaterial). -/
theorem boxle_L_of_super (g : Term (Var n)) (fL fR : Fin n → Term (Var n))
    (lam : Term (Var n)) (dom D : Formula (Var n)) (hfv : ∀ i : Fin n, Rv i ∉ g.fv)
    (hdomImp : ∀ x, Formula.sat dom x → Formula.sat D x)
    (hsup : ∀ z, Formula.sat D z → 0 ≤ Term.eval g z → Term.eval (lie1L g fL) z ≤ 0)
    {ν : DL.State (Var n)} (hinit : Term.eval g ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR lam) dom) (fun ω => Term.eval g ω) ν := by
  refine DI_nonstrict_superlevel (jointSys_wellFormed fL fR lam)
    (term_differentiable g) ?_ hinit
  intro x hx hge
  rw [← lieDeriv_correct, lieDeriv_one_sided_L g fL fR lam hfv]
  exact hsup x (hdomImp x hx) hge

/-- Route C (superlevel) as a superlevel condition: the probe's UNSAT, right side. -/
theorem super_of_unsat_R {g : Term (Var n)} {fR : Fin n → Term (Var n)}
    {D : Formula (Var n)}
    (hz3 : z3solve (flowQuerySuperlevel ⟨g, fun _ => Term.const 0, fR, Term.const 1, D⟩)
      = Verdict.unsat) :
    ∀ z, Formula.sat D z → 0 ≤ Term.eval g z → Term.eval (lie1R g fR) z ≤ 0 := by
  intro z hz hge
  by_contra hpos
  rw [not_le] at hpos
  exact z3_unsat_sound hz3 z ⟨hz, by simpa [Formula.sat, CompOp.interp, Term.eval] using hge,
    by simpa [lie1R, Formula.sat, CompOp.interp, Term.eval] using hpos⟩

/-- Route C, left side. -/
theorem super_of_unsat_L {g : Term (Var n)} {fL : Fin n → Term (Var n)}
    {D : Formula (Var n)}
    (hz3 : z3solve (flowQuerySuperlevel ⟨g, fL, fun _ => Term.const 0, Term.const 1, D⟩)
      = Verdict.unsat) :
    ∀ z, Formula.sat D z → 0 ≤ Term.eval g z → Term.eval (lie1L g fL) z ≤ 0 := by
  intro z hz hge
  by_contra hpos
  rw [not_le] at hpos
  exact z3_unsat_sound hz3 z ⟨hz, by simpa [Formula.sat, CompOp.interp, Term.eval] using hge,
    by simpa [lie1L, Formula.sat, CompOp.interp, Term.eval] using hpos⟩

/-- Route A (whole domain) as a superlevel condition, right side. -/
theorem super_of_unsatA_R {g : Term (Var n)} {fR : Fin n → Term (Var n)}
    {D : Formula (Var n)}
    (hz3 : z3solve (flowQuery ⟨g, fun _ => Term.const 0, fR, Term.const 1, D⟩)
      = Verdict.unsat) :
    ∀ z, Formula.sat D z → 0 ≤ Term.eval g z → Term.eval (lie1R g fR) z ≤ 0 := by
  intro z hz _
  by_contra hpos
  rw [not_le] at hpos
  exact z3_unsat_sound hz3 z ⟨hz,
    by simpa [lie1R, flowQuery, Formula.sat, CompOp.interp, Term.eval] using hpos⟩

/-- Route A, left side. -/
theorem super_of_unsatA_L {g : Term (Var n)} {fL : Fin n → Term (Var n)}
    {D : Formula (Var n)}
    (hz3 : z3solve (flowQuery ⟨g, fL, fun _ => Term.const 0, Term.const 1, D⟩)
      = Verdict.unsat) :
    ∀ z, Formula.sat D z → 0 ≤ Term.eval g z → Term.eval (lie1L g fL) z ≤ 0 := by
  intro z hz _
  by_contra hpos
  rw [not_le] at hpos
  exact z3_unsat_sound hz3 z ⟨hz,
    by simpa [lie1L, flowQuery, Formula.sat, CompOp.interp, Term.eval] using hpos⟩

/-! ### The linear form and its derived bound, as terms -/

/-- `y + r (x − c)` — the linear form, exactly as `lowerE` builds it from
`linFormExpr`. -/
def linQ (wx wy : Var n) (r c : ℝ) : Term (Var n) :=
  Term.binop .add (Term.var wy)
    (Term.binop .mul (Term.const r) (Term.binop .sub (Term.var wx) (Term.const c)))

/-- Safe-side term of `q ≤ K` (`cutAtomG` of a `<=` linear-form atom). -/
def linLe (wx wy : Var n) (r c K : ℝ) : Term (Var n) :=
  Term.binop .sub (linQ wx wy r c) (Term.const K)

/-- Safe-side term of `q ≥ K`. -/
def linGe (wx wy : Var n) (r c K : ℝ) : Term (Var n) :=
  Term.binop .sub (Term.const K) (linQ wx wy r c)

/-- Safe-side term of `x ≤ K'`. -/
def thrLe (wx : Var n) (K : ℝ) : Term (Var n) :=
  Term.binop .sub (Term.var wx) (Term.const K)

/-- Safe-side term of `x ≥ K'`. -/
def thrGe (wx : Var n) (K : ℝ) : Term (Var n) :=
  Term.binop .sub (Term.const K) (Term.var wx)

theorem eval_linQ (wx wy : Var n) (r c : ℝ) (z : DL.State (Var n)) :
    Term.eval (linQ wx wy r c) z = z wy + r * (z wx - c) := by
  simp [linQ, Term.eval, AOp.interp]

theorem eval_tderiv_linQ (wx wy : Var n) (r c : ℝ) (w : Var n) (z : DL.State (Var n)) :
    Term.eval (tderiv (linQ wx wy r c) w) z
      = (if wy = w then 1 else 0) + r * (if wx = w then 1 else 0) := by
  by_cases hy : wy = w <;> by_cases hx : wx = w <;>
    simp [linQ, tderiv, Term.eval, AOp.interp, hy, hx]

/-- The own-field Lie derivative of the linear form, right side: `f y + r f x`. -/
theorem eval_lie1R_linQ (jx jy : Fin n) (r c : ℝ)
    (f : Fin n → Term (Var n)) (z : DL.State (Var n)) :
    Term.eval (lie1R (linQ (Rv jx) (Rv jy) r c) f) z
      = Term.eval (f jy) z + r * Term.eval (f jx) z := by
  rw [eval_lie1R]
  simp only [eval_tderiv_linQ, add_mul, Finset.sum_add_distrib]
  have h1 : ∑ i : Fin n, (if (Rv jy : Var n) = Rv i then (1:ℝ) else 0) * Term.eval (f i) z
      = Term.eval (f jy) z := by
    simp [Rv, Prod.ext_iff]
  have h2 : ∑ i : Fin n, r * (if (Rv jx : Var n) = Rv i then (1:ℝ) else 0)
      * Term.eval (f i) z = r * Term.eval (f jx) z := by
    simp [Rv, Prod.ext_iff]
  rw [h1, h2]

/-- The own-field Lie derivative of the linear form, left side. -/
theorem eval_lie1L_linQ (jx jy : Fin n) (r c : ℝ)
    (f : Fin n → Term (Var n)) (z : DL.State (Var n)) :
    Term.eval (lie1L (linQ (Lv jx) (Lv jy) r c) f) z
      = Term.eval (f jy) z + r * Term.eval (f jx) z := by
  rw [eval_lie1L]
  simp only [eval_tderiv_linQ, add_mul, Finset.sum_add_distrib]
  have h1 : ∑ i : Fin n, (if (Lv jy : Var n) = Lv i then (1:ℝ) else 0) * Term.eval (f i) z
      = Term.eval (f jy) z := by
    simp [Lv, Prod.ext_iff]
  have h2 : ∑ i : Fin n, r * (if (Lv jx : Var n) = Lv i then (1:ℝ) else 0)
      * Term.eval (f i) z = r * Term.eval (f jx) z := by
    simp [Lv, Prod.ext_iff]
  rw [h1, h2]

/-- The pair's linear-form identity: with `x' = y`, `y' = −a (x − c) − b y` and
`r² − b r + a = 0`, the derivative of `q = y + r (x − c)` is `−(b − r) q`. -/
theorem linQ_rate {a b c r fx fy x y : ℝ} (hroot : r * r - b * r + a = 0)
    (hfx : fx = y) (hfy : fy = -a * (x - c) - b * y) :
    fy + r * fx = -(b - r) * (y + r * (x - c)) := by
  subst hfx; subst hfy
  have ha : a = b * r - r * r := by linarith
  subst ha
  ring

/-- **`linearShape`, `q ≤ K`** (the superlevel condition): on `{q ≥ K}`, `K ≥ 0`, the
own-field Lie derivative `−(b − r) q` is `≤ 0`. Right side. -/
theorem super_linear_le_R {jx jy : Fin n} {a b c r K : ℝ}
    (hroot : r * r - b * r + a = 0) (hσ : 0 ≤ b - r) (hK : 0 ≤ K)
    (f : Fin n → Term (Var n)) (D : Formula (Var n))
    (hfx : ∀ z, Formula.sat D z → Term.eval (f jx) z = z (Rv jy))
    (hfy : ∀ z, Formula.sat D z →
      Term.eval (f jy) z = -a * (z (Rv jx) - c) - b * z (Rv jy)) :
    ∀ z, Formula.sat D z → 0 ≤ Term.eval (linLe (Rv jx) (Rv jy) r c K) z →
      Term.eval (lie1R (linLe (Rv jx) (Rv jy) r c K) f) z ≤ 0 := by
  intro z hz hge
  have hlie : Term.eval (lie1R (linLe (Rv jx) (Rv jy) r c K) f) z
      = Term.eval (lie1R (linQ (Rv jx) (Rv jy) r c) f) z := by
    rw [eval_lie1R, eval_lie1R]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [linLe, tderiv, Term.eval, AOp.interp]
  rw [hlie, eval_lie1R_linQ jx jy, linQ_rate hroot (hfx z hz) (hfy z hz)]
  have hq : K ≤ z (Rv jy) + r * (z (Rv jx) - c) := by
    simpa [linLe, eval_linQ, Term.eval, AOp.interp] using hge
  nlinarith

/-- **`linearShape`, `q ≥ K`**: on `{q ≤ K}`, `K ≤ 0`. Right side. -/
theorem super_linear_ge_R {jx jy : Fin n} {a b c r K : ℝ}
    (hroot : r * r - b * r + a = 0) (hσ : 0 ≤ b - r) (hK : K ≤ 0)
    (f : Fin n → Term (Var n)) (D : Formula (Var n))
    (hfx : ∀ z, Formula.sat D z → Term.eval (f jx) z = z (Rv jy))
    (hfy : ∀ z, Formula.sat D z →
      Term.eval (f jy) z = -a * (z (Rv jx) - c) - b * z (Rv jy)) :
    ∀ z, Formula.sat D z → 0 ≤ Term.eval (linGe (Rv jx) (Rv jy) r c K) z →
      Term.eval (lie1R (linGe (Rv jx) (Rv jy) r c K) f) z ≤ 0 := by
  intro z hz hge
  have hlie : Term.eval (lie1R (linGe (Rv jx) (Rv jy) r c K) f) z
      = -Term.eval (lie1R (linQ (Rv jx) (Rv jy) r c) f) z := by
    rw [eval_lie1R, eval_lie1R, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [linGe, tderiv, Term.eval, AOp.interp]
  rw [hlie, eval_lie1R_linQ jx jy, linQ_rate hroot (hfx z hz) (hfy z hz)]
  have hq : z (Rv jy) + r * (z (Rv jx) - c) ≤ K := by
    simpa [linGe, eval_linQ, Term.eval, AOp.interp] using hge
  nlinarith

/-- **`linearShape`, `q ≤ K`**, left side. -/
theorem super_linear_le_L {jx jy : Fin n} {a b c r K : ℝ}
    (hroot : r * r - b * r + a = 0) (hσ : 0 ≤ b - r) (hK : 0 ≤ K)
    (f : Fin n → Term (Var n)) (D : Formula (Var n))
    (hfx : ∀ z, Formula.sat D z → Term.eval (f jx) z = z (Lv jy))
    (hfy : ∀ z, Formula.sat D z →
      Term.eval (f jy) z = -a * (z (Lv jx) - c) - b * z (Lv jy)) :
    ∀ z, Formula.sat D z → 0 ≤ Term.eval (linLe (Lv jx) (Lv jy) r c K) z →
      Term.eval (lie1L (linLe (Lv jx) (Lv jy) r c K) f) z ≤ 0 := by
  intro z hz hge
  have hlie : Term.eval (lie1L (linLe (Lv jx) (Lv jy) r c K) f) z
      = Term.eval (lie1L (linQ (Lv jx) (Lv jy) r c) f) z := by
    rw [eval_lie1L, eval_lie1L]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [linLe, tderiv, Term.eval, AOp.interp]
  rw [hlie, eval_lie1L_linQ jx jy, linQ_rate hroot (hfx z hz) (hfy z hz)]
  have hq : K ≤ z (Lv jy) + r * (z (Lv jx) - c) := by
    simpa [linLe, eval_linQ, Term.eval, AOp.interp] using hge
  nlinarith

/-- **`linearShape`, `q ≥ K`**, left side. -/
theorem super_linear_ge_L {jx jy : Fin n} {a b c r K : ℝ}
    (hroot : r * r - b * r + a = 0) (hσ : 0 ≤ b - r) (hK : K ≤ 0)
    (f : Fin n → Term (Var n)) (D : Formula (Var n))
    (hfx : ∀ z, Formula.sat D z → Term.eval (f jx) z = z (Lv jy))
    (hfy : ∀ z, Formula.sat D z →
      Term.eval (f jy) z = -a * (z (Lv jx) - c) - b * z (Lv jy)) :
    ∀ z, Formula.sat D z → 0 ≤ Term.eval (linGe (Lv jx) (Lv jy) r c K) z →
      Term.eval (lie1L (linGe (Lv jx) (Lv jy) r c K) f) z ≤ 0 := by
  intro z hz hge
  have hlie : Term.eval (lie1L (linGe (Lv jx) (Lv jy) r c K) f) z
      = -Term.eval (lie1L (linQ (Lv jx) (Lv jy) r c) f) z := by
    rw [eval_lie1L, eval_lie1L, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [linGe, tderiv, Term.eval, AOp.interp]
  rw [hlie, eval_lie1L_linQ jx jy, linQ_rate hroot (hfx z hz) (hfy z hz)]
  have hq : z (Lv jy) + r * (z (Lv jx) - c) ≤ K := by
    simpa [linGe, eval_linQ, Term.eval, AOp.interp] using hge
  nlinarith

/-- The own-field Lie derivative of a single-coordinate threshold term. -/
theorem eval_lie1R_thr (j : Fin n) (g : Term (Var n)) (s : ℝ)
    (hg : ∀ w z, Term.eval (tderiv g w) z = if Rv j = w then s else 0)
    (f : Fin n → Term (Var n)) (z : DL.State (Var n)) :
    Term.eval (lie1R g f) z = s * Term.eval (f j) z := by
  rw [eval_lie1R]
  simp only [hg]
  simp [Rv, Prod.ext_iff]

theorem eval_lie1L_thr (j : Fin n) (g : Term (Var n)) (s : ℝ)
    (hg : ∀ w z, Term.eval (tderiv g w) z = if Lv j = w then s else 0)
    (f : Fin n → Term (Var n)) (z : DL.State (Var n)) :
    Term.eval (lie1L g f) z = s * Term.eval (f j) z := by
  rw [eval_lie1L]
  simp only [hg]
  simp [Lv, Prod.ext_iff]

theorem tderiv_thrLe (wx : Var n) (K : ℝ) (w : Var n) (z : DL.State (Var n)) :
    Term.eval (tderiv (thrLe wx K) w) z = if wx = w then 1 else 0 := by
  by_cases h : wx = w <;> simp [thrLe, tderiv, Term.eval, AOp.interp, h]

theorem tderiv_thrGe (wx : Var n) (K : ℝ) (w : Var n) (z : DL.State (Var n)) :
    Term.eval (tderiv (thrGe wx K) w) z = if wx = w then -1 else 0 := by
  by_cases h : wx = w <;> simp [thrGe, tderiv, Term.eval, AOp.interp, h]

/-- **`derivedShape`, `x ≤ K'` given `q ≤ K`**: on `{x ≥ K'}` inside the given atom,
`x' = y = q − r (x − c) ≤ K − r (K' − c) ≤ 0`. Right side; `D` carries the given atom. -/
theorem super_derived_le_R {jx jy : Fin n} {r c K K' : ℝ} (hr : 0 ≤ r)
    (hKK : K ≤ r * (K' - c)) (f : Fin n → Term (Var n)) (D : Formula (Var n))
    (hfx : ∀ z, Formula.sat D z → Term.eval (f jx) z = z (Rv jy))
    (hgiven : ∀ z, Formula.sat D z → Term.eval (linLe (Rv jx) (Rv jy) r c K) z ≤ 0) :
    ∀ z, Formula.sat D z → 0 ≤ Term.eval (thrLe (Rv jx) K') z →
      Term.eval (lie1R (thrLe (Rv jx) K') f) z ≤ 0 := by
  intro z hz hge
  rw [eval_lie1R_thr jx _ 1 (fun w z => tderiv_thrLe _ _ w z), hfx z hz]
  have hq := hgiven z hz
  simp only [linLe, eval_linQ, Term.eval, AOp.interp] at hq
  have hx : K' ≤ z (Rv jx) := by simpa [thrLe, Term.eval, AOp.interp] using hge
  nlinarith [mul_le_mul_of_nonneg_left hx hr]

/-- **`derivedShape`, `x ≥ K'` given `q ≥ K`**. Right side. -/
theorem super_derived_ge_R {jx jy : Fin n} {r c K K' : ℝ} (hr : 0 ≤ r)
    (hKK : r * (K' - c) ≤ K) (f : Fin n → Term (Var n)) (D : Formula (Var n))
    (hfx : ∀ z, Formula.sat D z → Term.eval (f jx) z = z (Rv jy))
    (hgiven : ∀ z, Formula.sat D z → Term.eval (linGe (Rv jx) (Rv jy) r c K) z ≤ 0) :
    ∀ z, Formula.sat D z → 0 ≤ Term.eval (thrGe (Rv jx) K') z →
      Term.eval (lie1R (thrGe (Rv jx) K') f) z ≤ 0 := by
  intro z hz hge
  rw [eval_lie1R_thr jx _ (-1) (fun w z => tderiv_thrGe _ _ w z), hfx z hz]
  have hq := hgiven z hz
  simp only [linGe, eval_linQ, Term.eval, AOp.interp] at hq
  have hx : z (Rv jx) ≤ K' := by simpa [thrGe, Term.eval, AOp.interp] using hge
  nlinarith [mul_le_mul_of_nonneg_left hx hr]

/-- **`derivedShape`, `x ≤ K'` given `q ≤ K`**, left side. -/
theorem super_derived_le_L {jx jy : Fin n} {r c K K' : ℝ} (hr : 0 ≤ r)
    (hKK : K ≤ r * (K' - c)) (f : Fin n → Term (Var n)) (D : Formula (Var n))
    (hfx : ∀ z, Formula.sat D z → Term.eval (f jx) z = z (Lv jy))
    (hgiven : ∀ z, Formula.sat D z → Term.eval (linLe (Lv jx) (Lv jy) r c K) z ≤ 0) :
    ∀ z, Formula.sat D z → 0 ≤ Term.eval (thrLe (Lv jx) K') z →
      Term.eval (lie1L (thrLe (Lv jx) K') f) z ≤ 0 := by
  intro z hz hge
  rw [eval_lie1L_thr jx _ 1 (fun w z => tderiv_thrLe _ _ w z), hfx z hz]
  have hq := hgiven z hz
  simp only [linLe, eval_linQ, Term.eval, AOp.interp] at hq
  have hx : K' ≤ z (Lv jx) := by simpa [thrLe, Term.eval, AOp.interp] using hge
  nlinarith [mul_le_mul_of_nonneg_left hx hr]

/-- **`derivedShape`, `x ≥ K'` given `q ≥ K`**, left side. -/
theorem super_derived_ge_L {jx jy : Fin n} {r c K K' : ℝ} (hr : 0 ≤ r)
    (hKK : r * (K' - c) ≤ K) (f : Fin n → Term (Var n)) (D : Formula (Var n))
    (hfx : ∀ z, Formula.sat D z → Term.eval (f jx) z = z (Lv jy))
    (hgiven : ∀ z, Formula.sat D z → Term.eval (linGe (Lv jx) (Lv jy) r c K) z ≤ 0) :
    ∀ z, Formula.sat D z → 0 ≤ Term.eval (thrGe (Lv jx) K') z →
      Term.eval (lie1L (thrGe (Lv jx) K') f) z ≤ 0 := by
  intro z hz hge
  rw [eval_lie1L_thr jx _ (-1) (fun w z => tderiv_thrGe _ _ w z), hfx z hz]
  have hq := hgiven z hz
  simp only [linGe, eval_linQ, Term.eval, AOp.interp] at hq
  have hx : z (Lv jx) ≤ K' := by simpa [thrGe, Term.eval, AOp.interp] using hge
  nlinarith [mul_le_mul_of_nonneg_left hx hr]

/-! ## 5. Stratification: the derived bound inside its given atom -/

/-- **Sequential composition of a stratified atom** (a differential-cut chain). The given
atom `Fq` stays along every bare-domain run (its own O2); the derived atom's O2 holds over
the domain NARROWED by `Fq`; so from a base where both hold, the derived atom stays along
every bare-domain run. -/
theorem stay_given {sys : ODESystem (Var n)} {dom Fq : Formula (Var n)}
    {gq gx : Term (Var n)} (hFq : ∀ z, Formula.sat Fq z ↔ Term.eval gq z ≤ 0)
    (hq : ∀ ν, Term.eval gq ν ≤ 0 → BoxLe (Program.ode sys dom) (fun ω => Term.eval gq ω) ν)
    (hx : ∀ ν, Term.eval gx ν ≤ 0 →
      BoxLe (Program.ode sys (Formula.and dom Fq)) (fun ω => Term.eval gx ω) ν) :
    ∀ ν, Term.eval gq ν ≤ 0 → Term.eval gx ν ≤ 0 →
      BoxLe (Program.ode sys dom) (fun ω => Term.eval gx ω) ν := by
  intro ν hqν hxν ω hsem
  refine hx ν hxν ω (sem_ode_and_of_stays sys dom Fq hsem ?_)
  intro r Φ hr hΦ0 _ hder hmask hdom t ht
  exact (hFq (Φ t)).mpr (boxLe_trace (hq ν hqν) hr hΦ0 hder hmask hdom t ht)

/-! ## 6. The threading: conditional staying, the X certificate, the throughout form -/

/-- **Conditional staying** of an atom family: each atom stays along every run from a
base where ALL atoms of the family hold — the shape a stratified family has (a derived
bound stays only from inside its given linear form). Unconditional staying
(`AtomsStay`) is the special case. -/
def AtomsStayC (atoms : List (CutAtomP n)) (sys : ODESystem (Var n))
    (dom : Formula (Var n)) : Prop :=
  ∀ a ∈ atoms, ∀ ν, CutSat atoms ν → BoxLe (Program.ode sys dom) (fun ω => Term.eval a.2 ω) ν

theorem AtomsStay.toC {atoms : List (CutAtomP n)} {sys : ODESystem (Var n)}
    {dom : Formula (Var n)} (hiff : AtomsIff atoms) (h : AtomsStay atoms sys dom) :
    AtomsStayC atoms sys dom := fun a ha ν hν =>
  h a ha ν ((hiff a ha ν).mp (hν a ha))

/-- Narrowing under conditional staying. -/
theorem sem_ode_narrowC {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    (atoms : List (CutAtomP n)) (hiff : AtomsIff atoms)
    (hstay : AtomsStayC atoms sys dom) {ν μ : State (Var n)}
    (hsem : Program.sem (Program.ode sys dom) ν μ) (hν : CutSat atoms ν) :
    Program.sem (Program.ode sys (Formula.and dom (cutF atoms))) ν μ := by
  refine sem_ode_and_of_stays sys dom (cutF atoms) hsem ?_
  intro r Φ hr hΦ0 hΦr hder hmask hdom t ht
  rw [sat_cutF]
  intro a ha
  exact (hiff a ha (Φ t)).mpr (boxLe_trace (hstay a ha ν hν) hr hΦ0 hder hmask hdom t ht)

/-- Endpoint persistence under conditional staying. -/
theorem cutSat_endpointC {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    (atoms : List (CutAtomP n)) (hiff : AtomsIff atoms)
    (hstay : AtomsStayC atoms sys dom) {ν μ : State (Var n)}
    (hsem : Program.sem (Program.ode sys dom) ν μ) (hν : CutSat atoms ν) :
    CutSat atoms μ := by
  intro a ha
  exact (hiff a ha μ).mpr (hstay a ha ν hν μ hsem)

/-- Weakening a domain preserves conditional staying of the runs it admits. -/
theorem sem_ode_dom_left {sys : ODESystem (Var n)} {A B : Formula (Var n)}
    {ν μ : State (Var n)} (h : Program.sem (Program.ode sys (Formula.and A B)) ν μ) :
    Program.sem (Program.ode sys A) ν μ := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := h
  exact ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, fun t ht => (hdom t ht).1⟩

/-- Both atom families at once (left atoms first, as the tool folds them). -/
theorem sem_ode_narrow2C {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {cutL cutRq : List (CutAtomP n)} (hiffL : AtomsIff cutL) (hiffR : AtomsIff cutRq)
    (hstayL : AtomsStayC cutL sys dom) (hstayR : AtomsStayC cutRq sys dom)
    {ν μ : State (Var n)} (hsem : Program.sem (Program.ode sys dom) ν μ)
    (hL : CutSat cutL ν) (hR : CutSat cutRq ν) :
    Program.sem (Program.ode sys
      (Formula.and dom (Formula.and (cutF cutL) (cutF cutRq)))) ν μ := by
  have h1 := sem_ode_narrowC cutL hiffL hstayL hsem hL
  have hstayR' : AtomsStayC cutRq sys (Formula.and dom (cutF cutL)) := by
    intro a ha ν' hb ω hω
    exact hstayR a ha ν' hb ω (sem_ode_dom_left hω)
  have h2 := sem_ode_narrowC cutRq hiffR hstayR' h1 hR
  refine sem_ode_congr ?_ h2
  intro x
  constructor
  · rintro ⟨⟨hd, hl⟩, hr⟩
    exact ⟨hd, hl, hr⟩
  · rintro ⟨hd, hl, hr⟩
    exact ⟨⟨hd, hl⟩, hr⟩

/-- **The X-channel cut-narrowed certificate.** `CoverCertMC` with CONDITIONAL staying
(`AtomsStayC`), so a family may contain stratified atoms (a derived bound and its given
linear form); every other field is the legacy one — in particular `entryR`, the O1 fact
that a right mode's guard implies its atoms, which `modeCutWFX_entry` discharges for every
`CutEntry` from the kernel-checked extended certificate. -/
structure CoverCertMCX (G : SearchGraph (Var n)) (gs : List (Term (Var n)))
    (Gd : ℕ → Formula (Var n)) (cutL : List (CutAtomP n))
    (cutR : ℕ → List (CutAtomP n)) : Prop where
  hiffL : AtomsIff cutL
  hiffR : ∀ q, AtomsIff (cutR q)
  stayJL : ∀ q m, G.modeAt q = some m → m.jointOK = true → AtomsStayC cutL m.sys m.dom
  stayJR : ∀ q m, G.modeAt q = some m → m.jointOK = true → AtomsStayC (cutR q) m.sys m.dom
  stayDPreL : ∀ q m, G.modeAt q = some m → m.repoDynPreOK = true →
    AtomsStayC cutL m.dynSys m.dynDomPre
  stayDPreR : ∀ q m, G.modeAt q = some m → m.repoDynPreOK = true →
    AtomsStayC (cutR q) m.dynSys m.dynDomPre
  stayDPostL : ∀ q m, G.modeAt q = some m → m.repoDynPostOK = true →
    AtomsStayC cutL m.dynSys m.dynDomPost
  stayDPostR : ∀ q m, G.modeAt q = some m → m.repoDynPostOK = true →
    AtomsStayC (cutR q) m.dynSys m.dynDomPost
  entryR : ∀ q ν, Formula.sat (Gd q) ν → CutSat (cutR q) ν
  segPresC : ∀ q m, G.modeAt q = some m → m.jointOK = true →
    SegPreservesAllOn gs m.sys
      (Formula.and m.dom (Formula.and (cutF cutL) (cutF (cutR q))))
  repoDynPresPreC : ∀ q m, G.modeAt q = some m → m.repoDynPreOK = true →
    SegPreservesAllOn gs m.dynSys
      (Formula.and m.dynDomPre (Formula.and (cutF cutL) (cutF (cutR q))))
  repoDynPresPostC : ∀ q m, G.modeAt q = some m → m.repoDynPostOK = true →
    SegPreservesAllOn gs m.dynSys
      (Formula.and m.dynDomPost (Formula.and (cutF cutL) (cutF (cutR q))))
  weightPos : ∀ m ∈ G.modes, 0 < m.weight

/-- The legacy certificate is the special case (unconditional staying). -/
theorem CoverCertMC.toX {G : SearchGraph (Var n)} {gs : List (Term (Var n))}
    {Gd : ℕ → Formula (Var n)} {cutL : List (CutAtomP n)} {cutR : ℕ → List (CutAtomP n)}
    (c : CoverCertMC G gs Gd cutL cutR) : CoverCertMCX G gs Gd cutL cutR :=
  { hiffL := c.hiffL, hiffR := c.hiffR,
    stayJL := fun q m hm hj => (c.stayJL q m hm hj).toC c.hiffL,
    stayJR := fun q m hm hj => (c.stayJR q m hm hj).toC (c.hiffR q),
    stayDPreL := fun q m hm hj => (c.stayDPreL q m hm hj).toC c.hiffL,
    stayDPreR := fun q m hm hj => (c.stayDPreR q m hm hj).toC (c.hiffR q),
    stayDPostL := fun q m hm hj => (c.stayDPostL q m hm hj).toC c.hiffL,
    stayDPostR := fun q m hm hj => (c.stayDPostR q m hm hj).toC (c.hiffR q),
    entryR := c.entryR, segPresC := c.segPresC, repoDynPresPreC := c.repoDynPresPreC,
    repoDynPresPostC := c.repoDynPresPostC, weightPos := c.weightPos }

/-- **The cut-threaded preservation, X channel.** As `pres_multi_cut`, with conditional
staying: left atoms persist by their facts through every flow from a base where the whole
left family holds; right atoms persist within a mode the same way and RE-ENTER at each
switch from the recorded target guard (O1, `entryR`). -/
theorem pres_multi_cutX (G : SearchGraph (Var n)) (gs : List (Term (Var n)))
    (Gd : ℕ → Formula (Var n)) (cutL : List (CutAtomP n))
    (cutR : ℕ → List (CutAtomP n)) (cert : CoverCertMCX G gs Gd cutL cutR) :
    ∀ cfg ν ω, RightReachG G Gd cfg ν ω →
      InvAllHolds gs ν → CutSat cutL ν → CutSat (cutR cfg.q) ν →
      InvAllHolds gs ω := by
  intro cfg ν ω hreach
  induction hreach with
  | refl => exact fun h _ _ => h
  | evolve m hm hj hsem _ ih =>
      intro hν hL hR
      have hrun := sem_ode_narrow2C cert.hiffL (cert.hiffR _)
        (cert.stayJL _ m hm hj) (cert.stayJR _ m hm hj) hsem hL hR
      exact ih (cert.segPresC _ m hm hj _ hν _ hrun)
        (cutSat_endpointC cutL cert.hiffL (cert.stayJL _ m hm hj) hsem hL)
        (cutSat_endpointC _ (cert.hiffR _) (cert.stayJR _ m hm hj) hsem hR)
  | jump m hm hj e he hsrc hlt hsem hguard hGd _ ih =>
      intro hν hL hR
      have hrun := sem_ode_narrow2C cert.hiffL (cert.hiffR _)
        (cert.stayJL _ m hm hj) (cert.stayJR _ m hm hj) hsem hL hR
      exact ih (cert.segPresC _ m hm hj _ hν _ hrun)
        (cutSat_endpointC cutL cert.hiffL (cert.stayJL _ m hm hj) hsem hL)
        (cert.entryR _ _ hGd)
  | repositionDynPre m hm hrepo e he hsrc hB hsem hGd _ ih =>
      intro hν hL hR
      have hrun := sem_ode_narrow2C cert.hiffL (cert.hiffR _)
        (cert.stayDPreL _ m hm hrepo) (cert.stayDPreR _ m hm hrepo) hsem hL hR
      exact ih (cert.repoDynPresPreC _ m hm hrepo _ hν _ hrun)
        (cutSat_endpointC cutL cert.hiffL (cert.stayDPreL _ m hm hrepo) hsem hL)
        (cert.entryR _ _ hGd)
  | repositionDynPost m hm hrepo e he hsrc hB hsem hGd _ ih =>
      intro hν hL hR
      have hrun := sem_ode_narrow2C cert.hiffL (cert.hiffR _)
        (cert.stayDPostL _ m hm hrepo) (cert.stayDPostR _ m hm hrepo) hsem hL hR
      exact ih (cert.repoDynPresPostC _ m hm hrepo _ hν _ hrun)
        (cutSat_endpointC cutL cert.hiffL (cert.stayDPostL _ m hm hrepo) hsem hL)
        (cert.entryR _ _ hGd)

/-- **The runner↔theorem connection, X channel.** The kernel-replayed `decideCovered` +
the X cut-narrowed certificate + the initial conditioning give the throughout invariant
of every component along every guard-triggered coexecution. -/
theorem check_sound_multi_cutX (G : SearchGraph (Var n)) (gs : List (Term (Var n)))
    (Gd : ℕ → Formula (Var n)) (cutL : List (CutAtomP n))
    (cutR : ℕ → List (CutAtomP n)) (cert : CoverCertMCX G gs Gd cutL cutR)
    (fuel : ℕ) (cfg : Config) (hchk : decideCovered G fuel cfg = true)
    (ν : State (Var n)) (hinit : InvAllHolds gs ν)
    (hinitL : CutSat cutL ν) (hinitR : CutSat (cutR cfg.q) ν) :
    Covered G cfg ∧ CoexecInvAllThroughoutG G Gd gs cfg ν :=
  ⟨decideCovered_sound G fuel cfg hchk,
   fun ω hreach => pres_multi_cutX G gs Gd cutL cutR cert cfg ν ω hreach
     hinit hinitL hinitR⟩

/-! ## 7. The per-piece packaging the modal (Theorem 3) instances consume -/

/-- **`cut_hcert`, X channel.** From the NARROWED segment certificate (every component
preserved over `dom ∧ (cutL ∧ cutR)` — the tool's narrowed queries, through the stratified
multi-barrier verdicts) and conditional staying of both families, every component is
preserved over the BARE domain from every base where the atoms hold. -/
theorem segPresAll_cut_liftX {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {gs : List (Term (Var n))} {cutL cutRq : List (CutAtomP n)}
    (hiffL : AtomsIff cutL) (hiffR : AtomsIff cutRq)
    (hstayL : AtomsStayC cutL sys dom) (hstayR : AtomsStayC cutRq sys dom)
    (hnarrow : SegPreservesAllOn gs sys
      (Formula.and dom (Formula.and (cutF cutL) (cutF cutRq)))) :
    ∀ ν, CutSat cutL ν → CutSat cutRq ν → (∀ g ∈ gs, Term.eval g ν ≤ 0) →
      ∀ ω, Program.sem (Program.ode sys dom) ν ω →
        (∀ g ∈ gs, Term.eval g ω ≤ 0) ∧ CutSat cutL ω ∧ CutSat cutRq ω := by
  intro ν hL hR hinv ω hsem
  exact ⟨hnarrow ν hinv ω (sem_ode_narrow2C hiffL hiffR hstayL hstayR hsem hL hR),
    cutSat_endpointC cutL hiffL hstayL hsem hL,
    cutSat_endpointC cutRq hiffR hstayR hsem hR⟩

/-! ## 8. The extended certificate, looked up per mode -/

/-- A side entry of a well-formed extended certificate names a mode of that side whose
atom list passes `modeCutWFX`. -/
theorem sideCutWFX_mem {modes : List PMode} {mcs : List (String × List CutAtomX)}
    (h : sideCutWFX modes mcs = true) {name : String} {atoms : List CutAtomX}
    (hmem : (name, atoms) ∈ mcs) :
    ∃ m, modes.find? (·.name == name) = some m ∧ modeCutWFX m [] atoms = true := by
  unfold sideCutWFX at h
  have h1 := List.all_eq_true.mp h _ hmem
  simp only at h1
  split at h1
  · rename_i m hm; exact ⟨m, hm, h1⟩
  · exact absurd h1 (by simp)

/-- **O1 for a whole extended certificate** (right side): from the kernel-checked
`evolStrengtheningWFX p c = true`, for every right-mode entry of `c`, the lowered guard of
that mode implies every kept atom (given the `z3`-entry facts, none in `suite_v2`). -/
theorem evolStrengtheningWFX_entryR {p : PProblem} {c : EvolStrengtheningX}
    (h : evolStrengtheningWFX p c = true) {name : String} {atoms : List CutAtomX}
    (hmem : (name, atoms) ∈ c.R) :
    ∃ m, p.R.modes.find? (·.name == name) = some m ∧
      ∀ (vars : List String) (side : Side) (gI : IForm n),
        Run.lowerF vars n side m.guard = some gI →
        (∀ x ∈ atoms, x.entry = CutEntry.z3 → EntryZ3Fact vars n side gI x.atom) →
        ∀ ν, Formula.sat gI.toHost ν →
          ∀ x ∈ atoms, ∀ aI, Run.lowerF vars n side x.atom = some aI →
            Formula.sat aI.toHost ν := by
  unfold evolStrengtheningWFX at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨m, hm, hwf⟩ := sideCutWFX_mem h.2 hmem
  exact ⟨m, hm, fun vars side gI hg hz3 ν hsat => modeCutWFX_entry hwf hg hz3 ν hsat⟩

/-- **O1 for a whole extended certificate** (left side). -/
theorem evolStrengtheningWFX_entryL {p : PProblem} {c : EvolStrengtheningX}
    (h : evolStrengtheningWFX p c = true) {name : String} {atoms : List CutAtomX}
    (hmem : (name, atoms) ∈ c.L) :
    ∃ m, p.L.modes.find? (·.name == name) = some m ∧
      ∀ (vars : List String) (side : Side) (gI : IForm n),
        Run.lowerF vars n side m.guard = some gI →
        (∀ x ∈ atoms, x.entry = CutEntry.z3 → EntryZ3Fact vars n side gI x.atom) →
        ∀ ν, Formula.sat gI.toHost ν →
          ∀ x ∈ atoms, ∀ aI, Run.lowerF vars n side x.atom = some aI →
            Formula.sat aI.toHost ν := by
  unfold evolStrengtheningWFX at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨m, hm, hwf⟩ := sideCutWFX_mem h.1 hmem
  exact ⟨m, hm, fun vars side gI hg hz3 ν hsat => modeCutWFX_entry hwf hg hz3 ν hsat⟩

/-! ## 9. Axiom audit of the layer (re-emitted on every build of this file) -/

#print axioms entry_rational
#print axioms entry_linear
#print axioms evolStrengtheningWFX_entryR
#print axioms super_linear_le_R
#print axioms super_derived_le_R
#print axioms stay_given
#print axioms check_sound_multi_cutX
#print axioms segPresAll_cut_liftX
#print axioms entry_z3
#print axioms entryZ3Fact_of_unsat
#print axioms evolStrengtheningWFX_entryL

end RelCertifier
