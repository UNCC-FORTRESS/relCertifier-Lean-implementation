/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The Faithful bridge, padded models (`vs.length < n`)

**Status.** Part of the settling / `Faithful` route (per-benchmark settling, terrain and
affine models of the legacy suite, kernel-certified against the parsed IR). Its
per-benchmark batteries (`SettlingInstances`, `TerrainInstances`, `AffineInstances`,
`FaithfulCerts`, `RealInstances`) were retired with the legacy suite (git history); the
suite_v2 theorems use the modal chain instead. The generic definitions and lemmas stay
compiled as part of the soundness development.

Eight settling benchmarks carry a padded model: `SettlingModel 2` over one parsed state
variable. The padded coordinates are frozen with unconstrained envelope bands (enforced
by `modeCore`'s padding clause, part of the kernel fidelity certificate), the guarded
coordinate is parsed-width, and no real coordinate's shape references a padded one
(`shapeRefsInB`, decidable per benchmark).

The scale for a padded coordinate must be INVERTIBLE for the rescale witness, but the
transcription supplies no scale for it (the scales list has parsed width). `sigmaPad`
extends the scale function by `1` on padded coordinates; everything the formulas and
fields read lives on parsed-width coordinates, where `sigmaPad` agrees with `sigmaOf`,
so the full-width bridge lemmas transport by evaluation agreement.
-/
import RelCertifier.Proofs.Transfer.RealEndToEnd

namespace RelCertifier

open DL DLCalTiming DLRel Function Set

variable {n : ℕ}

/-! ## Evaluation agreement -/

theorem Term.eval_agree {V : Type*} {t : Term V} {ν ν' : DL.State V}
    (h : ∀ x ∈ t.fv, ν x = ν' x) : Term.eval t ν = Term.eval t ν' := by
  induction t with
  | var x => exact h x (by simp [Term.fv])
  | const c => rfl
  | binop op a b iha ihb =>
      show op.interp _ _ = op.interp _ _
      rw [iha (fun x hx => h x (by simp [Term.fv]; exact Or.inl hx)),
        ihb (fun x hx => h x (by simp [Term.fv]; exact Or.inr hx))]

/-! ## The padded scale -/

/-- The scale function extended by `1` on padded coordinates. -/
noncomputable def sigmaPad (σq : List QF) (w : ℕ) : Fin n → ℝ :=
  fun j => if j.val < w then sigmaOf σq j else 1

theorem sigmaPad_real {σq : List QF} {w : ℕ} {j : Fin n} (hj : j.val < w) :
    sigmaPad σq w j = sigmaOf σq j := if_pos hj

theorem sigmaPad_pad {σq : List QF} {w : ℕ} {j : Fin n} (hj : w ≤ j.val) :
    sigmaPad σq w j = 1 := if_neg (by omega)

theorem sigmaPad_pos {σq : List QF} {w : ℕ}
    (hσv : ∀ j : Fin n, j.val < w → 0 < sigmaOf σq j) (j : Fin n) :
    0 < sigmaPad σq w j := by
  unfold sigmaPad
  split
  · exact hσv j (by omega)
  · exact one_pos

/-- The padded and full scalings agree on every parsed-width right coordinate and on
every non-right coordinate. -/
theorem scaleState_pad_agree {σq : List QF} {w : ℕ} (ν : DL.State (Var n))
    {x : Var n} (hx : ∀ j : Fin n, x = Rv j → j.val < w) :
    scaleState (sigmaPad σq w) ν x = scaleState (sigmaOf σq) ν x := by
  obtain ⟨sd, i⟩ := x
  cases sd with
  | R =>
      show sigmaPad σq w i * ν (Side.R, i) = sigmaOf σq i * ν (Side.R, i)
      rw [sigmaPad_real (hx i rfl)]
  | L => rfl
  | Aux => rfl

/-! ## Shape reference discipline (decidable) -/

/-- Every model coordinate a shape references (its own plus any driver/damper). -/
def shapeRefsInB (w : ℕ) (i : Fin n) : CoordShape n → Bool
  | .frozen => true
  | .constRate _ => true
  | .contract _ _ => decide (i.val < w)
  | .contractQ _ _ _ => decide (i.val < w)
  | .driven j => decide (j.val < w)
  | .chase j _ => decide (i.val < w) && decide (j.val < w)
  | .riccati _ _ => decide (i.val < w)
  | .pairSym j _ _ => decide (i.val < w) && decide (j.val < w)
  | .drivenDamp j ds => decide (j.val < w) && ds.all (fun d => decide (d.1.val < w))

/-- A reference-disciplined shape's field reads only parsed-width right coordinates. -/
theorem field_fv_lt {w : ℕ} {i : Fin n} {sh : CoordShape n}
    (h : shapeRefsInB w i sh = true) :
    ∀ x ∈ (CoordShape.field i sh).fv, ∀ j : Fin n, x = Rv j → j.val < w := by
  cases sh with
  | frozen => intro x hx; exact absurd hx (by simp [CoordShape.field, Term.fv])
  | constRate c => intro x hx; exact absurd hx (by simp [CoordShape.field, Term.fv])
  | contract k c =>
      intro x hx j hj
      simp only [CoordShape.field, Term.fv, Set.union_empty, Set.empty_union,
        Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false,
        false_or] at hx
      subst hx
      have : i = j := by simpa [Rv, Prod.ext_iff] using hj
      subst this
      exact of_decide_eq_true h
  | contractQ kn kd c =>
      intro x hx j hj
      simp only [CoordShape.field, Term.fv, Set.union_empty, Set.empty_union,
        Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false,
        false_or] at hx
      subst hx
      have : i = j := by simpa [Rv, Prod.ext_iff] using hj
      subst this
      exact of_decide_eq_true h
  | driven jd =>
      intro x hx j hj
      simp only [CoordShape.field, Term.fv, Set.mem_singleton_iff] at hx
      subst hx
      have : jd = j := by simpa [Rv, Prod.ext_iff] using hj
      subst this
      exact of_decide_eq_true h
  | chase jd k =>
      intro x hx j hj
      simp only [shapeRefsInB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [CoordShape.field, Term.fv, Set.union_empty, Set.empty_union,
        Set.mem_union, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · have : jd = j := by simpa [Rv, Prod.ext_iff] using hj
        subst this
        exact h.2
      · have : i = j := by simpa [Rv, Prod.ext_iff] using hj
        subst this
        exact h.1
  | riccati b a =>
      intro x hx j hj
      simp only [CoordShape.field, Term.fv, Set.union_empty, Set.empty_union,
        Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false,
        false_or, or_self] at hx
      subst hx
      have : i = j := by simpa [Rv, Prod.ext_iff] using hj
      subst this
      exact of_decide_eq_true h
  | pairSym jd c hh =>
      intro x hx j hj
      simp only [shapeRefsInB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [CoordShape.field, Term.fv, Set.union_empty, Set.empty_union,
        Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false,
        false_or] at hx
      rcases hx with rfl | rfl
      · have : i = j := by simpa [Rv, Prod.ext_iff] using hj
        subst this
        exact h.1
      · have : jd = j := by simpa [Rv, Prod.ext_iff] using hj
        subst this
        exact h.2
  | drivenDamp jd ds =>
      intro x hx j hj
      simp only [shapeRefsInB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
      simp only [CoordShape.field, Term.fv, Set.mem_union, Set.mem_singleton_iff] at hx
      rcases hx with rfl | hx
      · have : jd = j := by simpa [Rv, Prod.ext_iff] using hj
        subst this
        exact h.1
      · -- damper fold: x sits in some damper's fv
        have hds : ∀ (l : List (Fin n × ℤ × ℤ)) (acc : Term (Var n)),
            (∀ y ∈ acc.fv, ∀ j' : Fin n, y = Rv j' → j'.val < w) →
            (∀ d ∈ l, d.1.val < w) →
            ∀ y ∈ (l.foldr (fun d acc =>
              Term.binop AOp.sub acc
                (Term.binop AOp.mul (Term.const ((d.2.1 : ℝ) / (d.2.2 : ℝ)))
                  (Term.binop AOp.mul (Term.var (Rv d.1)) (Term.var (Rv d.1)))))
              acc).fv, ∀ j' : Fin n, y = Rv j' → j'.val < w := by
          intro l
          induction l with
          | nil => intro acc hacc _; exact hacc
          | cons d l ih =>
              intro acc hacc hall y hy j' hj'
              simp only [List.foldr_cons, Term.fv, Set.mem_union,
                Set.mem_singleton_iff, Set.mem_empty_iff_false, Set.empty_union,
                false_or, or_self] at hy
              rcases hy with hy | rfl
              · exact ih acc hacc
                  (fun d' hd' => hall d' (List.mem_cons_of_mem _ hd')) y hy j' hj'
              · have : d.1 = j' := by simpa [Rv, Prod.ext_iff] using hj'
                subst this
                exact hall d (List.mem_cons_self ..)
        exact hds ds (Term.const 1)
          (fun y hy => absurd hy (by simp [Term.fv]))
          h.2
          x hx j hj

/-! ## Padding facts from `modeCore` -/

/-- The padding clause: coordinates at or beyond the parsed width are frozen with
unconstrained envelope bands. -/
theorem modeCore_pad_facts {vs : List String} {σq : List QF} {uq : QF}
    {names : List String} {self : Nat} {pm : Parse.PMode} {m : SettlingMode n}
    {env : Fin n → Band}
    (hmc : modeCore vs σq uq names self pm m env = true)
    (i : Fin n) (hi : vs.length ≤ i.val) :
    m.shapes i = CoordShape.frozen ∧ (env i).lo = none ∧ (env i).hi = none := by
  unfold modeCore at hmc
  simp only [Bool.and_eq_true] at hmc
  have hpad := hmc.1.1.2
  have hfact := List.all_eq_true.mp hpad i.val (List.mem_range.mpr i.isLt)
  rw [dif_pos i.isLt, if_pos hi] at hfact
  simp only [Bool.and_eq_true] at hfact
  obtain ⟨⟨hsh, hlo⟩, hhi⟩ := hfact
  refine ⟨?_, ?_, ?_⟩
  · revert hsh
    cases hshape : m.shapes ⟨i.val, i.isLt⟩ <;> intro hsh
    case frozen => simpa [Fin.eta] using hshape
    all_goals exact absurd hsh (by simp)
  · simpa [Option.isNone_iff_eq_none, Fin.eta] using hlo
  · simpa [Option.isNone_iff_eq_none, Fin.eta] using hhi

/-- In-range ode facts (the padded-model form of `modeCore_ode_facts`). -/
theorem modeCore_ode_facts' {vs : List String} {σq : List QF} {uq : QF}
    {names : List String} {self : Nat} {pm : Parse.PMode} {m : SettlingMode n}
    {env : Fin n → Band}
    (hmc : modeCore vs σq uq names self pm m env = true)
    (i : Fin n) (hi : i.val < vs.length) :
    ∃ o p, pm.odes.find? (fun o => o.1 == vs.getD i.val "") = some o
      ∧ exprPoly o.2 = some p
      ∧ shapeFaithful vs σq uq i.val (m.shapes i) p = true := by
  unfold modeCore at hmc
  simp only [Bool.and_eq_true] at hmc
  have hall := hmc.1.1.1
  have hfact := List.all_eq_true.mp hall i.val (List.mem_range.mpr hi)
  rw [dif_pos i.isLt] at hfact
  rcases hfind : pm.odes.find? (fun o => o.1 == vs.getD i.val "") with _ | o <;>
    rw [hfind] at hfact
  · exact absurd hfact (by simp)
  have hfact' : (match exprPoly o.2 with
      | some p => shapeFaithful vs σq uq i.val (m.shapes ⟨i.val, i.isLt⟩) p
      | none => false) = true := hfact
  rcases hep : exprPoly o.2 with _ | pq <;> rw [hep] at hfact'
  · exact absurd hfact' (by simp)
  exact ⟨o, pq, hfind, hep, by simpa using hfact'⟩

/-- Envelope facts from `modeCore`, parsed-width form. -/
theorem modeCore_env_facts_le {vs : List String} {σq : List QF} {uq : QF}
    {names : List String} {self : Nat} {pm : Parse.PMode} {m : SettlingMode n}
    {env : Fin n → Band} (hlenLE : vs.length ≤ n)
    (hmc : modeCore vs σq uq names self pm m env = true) :
    ∃ eb, boundsOfForm pm.evolve = some eb
      ∧ ∀ i : Fin n, i.val < vs.length →
          envFaithful (σq.getD i.val (qOfInt 0)) (env i)
            (boundOf eb (vs.getD i.val "")).1 (boundOf eb (vs.getD i.val "")).2
            = true := by
  unfold modeCore at hmc
  simp only [Bool.and_eq_true] at hmc
  have henv := hmc.1.2
  rcases heb : boundsOfForm pm.evolve with _ | eb <;> rw [heb] at henv
  · exact absurd henv (by simp)
  refine ⟨eb, rfl, ?_⟩
  intro i hi
  have hfact := List.all_eq_true.mp henv i.val (List.mem_range.mpr hi)
  rw [dif_pos i.isLt] at hfact
  simpa using hfact

/-! ## `boundsOfForm` name discipline -/

/-- Variable names occurring on the var side of a `PForm`'s comparison atoms. -/
def cmpVarNames : Parse.PForm → List String
  | .and a b => cmpVarNames a ++ cmpVarNames b
  | .cmp _ (.var v) (.num _) => [v]
  | .cmp _ (.num _) (.var v) => [v]
  | _ => []

/-- Every `boundsOfForm` entry is named by a comparison-atom variable. -/
theorem boundsOfForm_names : ∀ {f : Parse.PForm} {bs},
    boundsOfForm f = some bs → ∀ e ∈ bs, e.1 ∈ cmpVarNames f := by
  intro f
  induction f with
  | tt =>
      intro bs h e he
      injection h with h'
      subst h'
      exact absurd he (by simp)
  | cmp op a b =>
      intro bs h e he
      unfold boundsOfForm at h
      split at h
      · rcases hq : parseQ _ with _ | q <;> rw [hq] at h
        · simp at h
        simp only [Option.bind_eq_bind, Option.bind] at h
        split at h <;>
          first
            | (injection h with h'
               subst h'
               rw [List.mem_singleton.mp he]
               simp [cmpVarNames])
            | simp at h
      · rcases hq : parseQ _ with _ | q <;> rw [hq] at h
        · simp at h
        simp only [Option.bind_eq_bind, Option.bind] at h
        split at h <;>
          first
            | (injection h with h'
               subst h'
               rw [List.mem_singleton.mp he]
               simp [cmpVarNames])
            | simp at h
      · simp at h
  | and a b iha ihb =>
      intro bs h e he
      unfold boundsOfForm at h
      rcases hba : boundsOfForm a with _ | ba <;> rw [hba] at h
      · simp at h
      rcases hbb : boundsOfForm b with _ | bb <;> rw [hbb] at h
      · simp at h
      injection h with h'
      subst h'
      have hstep : ∀ (acc : List (String × Option QF × Option QF))
          (x : String × Option QF × Option QF),
          (∀ e' ∈ acc, e'.1 ∈ cmpVarNames (Parse.PForm.and a b)) →
          x.1 ∈ cmpVarNames (Parse.PForm.and a b) →
          ∀ e' ∈ mergeBound acc x, e'.1 ∈ cmpVarNames (Parse.PForm.and a b) := by
        intro acc x hacc hx e' he'
        unfold mergeBound at he'
        rcases hfind : acc.find? (fun e2 => e2.1 == x.1) with _ | e0 <;>
          rw [hfind] at he'
        · rcases List.mem_append.mp he' with h' | h'
          · exact hacc e' h'
          · rw [List.mem_singleton.mp h']
            exact hx
        · simp only [List.mem_map] at he'
          obtain ⟨g, hg, rfl⟩ := he'
          by_cases hgv : (g.1 == x.1) = true
          · rw [if_pos hgv]
            exact hx
          · rw [if_neg hgv]
            exact hacc g hg
      have hfold : ∀ (l : List (String × Option QF × Option QF))
          (acc : List (String × Option QF × Option QF)),
          (∀ e' ∈ acc, e'.1 ∈ cmpVarNames (Parse.PForm.and a b)) →
          (∀ e' ∈ l, e'.1 ∈ cmpVarNames (Parse.PForm.and a b)) →
          ∀ e' ∈ l.foldl mergeBound acc, e'.1 ∈ cmpVarNames (Parse.PForm.and a b) := by
        intro l
        induction l with
        | nil => intro acc hacc _ e' he'; exact hacc e' he'
        | cons x l ih =>
            intro acc hacc hl e' he'
            simp only [List.foldl_cons] at he'
            exact ih (mergeBound acc x)
              (hstep acc x hacc (hl x (List.mem_cons_self ..)))
              (fun y hy => hl y (List.mem_cons_of_mem _ hy)) e' he'
      refine hfold bb ba ?_ ?_ e he
      · intro e' he'
        simp only [cmpVarNames, List.mem_append]
        exact Or.inl (iha hba e' he')
      · intro e' he'
        simp only [cmpVarNames, List.mem_append]
        exact Or.inr (ihb hbb e' he')
  | or a b iha ihb =>
      intro bs h e he
      exact absurd h (by simp [boundsOfForm])
  | not a iha =>
      intro bs h e he
      exact absurd h (by simp [boundsOfForm])

/-- If the empty name is not among the form's atom variables, its `boundOf` is empty. -/
theorem boundOf_notmem {bs : List (String × Option QF × Option QF)} {v : String}
    (h : ∀ e ∈ bs, e.1 ≠ v) : boundOf bs v = (none, none) := by
  unfold boundOf
  rcases hf : bs.find? (fun e => e.1 == v) with _ | e <;> rw [hf]
  · rfl
  · exfalso
    have hmem := List.mem_of_find?_eq_some hf
    have := List.find?_some hf
    exact h e hmem (by simpa using this)

/-! ## Field pushforward, padded -/

/-- `getD` beyond the list is the default. -/
theorem getD_oob {l : List String} {i : ℕ} (h : l.length ≤ i) : l.getD i "" = "" := by
  unfold List.getD
  rw [List.getElem?_eq_none (by omega)]
  rfl

/-- Padded-model shape discipline: only self-referencing shapes, at parsed width. (The
eight padded benchmarks use frozen/constRate/contractQ; contract included for free.) -/
def padShapeOkB (w : ℕ) (i : Fin n) : CoordShape n → Bool
  | .frozen => true
  | .constRate _ => decide (i.val < w)
  | .contract _ _ => decide (i.val < w)
  | .contractQ _ _ _ => decide (i.val < w)
  | _ => false

theorem fieldOf_bridge_pad {vs : List String} {σq : List QF} {uq : QF}
    {names : List String} {self : Nat}
    (hnod : vs.Nodup) (hlenLE : vs.length ≤ n)
    (hσd : ∀ j, j < n → (σq.getD j (qOfInt 0)).pos)
    (hud : uq.pos) (pm : Parse.PMode) (m : SettlingMode n) {env : Fin n → Band}
    (hmc : modeCore vs σq uq names self pm m env = true)
    (hshapes : ∀ i : Fin n, i.val < vs.length →
      padShapeOkB vs.length i (m.shapes i) = true)
    (hnoempty : pm.odes.find? (fun o => o.1 == "") = none) :
    ∀ (i : Fin n) (ν : DL.State (Var n)),
      Term.eval (m.fieldOf i) (scaleState (sigmaPad σq vs.length) ν)
        = sigmaPad σq vs.length i * (uq.val * Term.eval (realFieldOf vs pm n i) ν) := by
  intro i ν
  by_cases hi : i.val < vs.length
  case neg =>
    obtain ⟨hfr, -, -⟩ := modeCore_pad_facts hmc i (by omega)
    have hzero : m.fieldOf i = Term.const 0 := by
      unfold SettlingMode.fieldOf
      rw [hfr]
      rfl
    have hreal : realFieldOf vs pm n i = Term.const 0 := by
      unfold realFieldOf
      rw [getD_oob (by omega), hnoempty]
    rw [hzero, hreal]
    show (0 : ℝ) = sigmaPad σq vs.length i * (uq.val * 0)
    ring
  case pos =>
    obtain ⟨o, p, hfind, hep, hsf⟩ := modeCore_ode_facts' hmc i hi
    have hreal : realFieldOf vs pm n i = polyToTerm vs n p := by
      unfold realFieldOf
      simp only [hfind, hep]
    rw [hreal]
    have hp := exprPoly_inv hep
    have hsh := hshapes i hi
    -- the padded/full scalings agree on everything a self-referencing shape reads
    have hagree : Term.eval (m.fieldOf i) (scaleState (sigmaPad σq vs.length) ν)
        = Term.eval (m.fieldOf i) (scaleState (sigmaOf σq) ν) := by
      refine Term.eval_agree ?_
      intro x hx
      refine scaleState_pad_agree ν ?_
      have hrefs : shapeRefsInB vs.length i (m.shapes i) = true := by
        revert hsh
        cases m.shapes i <;> intro hsh <;>
          first
            | rfl
            | exact hsh
            | exact absurd hsh (by simp [padShapeOkB])
      exact field_fv_lt hrefs x (by
        unfold SettlingMode.fieldOf at hx
        exact hx)
    rw [hagree, sigmaPad_real hi]
    show Term.eval ((m.shapes i).field i) (scaleState (sigmaOf σq) ν) = _
    cases hshc : m.shapes i with
    | frozen =>
        rw [hshc] at hsf
        exact bridge_frozen i hsf ν
    | constRate c =>
        rw [hshc] at hsf
        exact bridge_constRate hσd hud i hp hsf ν
    | contract k c =>
        rw [hshc] at hsf
        exact bridge_contract hnod i hi hσd hud hp hsf ν
    | contractQ kn kd c =>
        rw [hshc] at hsf
        exact bridge_contractQ hnod i hi hσd hud hp hsf ν
    | driven j => rw [hshc] at hsh; exact absurd hsh (by simp [padShapeOkB])
    | drivenDamp j ds => rw [hshc] at hsh; exact absurd hsh (by simp [padShapeOkB])
    | riccati b a => rw [hshc] at hsh; exact absurd hsh (by simp [padShapeOkB])
    | pairSym j c h => rw [hshc] at hsh; exact absurd hsh (by simp [padShapeOkB])
    | chase j k => rw [hshc] at hsh; exact absurd hsh (by simp [padShapeOkB])

/-! ## Envelope and guard, padded -/

/-- A band formula at coordinate `i` reads only `Rv i`, so satisfaction transports along
the padded/full agreement at parsed-width coordinates. -/
theorem sat_band_pad_agree {σq : List QF} {w : ℕ} (i : Fin n) (hi : i.val < w)
    (b : Band) (ν : DL.State (Var n)) :
    Formula.sat (Band.formula i b) (scaleState (sigmaPad σq w) ν)
      ↔ Formula.sat (Band.formula i b) (scaleState (sigmaOf σq) ν) := by
  have hRv : scaleState (sigmaPad σq w) ν (Rv i) = scaleState (sigmaOf σq) ν (Rv i) :=
    scaleState_pad_agree ν (by
      intro j hj
      have : i = j := by simpa [Rv, Prod.ext_iff] using hj
      omega)
  unfold Band.formula
  rcases b.lo with _ | z <;> rcases b.hi with _ | z' <;>
    simp only [Formula.sat, CompOp.interp, Term.eval, hRv]

theorem sat_bandDom_pad_agree {σq : List QF} {w : ℕ} (i : Fin n) (hi : i.val < w)
    (lo hi' : ℝ) (ν : DL.State (Var n)) :
    Formula.sat (bandDom i lo hi') (scaleState (sigmaPad σq w) ν)
      ↔ Formula.sat (bandDom i lo hi') (scaleState (sigmaOf σq) ν) := by
  have hRv : scaleState (sigmaPad σq w) ν (Rv i) = scaleState (sigmaOf σq) ν (Rv i) :=
    scaleState_pad_agree ν (by
      intro j hj
      have : i = j := by simpa [Rv, Prod.ext_iff] using hj
      omega)
  simp only [bandDom, Formula.sat, CompOp.interp, Term.eval, hRv]

/-- **The padded `hdom` discharger.** -/
theorem envFormulaR_sat_pad (M : SettlingModel n) {vs : List String} {σq : List QF}
    {eb : List (String × Option QF × Option QF)}
    (hbs : BoundsPos eb) (hlenLE : vs.length ≤ n)
    (hσd : ∀ j, j < n → (σq.getD j (qOfInt 0)).pos)
    (hσv : ∀ j : Fin n, j.val < vs.length → 0 < sigmaOf σq j)
    (hef : ∀ i : Fin n, i.val < vs.length →
      envFaithful (σq.getD i.val (qOfInt 0)) (M.env i)
        (boundOf eb (vs.getD i.val "")).1 (boundOf eb (vs.getD i.val "")).2 = true)
    (hpadenv : ∀ i : Fin n, vs.length ≤ i.val →
      (M.env i).lo = none ∧ (M.env i).hi = none)
    (hnames : ∀ e ∈ eb, e.1 ≠ "")
    (ν : DL.State (Var n)) :
    Formula.sat (envFormulaR vs n eb) ν
      ↔ Formula.sat M.envF (scaleState (sigmaPad σq vs.length) ν) := by
  unfold envFormulaR SettlingModel.envF
  refine foldr_and_sat ?_
  intro i _
  by_cases hi : i.val < vs.length
  · rw [sat_band_pad_agree i hi]
    exact envFaithful_sat i (hσd i.val i.isLt) (hσv i hi)
      (boundOf_pos hbs (vs.getD i.val "")).1 (boundOf_pos hbs (vs.getD i.val "")).2
      (hef i hi) ν
  · -- padded coordinate: both sides trivially true
    obtain ⟨hlo, hhi⟩ := hpadenv i (by omega)
    have hreal : boundOf eb (vs.getD i.val "") = (none, none) := by
      rw [getD_oob (by omega)]
      exact boundOf_notmem hnames
    rw [hreal]
    unfold bandFormulaR Band.formula
    rw [hlo, hhi]
    simp [Formula.sat]

/-- **The padded settling `hGd` discharger.** -/
theorem realGdOf_sat_pad (P : Parse.PProblem) (mt : TransMeta) (M : SettlingModel n)
    {εR : QF} (hεR : parseQ P.R.epsilon = some εR)
    (hf : faithfulSettling P mt M = true)
    (hlenLE : P.R.stateVars.length ≤ n)
    (hσd : ∀ j, j < n → (mt.scales.getD j (qOfInt 0)).pos)
    (hσv : ∀ j : Fin n, j.val < P.R.stateVars.length → 0 < sigmaOf mt.scales j)
    (hgcw : ∀ m ∈ M.modes, m.gcoord.val < P.R.stateVars.length)
    (hevnames : ∀ pm ∈ P.R.modes, "" ∉ cmpVarNames pm.evolve) :
    ∀ (q' : ℕ) (ν : DL.State (Var n)),
      Formula.sat (realGdOf P M q') ν
        ↔ Formula.sat (M.GdOf q')
            (scaleState (sigmaPad mt.scales P.R.stateVars.length) ν) := by
  obtain ⟨-, -, -, hml, hmode⟩ := faithfulSettling_facts hεR hf
  intro q' ν
  rcases hpm : P.R.modes[q']? with _ | pm
  · have hmnone : M.modes[q']? = none := by
      rw [List.getElem?_eq_none_iff] at hpm ⊢
      omega
    unfold realGdOf SettlingModel.GdOf
    rw [hpm, hmnone]
    simp [Formula.sat]
  rcases hm : M.modes[q']? with _ | m
  · exfalso
    rw [List.getElem?_eq_none_iff] at hm
    obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hpm
    omega
  obtain ⟨hmc, hbsb⟩ := hmode q' pm m hpm hm
  obtain ⟨eb, heb, hef⟩ := modeCore_env_facts_le hlenLE hmc
  obtain ⟨gb, hgb, hblo, hbhi⟩ := bandSettling_facts hbsb
  have hmm : m ∈ M.modes := by
    obtain ⟨h, hEq⟩ := List.getElem?_eq_some_iff.mp hm
    exact hEq ▸ List.getElem_mem h
  have hpmm : pm ∈ P.R.modes := by
    obtain ⟨h, hEq⟩ := List.getElem?_eq_some_iff.mp hpm
    exact hEq ▸ List.getElem_mem h
  have hgdred : realGdOf P M q'
      = Formula.and (envFormulaR P.R.stateVars n eb)
          (bandFormulaR m.gcoord
            (boundOf gb (P.R.stateVars.getD m.gcoord.val "")).1
            (boundOf gb (P.R.stateVars.getD m.gcoord.val "")).2) := by
    unfold realGdOf
    simp only [hpm, hm, heb, hgb]
  have hGdred : M.GdOf q'
      = Formula.and M.envF (bandDom m.gcoord (m.glo : ℝ) (m.ghi : ℝ)) := by
    unfold SettlingModel.GdOf
    rw [hm]
  rw [hgdred, hGdred]
  have hnames : ∀ e ∈ eb, e.1 ≠ "" := by
    intro e he hcontra
    have := boundsOfForm_names heb e he
    rw [hcontra] at this
    exact hevnames pm hpmm this
  have henv := envFormulaR_sat_pad M (boundsOfForm_pos heb) hlenLE hσd hσv
    hef (fun i hi => (modeCore_pad_facts hmc i hi).2) hnames ν
  have hband := bandSettling_sat (boundsOfForm_pos hgb) m hσd
    (hσv m.gcoord (hgcw m hmm)) ⟨hblo, hbhi⟩ ν
  simp only [Formula.sat]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨henv.mp h1, ?_⟩
    rw [← sat_bandDom_pad_agree m.gcoord (hgcw m hmm) (m.glo : ℝ) (m.ghi : ℝ) ν]
      at hband
    exact hband.mp h2
  · rintro ⟨h1, h2⟩
    refine ⟨henv.mpr h1, ?_⟩
    rw [← sat_bandDom_pad_agree m.gcoord (hgcw m hmm) (m.glo : ℝ) (m.ghi : ℝ) ν]
      at hband
    exact hband.mpr h2

/-- In-range positivity from the decidable entry check (padded-width form). -/
theorem sigmaOf_pos_lt {σq : List QF} (h : ∀ q ∈ σq, 0 < q.n ∧ 0 < q.d)
    {j : Fin n} (hj : j.val < σq.length) : 0 < sigmaOf σq j := by
  unfold sigmaOf QF.val
  rw [List.getD_eq_getElem _ _ hj]
  obtain ⟨hn, hd⟩ := h σq[j.val] (List.getElem_mem hj)
  have hnR : (0 : ℝ) < (σq[j.val].n : ℝ) := by exact_mod_cast hn
  have hdR : (0 : ℝ) < (σq[j.val].d : ℝ) := by exact_mod_cast hd
  positivity

/-! ## The padded assembly -/

/-- **The padded settling bridge.** -/
theorem faithfulSettling_rescale_pad (P : Parse.PProblem) (mt : TransMeta)
    (M : SettlingModel n) {εR : QF} (hεR : parseQ P.R.epsilon = some εR)
    (hf : faithfulSettling P mt M = true)
    (hnod : P.R.stateVars.Nodup) (hlenLE : P.R.stateVars.length ≤ n)
    (hσd : ∀ j, j < n → (mt.scales.getD j (qOfInt 0)).pos)
    (hσv : ∀ j : Fin n, j.val < P.R.stateVars.length → 0 < sigmaOf mt.scales j)
    (huv : 0 < (qDiv (qDiv εR mt.lam) (qOfInt M.dtQ)).val)
    (hshapes : ∀ m ∈ M.modes, ∀ i : Fin n, i.val < P.R.stateVars.length →
      padShapeOkB P.R.stateVars.length i (m.shapes i) = true)
    (hgcw : ∀ m ∈ M.modes, m.gcoord.val < P.R.stateVars.length)
    (hnoempty : ∀ pm ∈ P.R.modes, pm.odes.find? (fun o => o.1 == "") = none)
    (hevnames : ∀ pm ∈ P.R.modes, "" ∉ cmpVarNames pm.evolve)
    {q : ℕ} {pm : Parse.PMode} {m : SettlingMode n}
    (hpm : P.R.modes[q]? = some pm) (hm : M.modes[q]? = some m)
    (dts : ℝ)
    (hB : GuardSettlingB M.graph M.GdOf m.fieldOf (Term.const 1) M.envF dts q) :
    GuardSettlingB M.graph (realGdOf P M) (realFieldOf P.R.stateVars pm n)
      (Term.const 1) (realEnvOf P.R.stateVars n pm)
      ((qDiv (qDiv εR mt.lam) (qOfInt M.dtQ)).val * dts) q := by
  obtain ⟨hlam, hdt, -, hml, hmode⟩ := faithfulSettling_facts hεR hf
  have hud : (qDiv (qDiv εR mt.lam) (qOfInt M.dtQ)).pos :=
    qDiv_pos (qDiv_pos (parseQ_pos hεR) hlam) (by simpa [qOfInt] using hdt)
  obtain ⟨hmc, -⟩ := hmode q pm m hpm hm
  obtain ⟨eb, heb, hef⟩ := modeCore_env_facts_le hlenLE hmc
  have hmm : m ∈ M.modes := by
    obtain ⟨h, hEq⟩ := List.getElem?_eq_some_iff.mp hm
    exact hEq ▸ List.getElem_mem h
  have hpmm : pm ∈ P.R.modes := by
    obtain ⟨h, hEq⟩ := List.getElem?_eq_some_iff.mp hpm
    exact hEq ▸ List.getElem_mem h
  refine GuardSettlingB_rescale M.graph M.GdOf (realGdOf P M) m.fieldOf
    (realFieldOf P.R.stateVars pm n) M.envF (realEnvOf P.R.stateVars n pm)
    (sigmaPad mt.scales P.R.stateVars.length)
    (qDiv (qDiv εR mt.lam) (qOfInt M.dtQ)).val dts q
    (fun i => ne_of_gt (sigmaPad_pos hσv i)) huv
    (fieldOf_bridge_pad hnod hlenLE hσd hud pm m hmc
      (hshapes m hmm) (hnoempty pm hpmm))
    (realGdOf_sat_pad P mt M hεR hf hlenLE hσd hσv hgcw hevnames)
    ?_ hB
  intro ν
  have hered : realEnvOf P.R.stateVars n pm = envFormulaR P.R.stateVars n eb := by
    unfold realEnvOf
    simp only [heb]
  rw [hered]
  have hnames : ∀ e ∈ eb, e.1 ≠ "" := by
    intro e he hcontra
    have := boundsOfForm_names heb e he
    rw [hcontra] at this
    exact hevnames pm hpmm this
  exact envFormulaR_sat_pad M (boundsOfForm_pos heb) hlenLE hσd hσv hef
    (fun i hi => (modeCore_pad_facts hmc i hi).2) hnames ν

/-- **Padded settling family, real-model end to end (generic).** -/
theorem settling_real_end_to_end_pad (P : Parse.PProblem) (mt : TransMeta)
    (M : SettlingModel n) {εR : QF} (hεR : parseQ P.R.epsilon = some εR)
    (hfaith : faithfulSettling P mt M = true)
    (hnod : P.R.stateVars.Nodup) (hlenLE : P.R.stateVars.length ≤ n)
    (hσd : ∀ j, j < n → (mt.scales.getD j (qOfInt 0)).pos)
    (hσv : ∀ j : Fin n, j.val < P.R.stateVars.length → 0 < sigmaOf mt.scales j)
    (huv : 0 < (qDiv (qDiv εR mt.lam) (qOfInt M.dtQ)).val)
    (hshapes : ∀ m ∈ M.modes, ∀ i : Fin n, i.val < P.R.stateVars.length →
      padShapeOkB P.R.stateVars.length i (m.shapes i) = true)
    (hgcw : ∀ m ∈ M.modes, m.gcoord.val < P.R.stateVars.length)
    (hnoempty : ∀ pm ∈ P.R.modes, pm.odes.find? (fun o => o.1 == "") = none)
    (hevnames : ∀ pm ∈ P.R.modes, "" ∉ cmpVarNames pm.evolve)
    (mv tg : Var n) (g : Term (Var n)) (fL : Fin n → Term (Var n))
    (hwf : decideWellFormed M = true) (hdt : (0 : ℝ) ≤ (M.dt : ℝ))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (M.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (M.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (M.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    :
    ∀ q pm m, P.R.modes[q]? = some pm → M.modes[q]? = some m →
      GuardSettlingB M.graph (realGdOf P M) (realFieldOf P.R.stateVars pm n)
        (Term.const 1) (realEnvOf P.R.stateVars n pm)
        ((qDiv (qDiv εR mt.lam) (qOfInt M.dtQ)).val * (M.dt : ℝ)) q := by
  intro q pm m hpm hm
  have hH : GuardSettlingH M.graph M.GdOf mv g (Term.const 1) tg (M.dt : ℝ) fL M.envF :=
    wellformed_sound M mv tg g fL hwf hdt hg hmvclk hmvtg hmvGd htgGd hfrzGd
  exact faithfulSettling_rescale_pad P mt M hεR hfaith hnod hlenLE hσd hσv huv
    hshapes hgcw hnoempty hevnames hpm hm (M.dt : ℝ) (GuardSettlingH_B' M M.GdOf hH hm)

end RelCertifier
