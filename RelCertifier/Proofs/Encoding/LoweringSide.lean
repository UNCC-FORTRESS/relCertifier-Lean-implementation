/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Lowering side-splits: parser-lowered data lives on its declared side

The uniform dischargers (`UniformFvDischarge`) reduce every bookkeeping hypothesis to
three side-splits: left data on `Lv`, right data on `Rv`, the invariant on `Lv ∪ Rv`.
This file discharges THOSE from the lowering itself:

* `invToG_fv_LR` — the invariant term is Aux-free, hence on `Lv ∪ Rv` (no premise);
* `lowerE_fv_side` / `lowerF_fv_side` / `dynOf_fv_side` — a term/formula/field lowered
  with default side `s` lives on side `s`, PROVIDED no variable name in the source
  carries the opposite side prefix (`namesFree`) — a DECIDABLE syntactic check on the
  IR, dischargeable per benchmark by `decide`/`rfl`.

The prefix premise is necessary: `resolveVar` honors explicit `L_`/`R_` prefixes, so a
right-mode expression mentioning `L_x` genuinely reads the left. Benchmark mode bodies
use bare state names, so the check passes across the suite.
-/
import RelCertifier.Proofs.Encoding.FvDischarge

namespace RelCertifier
open DL Set

variable {n : ℕ}

/-- Total side classification: every non-Aux variable is an `Lv` or an `Rv`. -/
theorem notAux_mem_LR {x : Var n} (h : x.1 ≠ Side.Aux) : x ∈ range Lv ∪ range Rv := by
  obtain ⟨s, i⟩ := x
  cases s with
  | L => exact Or.inl ⟨i, rfl⟩
  | R => exact Or.inr ⟨i, rfl⟩
  | Aux => exact absurd rfl h

/-- The parser-lowered invariant term lives on `Lv ∪ Rv` — direct consequence of
`invToG_no_aux`, no premise. -/
theorem Run.invToG_fv_LR {vars : List String} {f : Parse.PForm} {gI : ITerm n}
    (h : Run.invToG vars n f = some gI) :
    (ITerm.toHost gI).fv ⊆ range Lv ∪ range Rv := by
  intro x hx
  refine notAux_mem_LR (fun haux => ?_)
  have hx' : ((Side.Aux, x.2) : Var n) ∈ (ITerm.toHost gI).fv := by
    rwa [show ((Side.Aux, x.2) : Var n) = x from Prod.ext haux.symm rfl]
  exact Run.invToG_no_aux h x.2 hx'

/-! ## Syntactic side purity (decidable, per benchmark by `rfl`) -/

/-- No variable name in the expression starts with the `bad` side prefix. -/
def Parse.PExpr.namesFree (bad : String) : Parse.PExpr → Bool
  | .var name => !name.startsWith bad
  | .num _ => true
  | .bin _ a b => a.namesFree bad && b.namesFree bad
  | .neg a => a.namesFree bad

/-- No variable name in the formula starts with the `bad` side prefix. -/
def Parse.PForm.namesFree (bad : String) : Parse.PForm → Bool
  | .tt => true
  | .cmp _ a b => a.namesFree bad && b.namesFree bad
  | .and x y => x.namesFree bad && y.namesFree bad
  | .or x y => x.namesFree bad && y.namesFree bad
  | .not x => x.namesFree bad

/-- The `finish` core of the `resolveVar` side inversions. -/
private theorem resolveVar_finish {vars : List String} {v : Var n} :
    ∀ (side : Side) (base : String),
      (match List.findIdx? (· == base) vars with
        | some i => if hlt : i < n then some ((side, ⟨i, hlt⟩) : Var n) else none
        | none => none) = some v → v.1 = side := by
  intro side base hm
  split at hm
  · split at hm
    · injection hm with h'
      subst h'
      rfl
    · exact absurd hm (by simp)
  · exact absurd hm (by simp)

/-- `resolveVar` at default side `L` yields a left variable when the name is not
`R_`-prefixed. -/
theorem Run.resolveVar_side_L {vars : List String} {name : String} {v : Var n}
    (hfree : name.startsWith "R_" = false)
    (h : Run.resolveVar vars n Side.L name = some v) : v.1 = Side.L := by
  unfold Run.resolveVar at h
  by_cases h1 : name.startsWith "L_"
  · simp only [h1, if_true] at h
    exact resolveVar_finish Side.L (Parse.dr name 2) h
  · rw [hfree] at h
    simp only [h1, Bool.false_eq_true, if_false] at h
    exact resolveVar_finish Side.L name h

/-- `resolveVar` at default side `R` yields a right variable when the name is not
`L_`-prefixed. -/
theorem Run.resolveVar_side_R {vars : List String} {name : String} {v : Var n}
    (hfree : name.startsWith "L_" = false)
    (h : Run.resolveVar vars n Side.R name = some v) : v.1 = Side.R := by
  unfold Run.resolveVar at h
  rw [hfree] at h
  by_cases h2 : name.startsWith "R_"
  · simp only [h2, Bool.false_eq_true, if_false, if_true] at h
    exact resolveVar_finish Side.R (Parse.dr name 2) h
  · simp only [h2, Bool.false_eq_true, if_false] at h
    exact resolveVar_finish Side.R name h

/-- The two side resolvers, packaged as the hypothesis the traversals thread. -/
def ResolvesTo (vars : List String) (n : ℕ) (s : Side) (bad : String) : Prop :=
  ∀ {name : String} {v : Var n}, name.startsWith bad = false →
    Run.resolveVar vars n s name = some v → v.1 = s

theorem resolvesTo_L (vars : List String) : ResolvesTo vars n Side.L "R_" :=
  fun hfree h => Run.resolveVar_side_L hfree h

theorem resolvesTo_R (vars : List String) : ResolvesTo vars n Side.R "L_" :=
  fun hfree h => Run.resolveVar_side_R hfree h

/-- A side-`s`-lowered, opposite-prefix-free expression lives on side `s`. -/
theorem Run.lowerE_fv_side {vars : List String} {s : Side} {bad : String}
    (hres : ResolvesTo vars n s bad) :
    ∀ {e : Parse.PExpr} {t : ITerm n},
      Parse.PExpr.namesFree bad e = true →
      Run.lowerE vars n s e = some t →
      ∀ v ∈ (ITerm.toHost t).fv, v.1 = s := by
  intro e
  induction e with
  | num str =>
      intro t hfree h v hv
      simp only [Run.lowerE, Option.map_eq_some_iff] at h
      obtain ⟨q, -, rfl⟩ := h
      exact absurd hv (by simp [ITerm.toHost, Term.fv])
  | var name =>
      intro t hfree h v hv
      simp only [Run.lowerE, Option.map_eq_some_iff] at h
      obtain ⟨w, hw, rfl⟩ := h
      simp only [ITerm.toHost, Term.fv, Set.mem_singleton_iff] at hv
      subst hv
      have hf : name.startsWith bad = false := by
        simpa [Parse.PExpr.namesFree] using hfree
      exact hres hf hw
  | neg a ih =>
      intro t hfree h v hv
      simp only [Run.lowerE, Option.map_eq_some_iff] at h
      obtain ⟨ta, hta, rfl⟩ := h
      simp only [ITerm.toHost, Term.fv, Set.mem_union] at hv
      rcases hv with hv | hv
      · exact absurd hv (by simp [Term.fv])
      · exact ih (by simpa [Parse.PExpr.namesFree] using hfree) hta v hv
  | bin op a b iha ihb =>
      intro t hfree h v hv
      have hfa : Parse.PExpr.namesFree bad a = true := by
        simp only [Parse.PExpr.namesFree, Bool.and_eq_true] at hfree
        exact hfree.1
      have hfb : Parse.PExpr.namesFree bad b = true := by
        simp only [Parse.PExpr.namesFree, Bool.and_eq_true] at hfree
        exact hfree.2
      simp only [Run.lowerE] at h
      rcases hea : Run.lowerE vars n s a with _ | ea <;> rw [hea] at h
      · simp at h
      rcases heb : Run.lowerE vars n s b with _ | eb <;> rw [heb] at h
      · simp at h
      simp only [Option.bind_eq_bind, Option.bind] at h
      have hbin : ∀ aop : AOp, t = ITerm.bin aop ea eb → v.1 = s := by
        intro aop ht
        subst ht
        simp only [ITerm.toHost, Term.fv, Set.mem_union] at hv
        rcases hv with hv | hv
        · exact iha hfa hea v hv
        · exact ihb hfb heb v hv
      split at h
      · injection h with h'; exact hbin _ h'.symm
      · injection h with h'; exact hbin _ h'.symm
      · injection h with h'; exact hbin _ h'.symm
      · split at h
        · split at h
          · simp at h
          · injection h with h'
            subst h'
            exact absurd hv (by simp [ITerm.toHost, Term.fv])
        · simp at h
      · simp at h

/-- A side-`s`-lowered, opposite-prefix-free formula lives on side `s`. -/
theorem Run.lowerF_fv_side {vars : List String} {s : Side} {bad : String}
    (hres : ResolvesTo vars n s bad) :
    ∀ {f : Parse.PForm} {ff : IForm n},
      Parse.PForm.namesFree bad f = true →
      Run.lowerF vars n s f = some ff →
      ∀ v ∈ (IForm.toHost ff).fv, v.1 = s := by
  intro f
  induction f with
  | tt =>
      intro ff hfree h v hv
      simp only [Run.lowerF] at h
      injection h with h'
      subst h'
      exact absurd hv (by simp [IForm.toHost, Formula.fv])
  | cmp op a b =>
      intro ff hfree h v hv
      have hfa : Parse.PExpr.namesFree bad a = true := by
        simp only [Parse.PForm.namesFree, Bool.and_eq_true] at hfree
        exact hfree.1
      have hfb : Parse.PExpr.namesFree bad b = true := by
        simp only [Parse.PForm.namesFree, Bool.and_eq_true] at hfree
        exact hfree.2
      simp only [Run.lowerF] at h
      rcases hea : Run.lowerE vars n s a with _ | ea <;> rw [hea] at h
      · simp at h
      rcases heb : Run.lowerE vars n s b with _ | eb <;> rw [heb] at h
      · simp at h
      simp only [Option.bind_eq_bind, Option.bind] at h
      have hcmp : ∀ c : CompOp, ff = IForm.cmp c ea eb → v.1 = s := by
        intro c hff
        subst hff
        simp only [IForm.toHost, Formula.fv, Set.mem_union] at hv
        rcases hv with hv | hv
        · exact Run.lowerE_fv_side hres hfa hea v hv
        · exact Run.lowerE_fv_side hres hfb heb v hv
      split at h
      · injection h with h'; exact hcmp _ h'.symm
      · injection h with h'; exact hcmp _ h'.symm
      · injection h with h'; exact hcmp _ h'.symm
      · injection h with h'; exact hcmp _ h'.symm
      · injection h with h'; exact hcmp _ h'.symm
      · simp at h
  | and x y ihx ihy =>
      intro ff hfree h v hv
      have hfx : Parse.PForm.namesFree bad x = true := by
        simp only [Parse.PForm.namesFree, Bool.and_eq_true] at hfree
        exact hfree.1
      have hfy : Parse.PForm.namesFree bad y = true := by
        simp only [Parse.PForm.namesFree, Bool.and_eq_true] at hfree
        exact hfree.2
      simp only [Run.lowerF] at h
      rcases hfx' : Run.lowerF vars n s x with _ | fx <;> rw [hfx'] at h
      · simp at h
      rcases hfy' : Run.lowerF vars n s y with _ | fy <;> rw [hfy'] at h
      · simp at h
      simp only [Option.bind_eq_bind, Option.bind] at h
      injection h with h'
      subst h'
      simp only [IForm.toHost, Formula.fv, Set.mem_union] at hv
      rcases hv with hv | hv
      · exact ihx hfx hfx' v hv
      · exact ihy hfy hfy' v hv
  | or x y ihx ihy => intro ff hfree h; exact absurd h (by simp [Run.lowerF])
  | not x ihx => intro ff hfree h; exact absurd h (by simp [Run.lowerF])

/-! ## The field lowering (`dynOf`) -/

/-- `mapM` over `Option` yields elementwise successes. -/
theorem mapM_option_spec {α β : Type*} (g : α → Option β) :
    ∀ (l : List α) (ts : List β), l.mapM g = some ts →
      ts.length = l.length ∧ ∀ (k : ℕ) (hk : k < l.length),
        ∃ (hk' : k < ts.length), g l[k] = some ts[k] := by
  intro l
  induction l with
  | nil =>
      intro ts h
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h
      exact ⟨rfl, fun k hk => absurd hk (by simp)⟩
  | cons a l ih =>
      intro ts h
      simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at h
      obtain ⟨b, hb, ts', hts', hcons⟩ := h
      injection hcons with hcons
      subst hcons
      obtain ⟨hlen, hspec⟩ := ih ts' hts'
      refine ⟨by simp [hlen], ?_⟩
      intro k hk
      match k with
      | 0 => exact ⟨by simp, by simpa using hb⟩
      | k + 1 =>
          have hk'' : k < l.length := by simpa using hk
          obtain ⟨hk', hgk⟩ := hspec k hk''
          exact ⟨by simpa using hk', by simpa using hgk⟩

/-- Inversion of `dynOf`: each coordinate's field is either the inert `0` (no ode
declared) or the side-lowered image of a declared ode expression. -/
theorem Run.dynOf_spec {vars : List String} {s : Side} {m : Parse.PMode}
    {f : Fin n → ITerm n} (h : Run.dynOf vars n s m = some f) (i : Fin n) :
    f i = ITerm.rat 0 ∨
      ∃ o ∈ m.odes, Run.lowerE vars n s o.2 = some (f i) := by
  simp only [Run.dynOf, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨terms, hterms, hf⟩ := h
  obtain ⟨hlen, hspec⟩ := mapM_option_spec _ _ _ hterms
  have hi : i.val < (List.finRange n).length := by simpa using i.isLt
  obtain ⟨hi', hgi⟩ := hspec i.val hi
  have hfi : f i = terms[i.val] := by
    rw [← hf]
    exact (List.getD_eq_getElem terms _ hi').symm ▸ rfl
  have hidx : (List.finRange n)[i.val] = i := by
    apply Fin.ext
    simp [List.getElem_finRange]
  rw [hidx] at hgi
  rcases hfind : m.odes.find? (fun p => p.1 == vars.getD i.val "") with _ | o <;>
    rw [hfind] at hgi
  · left
    injection hgi with hgi
    rw [hfi, ← hgi]
  · right
    exact ⟨o, List.mem_of_find?_eq_some hfind, by rw [hfi]; exact (by
      rcases o with ⟨name, e⟩
      simpa using hgi)⟩

/-- A side-`s`-lowered field (all declared odes opposite-prefix-free) lives on side `s`. -/
theorem Run.dynOf_fv_side {vars : List String} {s : Side} {bad : String}
    (hres : ResolvesTo vars n s bad)
    {m : Parse.PMode} {f : Fin n → ITerm n}
    (hfree : m.odes.all (fun o => Parse.PExpr.namesFree bad o.2) = true)
    (h : Run.dynOf vars n s m = some f) (i : Fin n) :
    ∀ v ∈ (ITerm.toHost (f i)).fv, v.1 = s := by
  intro v hv
  rcases Run.dynOf_spec h i with hz | ⟨o, ho, hlow⟩
  · rw [hz] at hv
    exact absurd hv (by simp [ITerm.toHost, Term.fv])
  · exact Run.lowerE_fv_side hres (List.all_eq_true.mp hfree o ho) hlow v hv

/-! ## Side-membership packaging (`v.1 = s` ⟹ range membership) -/

theorem side_eq_L_mem {x : Var n} (h : x.1 = Side.L) : x ∈ range Lv :=
  ⟨x.2, Prod.ext h.symm rfl⟩

theorem side_eq_R_mem {x : Var n} (h : x.1 = Side.R) : x ∈ range Rv :=
  ⟨x.2, Prod.ext h.symm rfl⟩

/-! ## Pipeline forms (the `Option`-chained shapes the instances define) -/

/-- The instance-shaped field pipeline lives on side `s` (the `none`/failure branches
default to the variable-free `0`). The `namesFree` premise is per benchmark by `rfl`. -/
theorem field_pipeline_side {vars : List String} {s : Side} {bad : String}
    (hres : ResolvesTo vars n s bad) (om : Option Parse.PMode)
    (hfree : om.all (fun m => m.odes.all
      (fun o => Parse.PExpr.namesFree bad o.2)) = true) (i : Fin n) :
    ∀ x ∈ (((om.bind (Run.dynOf vars n s)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0)).fv, x.1 = s := by
  rcases om with _ | m
  · intro x hx
    exact absurd hx (by simp [Term.fv])
  · rcases hdyn : Run.dynOf vars n s m with _ | f
    · intro x hx
      rw [Option.bind_some, hdyn] at hx
      exact absurd hx (by simp [Term.fv])
    · intro x hx
      rw [Option.bind_some, hdyn, Option.map_some, Option.getD_some] at hx
      exact Run.dynOf_fv_side hres (by simpa using hfree) hdyn i x hx

/-- The instance-shaped domain pipeline lives on side `s`. -/
theorem form_pipeline_side {vars : List String} {s : Side} {bad : String}
    (hres : ResolvesTo vars n s bad) (om : Option Parse.PMode)
    (hfree : om.all (fun m => Parse.PForm.namesFree bad m.evolve) = true) :
    ∀ x ∈ (((om.bind (fun m => Run.lowerF vars n s m.evolve)).map
      IForm.toHost).getD Formula.tt).fv, x.1 = s := by
  rcases om with _ | m
  · intro x hx
    exact absurd hx (by simp [Formula.fv])
  · rcases hlow : Run.lowerF vars n s m.evolve with _ | ff
    · intro x hx
      rw [Option.bind_some, hlow] at hx
      exact absurd hx (by simp [Formula.fv])
    · intro x hx
      rw [Option.bind_some, hlow, Option.map_some, Option.getD_some] at hx
      exact Run.lowerF_fv_side hres (by simpa using hfree) hlow x hx

/-- The instance-shaped invariant pipeline lives on `Lv ∪ Rv` — no premise. -/
theorem invToG_pipeline_LR {vars : List String} (f : Parse.PForm) :
    (((Run.invToG vars n f).map ITerm.toHost).getD (Term.const 0)).fv
      ⊆ range Lv ∪ range Rv := by
  rcases hg : Run.invToG vars n f with _ | gI
  · intro x hx
    exact absurd hx (by simp [Term.fv])
  · rw [Option.map_some, Option.getD_some]
    exact Run.invToG_fv_LR hg

end RelCertifier
