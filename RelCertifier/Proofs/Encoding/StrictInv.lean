/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Strict invariant rows: the mask-selected conjunction (extension `strict-atoms`)

A row's components `g :: gs` carry a strictness mask `m : List Bool` aligned with them (the
flatten order of `invComponents`, `Oracle.invStrictFlags`): component `i` means `gᵢ < 0` when
`m[i]` is `true` and `gᵢ ≤ 0` otherwise (a missing flag is `false`). This file mirrors the
list-invariant layer of `EnvelopeChainM` (`FM`, `canonInvM` and their encode/sat/fv lemmas)
for the mask-selected conjunction:

* `invLt`, `invAt` (the atom formula selected by a flag), `HoldsAt` (its scalar meaning);
* `tagS` (components paired with their flags), `FMS g gs m`, `canonInvMS g gs m`;
* `sat_FMS_iff`, `FMS_fv`, `notMem_FMS_fv`, `encode_canonInvMS`, `canonInvMS_varsL/R`;
* **collapse**: with an all-false mask, `FMS = FM` and `canonInvMS = canonInvM`, so the
  existing theorems are the special case;
* **weakening**: `FMS → FM` (the closure), so every proof that only ASSUMES the row is
  reused unchanged.

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChainM
import RelCertifier.Proofs.Flow.DIStrictOpen

namespace RelCertifier
open DL DLCalTiming DLRel Set

variable {n : ℕ}

/-! ## The strict atom and the flag-selected atom -/

/-- The strict invariant `g < 0` as a `Formula`. -/
def invLt (g : Term (Var n)) : Formula (Var n) := Formula.cmp CompOp.lt g (Term.const 0)

@[simp] theorem sat_invLt (g : Term (Var n)) (ω : State (Var n)) :
    Formula.sat (invLt g) ω ↔ Term.eval g ω < 0 := by
  simp only [invLt, Formula.sat, CompOp.interp, Term.eval]

/-- The atom formula of a component selected by its flag. -/
def invAt : Bool → Term (Var n) → Formula (Var n)
  | true, g => invLt g
  | false, g => invLe g

/-- The scalar meaning of a flagged component. -/
def HoldsAt : Bool → Term (Var n) → State (Var n) → Prop
  | true, g, ω => Term.eval g ω < 0
  | false, g, ω => Term.eval g ω ≤ 0

@[simp] theorem invAt_false (g : Term (Var n)) : invAt false g = invLe g := rfl
@[simp] theorem invAt_true (g : Term (Var n)) : invAt true g = invLt g := rfl

theorem sat_invAt (b : Bool) (g : Term (Var n)) (ω : State (Var n)) :
    Formula.sat (invAt b g) ω ↔ HoldsAt b g ω := by
  cases b <;> simp [invAt, HoldsAt]

theorem HoldsAt.le {b : Bool} {g : Term (Var n)} {ω : State (Var n)} (h : HoldsAt b g ω) :
    Term.eval g ω ≤ 0 := by
  cases b
  · exact h
  · exact le_of_lt h

theorem holdsAt_false {g : Term (Var n)} {ω : State (Var n)} :
    HoldsAt false g ω ↔ Term.eval g ω ≤ 0 := Iff.rfl

theorem holdsAt_true {g : Term (Var n)} {ω : State (Var n)} :
    HoldsAt true g ω ↔ Term.eval g ω < 0 := Iff.rfl

theorem invAt_fv (b : Bool) (g : Term (Var n)) : (invAt b g).fv = (invLe g).fv := by
  cases b <;> rfl

/-! ## Components paired with their flags -/

/-- Each component with its flag (a missing flag is `false`). -/
def tagS : List (Term (Var n)) → List Bool → List (Bool × Term (Var n))
  | [], _ => []
  | c :: cs, m => (m.headD false, c) :: tagS cs m.tail

@[simp] theorem tagS_nil (m : List Bool) : tagS ([] : List (Term (Var n))) m = [] := rfl
@[simp] theorem tagS_cons (c : Term (Var n)) (cs : List (Term (Var n))) (m : List Bool) :
    tagS (c :: cs) m = (m.headD false, c) :: tagS cs m.tail := rfl

theorem tagS_map_snd (cs : List (Term (Var n))) (m : List Bool) :
    (tagS cs m).map Prod.snd = cs := by
  induction cs generalizing m with
  | nil => rfl
  | cons c cs ih => simp [ih]

theorem mem_tagS_snd {cs : List (Term (Var n))} {m : List Bool} {c : Bool × Term (Var n)}
    (h : c ∈ tagS cs m) : c.2 ∈ cs := by
  rw [← tagS_map_snd cs m]; exact List.mem_map_of_mem h

theorem exists_mem_tagS {cs : List (Term (Var n))} (m : List Bool) {g : Term (Var n)}
    (h : g ∈ cs) : ∃ b, (b, g) ∈ tagS cs m := by
  rw [← tagS_map_snd cs m] at h
  obtain ⟨⟨b, g'⟩, hm, rfl⟩ := List.mem_map.mp h
  exact ⟨b, hm⟩

/-- An all-false mask tags every component `false`. -/
theorem tagS_allFalse (cs : List (Term (Var n))) {m : List Bool} (h : ∀ b ∈ m, b = false) :
    tagS cs m = cs.map (fun c => (false, c)) := by
  induction cs generalizing m with
  | nil => rfl
  | cons c cs ih =>
      have hhd : m.headD false = false := by
        cases m with
        | nil => rfl
        | cons b bs => exact h b List.mem_cons_self
      have htl : ∀ b ∈ m.tail, b = false := fun b hb => h b (List.mem_of_mem_tail hb)
      rw [tagS_cons, hhd, ih htl]; rfl

theorem tagS_append (cs ts : List (Term (Var n))) (m : List Bool) :
    tagS (cs ++ ts) m = tagS cs m ++ tagS ts (m.drop cs.length) := by
  induction cs generalizing m with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.cons_append, tagS_cons, ih, List.length_cons]
      congr 2
      cases m <;> simp

/-! ## The mask-selected conjunction -/

/-- The fold of flagged atoms over a base formula. -/
def foldAt (ts : List (Bool × Term (Var n))) (B : Formula (Var n)) : Formula (Var n) :=
  ts.foldr (fun c acc => Formula.and (invAt c.1 c.2) acc) B

theorem sat_foldAt (ts : List (Bool × Term (Var n))) (B : Formula (Var n))
    (ν : State (Var n)) :
    Formula.sat (foldAt ts B) ν ↔ (∀ c ∈ ts, HoldsAt c.1 c.2 ν) ∧ Formula.sat B ν := by
  induction ts with
  | nil => simp [foldAt]
  | cons c ts ih =>
      show Formula.sat (invAt c.1 c.2) ν ∧ Formula.sat (foldAt ts B) ν ↔ _
      rw [ih, sat_invAt, List.forall_mem_cons]
      tauto

theorem foldAt_fv (ts : List (Bool × Term (Var n))) (B : Formula (Var n)) :
    (foldAt ts B).fv =
      ((ts.map Prod.snd).foldr (fun g acc => Formula.and (invLe g) acc) B).fv := by
  induction ts with
  | nil => rfl
  | cons c ts ih =>
      show (invAt c.1 c.2).fv ∪ (foldAt ts B).fv = (invLe c.2).fv ∪ _
      rw [invAt_fv, ih]

/-- `g₀ ∼₀ 0 ∧ … ∧ gₘ ∼ₘ 0`, each `∼ᵢ` selected by the mask (head `g`, tail `gs`, the
same nesting as `FM`). -/
def FMS (g : Term (Var n)) (gs : List (Term (Var n))) (m : List Bool) : Formula (Var n) :=
  foldAt (tagS gs m.tail) (invAt (m.headD false) g)

theorem sat_FMS_iff (g : Term (Var n)) (gs : List (Term (Var n))) (m : List Bool)
    (ν : State (Var n)) :
    Formula.sat (FMS g gs m) ν ↔ ∀ c ∈ tagS (g :: gs) m, HoldsAt c.1 c.2 ν := by
  rw [FMS, sat_foldAt, sat_invAt, tagS_cons, List.forall_mem_cons]
  tauto

/-- **Collapse**: an all-false mask is the existing conjunction. -/
theorem FMS_allFalse (g : Term (Var n)) (gs : List (Term (Var n))) {m : List Bool}
    (h : ∀ b ∈ m, b = false) : FMS g gs m = FM g gs := by
  have hhd : m.headD false = false := by
    cases m with
    | nil => rfl
    | cons b bs => exact h b List.mem_cons_self
  have htl : ∀ b ∈ m.tail, b = false := fun b hb => h b (List.mem_of_mem_tail hb)
  unfold FMS FM foldAt
  rw [tagS_allFalse gs htl, hhd, List.foldr_map]
  rfl

@[simp] theorem FMS_nil_mask (g : Term (Var n)) (gs : List (Term (Var n))) :
    FMS g gs [] = FM g gs :=
  FMS_allFalse g gs (by simp)

theorem FMS_fv (g : Term (Var n)) (gs : List (Term (Var n))) (m : List Bool) :
    (FMS g gs m).fv = (FM g gs).fv := by
  unfold FMS FM
  rw [foldAt_fv, tagS_map_snd]
  induction gs with
  | nil => exact invAt_fv _ _
  | cons g' rest ih =>
      show (invLe g').fv ∪ _ = (invLe g').fv ∪ _
      rw [ih]

theorem notMem_FMS_fv {g : Term (Var n)} {gs : List (Term (Var n))} {m : List Bool}
    {v : Var n} (h : ∀ g' ∈ g :: gs, v ∉ g'.fv) : v ∉ (FMS g gs m).fv := by
  rw [FMS_fv]; exact notMem_FM_fv h

/-- **Weakening**: the mask-selected conjunction implies its closure. -/
theorem FMS_weaken {g : Term (Var n)} {gs : List (Term (Var n))} {m : List Bool}
    {ν : State (Var n)} (h : Formula.sat (FMS g gs m) ν) : Formula.sat (FM g gs) ν := by
  rw [sat_FM_iff]
  intro g' hg'
  obtain ⟨b, hb⟩ := exists_mem_tagS m hg'
  exact ((sat_FMS_iff g gs m ν).mp h _ hb).le

/-- A state in the closure where every strict component is strictly negative is in `FMS`. -/
theorem FMS_of_FM {g : Term (Var n)} {gs : List (Term (Var n))} {m : List Bool}
    {ν : State (Var n)} (h : Formula.sat (FM g gs) ν)
    (hs : ∀ c ∈ tagS (g :: gs) m, c.1 = true → Term.eval c.2 ν < 0) :
    Formula.sat (FMS g gs m) ν := by
  rw [sat_FMS_iff]
  intro c hc
  rcases c with ⟨b, c⟩
  cases b
  · exact (sat_FM_iff g gs ν).mp h c (mem_tagS_snd hc)
  · exact hs _ hc rfl

/-- `FMS` over an appended tail whose extra components carry no flag. -/
theorem sat_FMS_append (g : Term (Var n)) (gs ts : List (Term (Var n))) (m : List Bool)
    (hm : m.length ≤ gs.length + 1) (ν : State (Var n)) :
    Formula.sat (FMS g (gs ++ ts) m) ν ↔
      Formula.sat (FMS g gs m) ν ∧ ∀ t ∈ ts, Term.eval t ν ≤ 0 := by
  rw [sat_FMS_iff, sat_FMS_iff, ← List.cons_append, tagS_append]
  have hdrop : m.drop (g :: gs).length = [] := by
    rw [List.drop_eq_nil_iff]; simpa using hm
  rw [hdrop, tagS_allFalse ts (by simp)]
  simp only [List.mem_append, List.mem_map]
  constructor
  · intro h
    exact ⟨fun c hc => h c (Or.inl hc), fun t ht => h (false, t) (Or.inr ⟨t, ht, rfl⟩)⟩
  · rintro ⟨h1, h2⟩ c (hc | ⟨t, ht, rfl⟩)
    · exact h1 c hc
    · exact h2 t ht

/-! ## The relational form -/

/-- The canonical strict relational invariant `⌊g⌋ < 0`. -/
def canonInvLt (g : Term (Var n)) : RFormula (Var n) :=
  RFormula.cmp CompOp.lt (rsplit g) (RTerm.proj DLRel.Side.L (Term.const 0))

/-- The canonical relational invariant selected by a flag. -/
def canonInvAt : Bool → Term (Var n) → RFormula (Var n)
  | true, g => canonInvLt g
  | false, g => canonInv g

theorem encode_canonInvLt (g : Term (Var n)) :
    encode (Equiv.refl (Var n)) (canonInvLt g) = invLt g := by
  unfold encode canonInvLt invLt
  simp only [RFormula.renameR, RTerm.renameR, rsplit_renameR_refl]
  simp only [RFormula.enc, RTerm.enc, rsplit_enc]

theorem encode_canonInvAt (b : Bool) (g : Term (Var n)) :
    encode (Equiv.refl (Var n)) (canonInvAt b g) = invAt b g := by
  cases b
  · exact encode_canonInv g
  · exact encode_canonInvLt g

theorem canonInvAt_varsL (b : Bool) (g : Term (Var n)) :
    (canonInvAt b g).varsL = (canonInv g).varsL := by
  cases b <;> rfl

theorem canonInvAt_varsR (b : Bool) (g : Term (Var n)) :
    (canonInvAt b g).varsR = (canonInv g).varsR := by
  cases b <;> rfl

/-- The relational fold of flagged canonical atoms over a base. -/
def rfoldAt (ts : List (Bool × Term (Var n))) (B : RFormula (Var n)) : RFormula (Var n) :=
  ts.foldr (fun c acc => RFormula.and (canonInvAt c.1 c.2) acc) B

/-- The relational mask-selected conjunction (the strict `canonInvM`). -/
def canonInvMS (g : Term (Var n)) (gs : List (Term (Var n))) (m : List Bool) :
    RFormula (Var n) :=
  rfoldAt (tagS gs m.tail) (canonInvAt (m.headD false) g)

theorem encode_rfoldAt (ts : List (Bool × Term (Var n))) (B : RFormula (Var n)) :
    encode (Equiv.refl (Var n)) (rfoldAt ts B) = foldAt ts (encode (Equiv.refl (Var n)) B) := by
  induction ts with
  | nil => rfl
  | cons c ts ih =>
      show encode _ (RFormula.and (canonInvAt c.1 c.2) (rfoldAt ts B))
        = Formula.and (invAt c.1 c.2) (foldAt ts _)
      have hdist : encode (Equiv.refl (Var n)) (RFormula.and (canonInvAt c.1 c.2) (rfoldAt ts B))
          = Formula.and (encode (Equiv.refl (Var n)) (canonInvAt c.1 c.2))
            (encode (Equiv.refl (Var n)) (rfoldAt ts B)) := by
        unfold encode
        simp only [RFormula.renameR, RFormula.enc]
      rw [hdist, encode_canonInvAt, ih]

theorem encode_canonInvMS (g : Term (Var n)) (gs : List (Term (Var n))) (m : List Bool) :
    encode (Equiv.refl (Var n)) (canonInvMS g gs m) = FMS g gs m := by
  unfold canonInvMS FMS
  rw [encode_rfoldAt, encode_canonInvAt]

theorem rfoldAt_varsL (ts : List (Bool × Term (Var n))) (B : RFormula (Var n)) :
    (rfoldAt ts B).varsL =
      ((ts.map Prod.snd).foldr (fun g acc => RFormula.and (canonInv g) acc) B).varsL := by
  induction ts with
  | nil => rfl
  | cons c ts ih =>
      show (canonInvAt c.1 c.2).varsL ∪ (rfoldAt ts B).varsL = (canonInv c.2).varsL ∪ _
      rw [canonInvAt_varsL, ih]

theorem rfoldAt_varsR (ts : List (Bool × Term (Var n))) (B : RFormula (Var n)) :
    (rfoldAt ts B).varsR =
      ((ts.map Prod.snd).foldr (fun g acc => RFormula.and (canonInv g) acc) B).varsR := by
  induction ts with
  | nil => rfl
  | cons c ts ih =>
      show (canonInvAt c.1 c.2).varsR ∪ (rfoldAt ts B).varsR = (canonInv c.2).varsR ∪ _
      rw [canonInvAt_varsR, ih]

theorem canonInvMS_varsL_eq (g : Term (Var n)) (gs : List (Term (Var n))) (m : List Bool) :
    (canonInvMS g gs m).varsL = (canonInvM g gs).varsL := by
  unfold canonInvMS canonInvM
  rw [rfoldAt_varsL, tagS_map_snd]
  induction gs with
  | nil => exact canonInvAt_varsL _ _
  | cons g' rest ih =>
      show (canonInv g').varsL ∪ _ = (canonInv g').varsL ∪ _
      rw [ih]

theorem canonInvMS_varsR_eq (g : Term (Var n)) (gs : List (Term (Var n))) (m : List Bool) :
    (canonInvMS g gs m).varsR = (canonInvM g gs).varsR := by
  unfold canonInvMS canonInvM
  rw [rfoldAt_varsR, tagS_map_snd]
  induction gs with
  | nil => exact canonInvAt_varsR _ _
  | cons g' rest ih =>
      show (canonInv g').varsR ∪ _ = (canonInv g').varsR ∪ _
      rw [ih]

theorem canonInvMS_varsL (g : Term (Var n)) (gs : List (Term (Var n))) (m : List Bool)
    (hg : ∀ g' ∈ g :: gs, g'.fv ⊆ range Lv ∪ range Rv) :
    (canonInvMS g gs m).varsL ⊆ range Lv := by
  rw [canonInvMS_varsL_eq]; exact canonInvM_varsL g gs hg

theorem canonInvMS_varsR (g : Term (Var n)) (gs : List (Term (Var n))) (m : List Bool) :
    (canonInvMS g gs m).varsR ⊆ range Rv := by
  rw [canonInvMS_varsR_eq]; exact canonInvM_varsR g gs

/-- **Collapse** (relational): an all-false mask is the existing `canonInvM`. -/
theorem canonInvMS_allFalse (g : Term (Var n)) (gs : List (Term (Var n))) {m : List Bool}
    (h : ∀ b ∈ m, b = false) : canonInvMS g gs m = canonInvM g gs := by
  have hhd : m.headD false = false := by
    cases m with
    | nil => rfl
    | cons b bs => exact h b List.mem_cons_self
  have htl : ∀ b ∈ m.tail, b = false := fun b hb => h b (List.mem_of_mem_tail hb)
  unfold canonInvMS canonInvM rfoldAt
  rw [tagS_allFalse gs htl, hhd, List.foldr_map]
  rfl

@[simp] theorem canonInvMS_nil_mask (g : Term (Var n)) (gs : List (Term (Var n))) :
    canonInvMS g gs [] = canonInvM g gs :=
  canonInvMS_allFalse g gs (by simp)

end RelCertifier
