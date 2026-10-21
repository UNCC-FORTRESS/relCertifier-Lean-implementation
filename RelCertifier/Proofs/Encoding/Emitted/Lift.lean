/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Assumption 1, lifted by one coordinate (W3)

The suite's `WellFormedR` lemmas (`InstancesV2/WellFormed/*`) are stated at a fixed
dimension `n`; the clocked bridge needs one more auxiliary coordinate (the right clock), so
the generated instances live at `n+1`. The lowering of the same IR at `n+1` is the lowering
at `n` with every coordinate cast along `Fin.castSucc` and the new coordinate unbound: the
state variables are the same, so `dynOf` gives the new coordinate derivative `0` and no
guard or domain mentions it. Hence every solution at `n+1` projects to one at `n`
(`odeSol_proj`) and every solution at `n` extends with the new coordinates constant
(`odeSol_ext`), and Assumption 1 lifts (`wellFormedR_lift`).

The syntactic facts are one decidable bundle, `padOK p n`, which a generated instance proves
by `decide +kernel`: for every right mode (and the out-of-range default), the guard and the
evolve domain lower at `n+1` to the embedding of their lowering at `n`, and the dynamics
lower to the embedding with the new coordinate frozen.
-/
import RelCertifier.Proofs.Encoding.Emitted.Transport

set_option autoImplicit false

namespace RelCertifier

open DL

/-! ## The embedding of the IR along `Fin.castSucc` -/

/-- A coordinate of `Var n` as one of `Var (n+1)`. -/
def castVar {n : ℕ} (v : Var n) : Var (n+1) := (v.1, v.2.castSucc)

def ITerm.embed {n : ℕ} : ITerm n → ITerm (n+1)
  | .var v => .var (castVar v)
  | .rat q => .rat q
  | .bin op a b => .bin op a.embed b.embed

def IForm.embed {n : ℕ} : IForm n → IForm (n+1)
  | .tt => .tt
  | .cmp op a b => .cmp op a.embed b.embed
  | .neg f => .neg f.embed
  | .and a b => .and a.embed b.embed

namespace Emitted

open DL DLCalTiming Parse Run Set

/-- The projection of a state at `n+1` to the coordinates of `n`. -/
def projState {n : ℕ} (x : State (Var (n+1))) : State (Var n) := fun v => x (castVar v)

/-- The extension of a state `y` at `n` by the new coordinates of `x'`. -/
def extState {n : ℕ} (x' : State (Var (n+1))) (y : State (Var n)) : State (Var (n+1)) :=
  fun w => if h : w.2.val < n then y (w.1, ⟨w.2.val, h⟩) else x' w

theorem extState_cast {n : ℕ} (x' : State (Var (n+1))) (y : State (Var n)) (v : Var n) :
    extState x' y (castVar v) = y v := by
  unfold extState castVar
  rw [dif_pos (by simp)]
  rfl

theorem extState_last {n : ℕ} (x' : State (Var (n+1))) (y : State (Var n)) (s : Side) :
    extState x' y (s, Fin.last n) = x' (s, Fin.last n) := by
  unfold extState
  rw [dif_neg (by simp)]

theorem projState_ext {n : ℕ} (x' : State (Var (n+1))) (y : State (Var n)) :
    projState (extState x' y) = y := by
  funext v; exact extState_cast x' y v

theorem extState_proj {n : ℕ} (x' : State (Var (n+1))) : extState x' (projState x') = x' := by
  funext w
  unfold extState
  split_ifs with h
  · rfl
  · rfl

theorem eval_embed {n : ℕ} (t : ITerm n) (x' : State (Var (n+1))) :
    t.embed.toHost.eval x' = t.toHost.eval (projState x') := by
  induction t with
  | var v => rfl
  | rat q => rfl
  | bin op a b iha ihb => simp only [ITerm.embed, ITerm.toHost, Term.eval, iha, ihb]

theorem sat_embed {n : ℕ} (f : IForm n) (x' : State (Var (n+1))) :
    f.embed.toHost.sat x' ↔ f.toHost.sat (projState x') := by
  induction f with
  | tt => exact Iff.rfl
  | cmp op a b => simp only [IForm.embed, IForm.toHost, Formula.sat, eval_embed]
  | neg f ih => simp only [IForm.embed, IForm.toHost, Formula.sat, ih]
  | and a b iha ihb => simp only [IForm.embed, IForm.toHost, Formula.sat, iha, ihb]

/-! ## The decidable padding bundle -/

/-- The dynamics of a right mode lower at `n+1` to the embedding of their lowering at `n`,
the new coordinate frozen (or fail to lower at both dimensions). -/
def dynPadOK (vars : List String) (n : ℕ) (m : PMode) : Bool :=
  match Run.dynOf vars n Side.R m, Run.dynOf vars (n+1) Side.R m with
  | some f, some f' =>
      (List.finRange n).all (fun j => decide (f' j.castSucc = (f j).embed)) &&
      decide (f' (Fin.last n) = .rat 0)
  | none, none => true
  | _, _ => false

/-- **The padding bundle**: for every right mode `q ≤ nR p` (`nR p` is the out-of-range
default mode), the guard and the evolve domain lower at `n+1` to the embedding of their
lowering at `n`, and the dynamics pad (`dynPadOK`). -/
def padOK (p : PProblem) (n : ℕ) : Bool :=
  (List.range (nR p + 1)).all (fun q =>
    decide (Run.lowerF (vars p) (n+1) Side.R (mRof p q).guard =
      (Run.lowerF (vars p) n Side.R (mRof p q).guard).map IForm.embed) &&
    decide (Run.lowerF (vars p) (n+1) Side.R (mRof p q).evolve =
      (Run.lowerF (vars p) n Side.R (mRof p q).evolve).map IForm.embed) &&
    dynPadOK (vars p) n (mRof p q))

theorem padOK_at {p : PProblem} {n : ℕ} (h : padOK p n = true) {q : ℕ} (hq : q ≤ nR p) :
    Run.lowerF (vars p) (n+1) Side.R (mRof p q).guard =
      (Run.lowerF (vars p) n Side.R (mRof p q).guard).map IForm.embed ∧
    Run.lowerF (vars p) (n+1) Side.R (mRof p q).evolve =
      (Run.lowerF (vars p) n Side.R (mRof p q).evolve).map IForm.embed ∧
    dynPadOK (vars p) n (mRof p q) = true := by
  simp only [padOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h q (Nat.lt_succ_of_le hq)
  exact ⟨h1, h2, h3⟩

theorem mRof_of_ge {p : PProblem} {q : ℕ} (h : nR p ≤ q) : mRof p q = dm := by
  unfold mRof
  exact List.getD_eq_default _ _ h

theorem guardR_pad {p : PProblem} {n : ℕ} (h : padOK p n = true) (q : ℕ) :
    Run.lowerF (vars p) (n+1) Side.R (mRof p q).guard =
      (Run.lowerF (vars p) n Side.R (mRof p q).guard).map IForm.embed := by
  by_cases hq : q ≤ nR p
  · exact (padOK_at h hq).1
  · rw [mRof_of_ge (by omega)]
    have := (padOK_at h (le_refl (nR p))).1
    rwa [mRof_of_ge (le_refl _)] at this

/-- A right guard at `n+1` is the right guard at `n` read on the projection. -/
theorem sat_guardR_succ {p : PProblem} {n : ℕ} (h : padOK p n = true) (q : ℕ)
    (x' : State (Var (n+1))) :
    (guardR p (n+1) q).sat x' ↔ (guardR p n q).sat (projState x') := by
  unfold guardR hostGuard
  rw [guardR_pad h q]
  rcases Run.lowerF (vars p) n Side.R (mRof p q).guard with _ | f
  · exact Iff.rfl
  · exact sat_embed f x'

/-- The right evolve domain at `n+1` is the one at `n` read on the projection. -/
theorem sat_domR_succ {p : PProblem} {n : ℕ} (h : padOK p n = true) (x' : State (Var (n+1))) :
    (domR p (n+1)).sat x' ↔ (domR p n).sat (projState x') := by
  unfold domR hostEvolve
  rw [(padOK_at h (Nat.zero_le _)).2.1]
  rcases Run.lowerF (vars p) n Side.R (mRof p 0).evolve with _ | f
  · exact Iff.rfl
  · exact sat_embed f x'

/-- A right-hand side at `n+1`, at a cast coordinate, is the one at `n` read on the
projection. -/
theorem fR_succ_eval {p : PProblem} {n : ℕ} (h : padOK p n = true) {q : ℕ} (hq : q ≤ nR p)
    (j : Fin n) (x' : State (Var (n+1))) :
    (fR p (n+1) q (Fin.castSucc j)).eval x' = (fR p n q j).eval (projState x') := by
  have hd := (padOK_at h hq).2.2
  unfold dynPadOK at hd
  revert hd
  unfold fR hostDyn
  rcases Run.dynOf (vars p) n Side.R (mRof p q) with _ | f <;>
    rcases Run.dynOf (vars p) (n+1) Side.R (mRof p q) with _ | f' <;> intro hd
  · rfl
  · simp at hd
  · simp at hd
  · simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, decide_eq_true_eq,
      true_implies] at hd
    show (ITerm.toHost (f' (Fin.castSucc j))).eval x' = (ITerm.toHost (f j)).eval (projState x')
    rw [hd.1 j]
    exact eval_embed _ _

/-- The new coordinate's right-hand side at `n+1` is `0`. -/
theorem eval_fR_succ_last {p : PProblem} {n : ℕ} (h : padOK p n = true) {q : ℕ} (hq : q ≤ nR p)
    (x' : State (Var (n+1))) : (fR p (n+1) q (Fin.last n)).eval x' = 0 := by
  have hd := (padOK_at h hq).2.2
  unfold dynPadOK at hd
  revert hd
  unfold fR hostDyn
  rcases Run.dynOf (vars p) n Side.R (mRof p q) with _ | f <;>
    rcases Run.dynOf (vars p) (n+1) Side.R (mRof p q) with _ | f' <;> intro hd
  · rfl
  · simp at hd
  · simp at hd
  · simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, decide_eq_true_eq,
      true_implies] at hd
    show (ITerm.toHost (f' (Fin.last n))).eval x' = 0
    rw [hd.2]
    simp [ITerm.toHost, Term.eval]

/-! ## The right block at the two dimensions -/

theorem mem_rightBlock_iff {n : ℕ} (f : Fin n → Term (Var n)) (lam : Term (Var n))
    (pr : Var n × Term (Var n)) :
    pr ∈ rightBlock f lam ↔ ∃ i, pr = (Rv i, Term.binop .mul lam (f i)) := by
  simp only [rightBlock, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩

theorem bound_rightBlock {n : ℕ} (f : Fin n → Term (Var n)) (lam : Term (Var n)) (v : Var n) :
    v ∈ (rightBlock f lam).bound ↔ v.1 = Side.R := by
  simp only [ODESystem.bound, rightBlock, List.map_map, List.mem_map, List.mem_finRange,
    true_and, Function.comp]
  constructor
  · rintro ⟨i, rfl⟩; rfl
  · intro h; exact ⟨v.2, Prod.ext h.symm rfl⟩

/-- A right solution at `n` extends to one at `n+1` with the new coordinates constant. -/
theorem odeSol_ext {p : PProblem} {n : ℕ} (hpad : padOK p n = true) {q : ℕ} (hq : q ≤ nR p)
    (x' : State (Var (n+1))) {r : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol (rightBlock (fR p n q) (Term.const 1)) (domR p n) (projState x') r Φ) :
    ODESol (rightBlock (fR p (n+1) q) (Term.const 1)) (domR p (n+1)) x' r
      (fun t => extState x' (Φ t)) := by
  refine ⟨H.hr, ?_, ?_, ?_, ?_⟩
  · show extState x' (Φ 0) = x'
    rw [H.hΦ0, extState_proj]
  · intro t ht pr hpr
    obtain ⟨i, rfl⟩ := (mem_rightBlock_iff _ _ _).mp hpr
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have hmem : ((Rv j : Var n), Term.binop .mul (Term.const 1) (fR p n q j)) ∈
          rightBlock (fR p n q) (Term.const 1) :=
        List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
      have hd := H.hder t ht _ hmem
      have heq : (fun u => extState x' (Φ u) (Rv (Fin.castSucc j))) = fun u => Φ u (Rv j) := by
        funext u; exact extState_cast x' (Φ u) (Rv j)
      have hev : (Term.binop .mul (Term.const 1) (fR p (n+1) q (Fin.castSucc j))).eval
            (extState x' (Φ t))
          = (Term.binop .mul (Term.const 1) (fR p n q j)).eval (Φ t) := by
        simp only [Term.eval, fR_succ_eval hpad hq j, projState_ext]
      show HasDerivWithinAt (fun u => extState x' (Φ u) (Rv (Fin.castSucc j))) _ _ _
      rw [heq, hev]
      exact hd
    · have heq : (fun u => extState x' (Φ u) (Rv (Fin.last n))) = fun _ => x' (Rv (Fin.last n)) := by
        funext u; exact extState_last x' (Φ u) Side.R
      have hev : (Term.binop .mul (Term.const 1) (fR p (n+1) q (Fin.last n))).eval
            (extState x' (Φ t)) = 0 := by
        simp [Term.eval, AOp.interp, eval_fR_succ_last hpad hq]
      show HasDerivWithinAt (fun u => extState x' (Φ u) (Rv (Fin.last n))) _ _ _
      rw [heq, hev]
      exact hasDerivWithinAt_const _ _ _
  · intro t ht w hw
    rw [bound_rightBlock] at hw
    rcases Fin.eq_castSucc_or_eq_last w.2 with ⟨j, hj⟩ | hj
    · have hw' : w = castVar (w.1, j) := Prod.ext rfl hj
      have hmask := H.hmask t ht (w.1, j) (by rw [bound_rightBlock]; exact hw)
      show extState x' (Φ t) w = x' w
      rw [hw', extState_cast, hmask]
      rfl
    · have hw' : w = (w.1, Fin.last n) := Prod.ext rfl hj
      show extState x' (Φ t) w = x' w
      rw [hw', extState_last]
  · intro t ht
    show (domR p (n+1)).sat (extState x' (Φ t))
    rw [sat_domR_succ hpad, projState_ext]
    exact H.hdom t ht

/-- A right solution at `n+1` projects to one at `n`. -/
theorem odeSol_proj {p : PProblem} {n : ℕ} (hpad : padOK p n = true) {q : ℕ} (hq : q ≤ nR p)
    {x' : State (Var (n+1))} {r : ℝ} {Φ' : ℝ → State (Var (n+1))}
    (H : ODESol (rightBlock (fR p (n+1) q) (Term.const 1)) (domR p (n+1)) x' r Φ') :
    ODESol (rightBlock (fR p n q) (Term.const 1)) (domR p n) (projState x') r
      (fun t => projState (Φ' t)) := by
  refine ⟨H.hr, ?_, ?_, ?_, ?_⟩
  · show projState (Φ' 0) = projState x'
    rw [H.hΦ0]
  · intro t ht pr hpr
    obtain ⟨j, rfl⟩ := (mem_rightBlock_iff _ _ _).mp hpr
    have hmem : ((Rv (Fin.castSucc j) : Var (n+1)),
        Term.binop .mul (Term.const 1) (fR p (n+1) q (Fin.castSucc j))) ∈
          rightBlock (fR p (n+1) q) (Term.const 1) :=
      List.mem_map.mpr ⟨_, List.mem_finRange _, rfl⟩
    have hd := H.hder t ht _ hmem
    have hev : (Term.binop .mul (Term.const 1) (fR p (n+1) q (Fin.castSucc j))).eval (Φ' t)
        = (Term.binop .mul (Term.const 1) (fR p n q j)).eval (projState (Φ' t)) := by
      simp only [Term.eval, fR_succ_eval hpad hq j]
    rw [hev] at hd
    exact hd
  · intro t ht v hv
    rw [bound_rightBlock] at hv
    exact H.hmask t ht (castVar v) (by rw [bound_rightBlock]; exact hv)
  · intro t ht
    exact (sat_domR_succ hpad _).mp (H.hdom t ht)

/-- **Assumption 1 lifts by one coordinate.** Side condition: the decidable padding bundle
`padOK p n` (the IR lowers at `n+1` as the embedding of its lowering at `n`). -/
theorem wellFormedR_lift {p : PProblem} {n : ℕ} {pr : String → String → Bool} {ε : ℝ}
    (hpad : padOK p n = true) (h : WellFormedR (grOf p n pr) (guardR p n) ε) :
    WellFormedR (grOf p (n+1) pr) (guardR p (n+1)) ε := by
  intro q hq m' hm' x' hg hd _
  obtain ⟨hqn, rfl⟩ := grOf_modeAt_inv hm'
  have hqle : q ≤ nR p := hqn.le
  have hgx : (guardR p n q).sat (projState x') := (sat_guardR_succ hpad q x').mp hg
  have hdx : (domR p n).sat (projState x') := (sat_domR_succ hpad x').mp hd
  have hw := h q (by rw [grOf_len]; exact hqn) (modeOf p n q) (grOf_modeAt hqn) (projState x')
    hgx hdx trivial
  refine ⟨?_, ?_⟩
  · obtain ⟨Φ, hΦ⟩ := hw.1
    exact ⟨fun t => extState x' (Φ t), odeSol_ext hpad hqle x' hΦ⟩
  · intro t Φ' ht hΦ'
    obtain ⟨e, he, hsat⟩ := hw.2 t (fun u => projState (Φ' u)) ht (odeSol_proj hpad hqle hΦ')
    obtain ⟨-, nm, hnm, rfl⟩ := edgesFrom_grOf he
    refine ⟨edgeOf p (n+1) pr q nm, edge_mem_grOf hqn hnm, ?_⟩
    show (guardR p (n+1) (tgtIdx p nm)).sat (Φ' t)
    exact (sat_guardR_succ hpad _ _).mpr hsat

end Emitted
end RelCertifier
