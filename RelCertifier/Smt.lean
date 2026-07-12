/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Computable SMT-LIB front-end (trusted IO-shell plumbing)

`DL.Term` carries `const : ℝ → Term`, and `ℝ` is not computably printable, so the
runnable front-end works over a small **computable IR** with `ℚ` constants and maps
it to the host `Term (Var n)` / `Formula (Var n)` via `toHost`.

The IR mirrors the verified `tderiv` / `lieDeriv` / `flowQuery`, and the bridge
lemmas (`itderiv_toHost`, `ilieDeriv_toHost`, `iflowQuery_toHost`) prove the mirror
denotes exactly the verified object. So the emitted SMT-LIB text is pinned to the
verified `flowQuery` — the string is not free-floating.
-/
import RelCertifier.FlowCert

namespace RelCertifier

open DL

/-! ## Computable IR -/

/-- Computable term IR over the joint variable space (`ℚ` constants). -/
inductive ITerm (n : ℕ) where
  | var : Var n → ITerm n
  | rat : ℚ → ITerm n
  | bin : AOp → ITerm n → ITerm n → ITerm n
  deriving Repr, DecidableEq

/-- Computable box-free formula IR. -/
inductive IForm (n : ℕ) where
  | tt  : IForm n
  | cmp : CompOp → ITerm n → ITerm n → IForm n
  | neg : IForm n → IForm n
  | and : IForm n → IForm n → IForm n
  deriving Repr, DecidableEq

/-! ## Denotation into verified host syntax -/

/-- Host term denoted by an IR term (`ℚ`-literal ↦ its real value). -/
def ITerm.toHost {n : ℕ} : ITerm n → Term (Var n)
  | .var v     => .var v
  | .rat q     => .const (q : ℝ)
  | .bin op a b => .binop op a.toHost b.toHost

/-- Host formula denoted by an IR formula. -/
def IForm.toHost {n : ℕ} : IForm n → Formula (Var n)
  | .tt        => .tt
  | .cmp op a b => .cmp op a.toHost b.toHost
  | .neg f     => .neg f.toHost
  | .and a b   => .and a.toHost b.toHost

/-! ## IR mirror of the verified differentiation / Lie derivative -/

/-- IR mirror of `tderiv`. -/
def ITerm.itderiv {n : ℕ} : ITerm n → Var n → ITerm n
  | .var y,        x => if y = x then .rat 1 else .rat 0
  | .rat _,        _ => .rat 0
  | .bin .add a b, x => .bin .add (a.itderiv x) (b.itderiv x)
  | .bin .sub a b, x => .bin .sub (a.itderiv x) (b.itderiv x)
  | .bin .mul a b, x => .bin .add (.bin .mul (a.itderiv x) b) (.bin .mul a (b.itderiv x))

/-- IR mirror of `sumTerm`. -/
def isumTerm {n : ℕ} : List (ITerm n) → ITerm n
  | []      => .rat 0
  | t :: ts => .bin .add t (isumTerm ts)

/-- IR mirror of `lieDeriv`. -/
def ilieDeriv {n : ℕ} (g : ITerm n) (fL fR : Fin n → ITerm n) (lam : ITerm n) : ITerm n :=
  isumTerm ((List.finRange n).map (fun i =>
    ITerm.bin .add
      (ITerm.bin .mul (g.itderiv (Lv i)) (fL i))
      (ITerm.bin .mul (g.itderiv (Rv i)) (ITerm.bin .mul lam (fR i)))))

/-- IR mirror of `flowQuery`: `domain ∧ ġ > 0`. -/
def iflowQuery {n : ℕ} (g : ITerm n) (fL fR : Fin n → ITerm n) (lam : ITerm n)
    (domain : IForm n) : IForm n :=
  IForm.and domain (IForm.cmp .gt (ilieDeriv g fL fR lam) (.rat 0))

/-! ## Bridge lemmas — the mirror denotes the verified object -/

@[simp] theorem itderiv_toHost {n : ℕ} (e : ITerm n) (x : Var n) :
    (e.itderiv x).toHost = tderiv e.toHost x := by
  induction e with
  | var y =>
    by_cases h : y = x <;> simp [ITerm.itderiv, tderiv, ITerm.toHost, h]
  | rat q => simp [ITerm.itderiv, tderiv, ITerm.toHost]
  | bin op a b iha ihb =>
    cases op <;> simp [ITerm.itderiv, tderiv, ITerm.toHost, iha, ihb]

theorem isumTerm_toHost {n : ℕ} (ts : List (ITerm n)) :
    (isumTerm ts).toHost = sumTerm (ts.map ITerm.toHost) := by
  induction ts with
  | nil => simp [isumTerm, sumTerm, ITerm.toHost]
  | cons a t ih => simp [isumTerm, sumTerm, ITerm.toHost, ih]

theorem ilieDeriv_toHost {n : ℕ} (g : ITerm n) (fL fR : Fin n → ITerm n) (lam : ITerm n) :
    (ilieDeriv g fL fR lam).toHost
      = lieDeriv g.toHost (fun i => (fL i).toHost) (fun i => (fR i).toHost) lam.toHost := by
  simp only [ilieDeriv, lieDeriv, isumTerm_toHost, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [ITerm.toHost, itderiv_toHost]

theorem iflowQuery_toHost {n : ℕ} (g : ITerm n) (fL fR : Fin n → ITerm n) (lam : ITerm n)
    (domain : IForm n) :
    (iflowQuery g fL fR lam domain).toHost
      = flowQuery ⟨g.toHost, (fun i => (fL i).toHost), (fun i => (fR i).toHost),
          lam.toHost, domain.toHost⟩ := by
  simp [iflowQuery, flowQuery, IForm.toHost, ITerm.toHost, ilieDeriv_toHost]

/-! ## Printer -/

def AOp.sym : AOp → String
  | .add => "+" | .sub => "-" | .mul => "*"

/-- Exact SMT-LIB numeral for a rational (avoids decimal ambiguity). -/
def ratToSmt (q : ℚ) : String :=
  let n := if q.num < 0 then s!"(- {-q.num})" else s!"{q.num}"
  if q.den == 1 then n else s!"(/ {n} {q.den})"

/-- SMT-LIB name for a joint variable, given per-coordinate names. -/
def varName {n : ℕ} (coord : Fin n → String) : Var n → String
  | (Side.L, i) => "L_" ++ coord i
  | (Side.R, i) => "R_" ++ coord i
  | (Side.Aux, i) => "A_" ++ coord i

def ITerm.toSmt {n : ℕ} (coord : Fin n → String) : ITerm n → String
  | .var v      => varName coord v
  | .rat q      => ratToSmt q
  | .bin op a b => s!"({AOp.sym op} {a.toSmt coord} {b.toSmt coord})"

def IForm.toSmt {n : ℕ} (coord : Fin n → String) : IForm n → String
  | .tt         => "true"
  | .cmp op a b =>
      let l := a.toSmt coord
      let r := b.toSmt coord
      match op with
      | .eq => s!"(= {l} {r})"
      | .ne => s!"(not (= {l} {r}))"
      | .lt => s!"(< {l} {r})"
      | .le => s!"(<= {l} {r})"
      | .gt => s!"(> {l} {r})"
      | .ge => s!"(>= {l} {r})"
  | .neg f      => s!"(not {f.toSmt coord})"
  | .and a b    => s!"(and {a.toSmt coord} {b.toSmt coord})"

/-- Full SMT-LIB script over the whole joint variable space. Declares every
`Side × Fin n` variable, asserts the query, `check-sat`. -/
def IForm.toScript {n : ℕ} (coord : Fin n → String) (f : IForm n) : String :=
  let vs : List (Var n) :=
    (List.finRange n).map (fun i => (Side.L, i)) ++ (List.finRange n).map (fun i => (Side.R, i))
  let decls := vs.map (fun v => s!"(declare-fun {varName coord v} () Real)")
  let body := String.intercalate "\n" decls
  s!"(set-logic QF_NRA)\n{body}\n(assert {f.toSmt coord})\n(check-sat)\n"

end RelCertifier
