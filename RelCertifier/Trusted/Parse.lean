/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# input.txt parser — TRUSTED IO plumbing (Stage-4 runner front-end)

Parses the benchmark `input.txt` (INI sections + infix/`smt2:` expressions) into a
string-keyed model IR (`PProblem`). A later lowering pass indexes the variables into
the verified joint space `Var n` and builds the Stage-1/2 obligations, so emitted Z3
queries are pinned to the verified `lieDeriv`/`flowQuery`. The parser is untrusted
plumbing (like the SMT printer): a parse failure ⟹ the benchmark is reported UNPARSED,
never silently certified.

Grammar handled: space-separated infix and `smt2:` prefix expressions; relational
projections `x[l]`/`x[r]` ↦ `L_x`/`R_x`. Tightly-packed infix (no spaces around `*`) and
disjunctive guards are out of scope (reported unparsed).

STRICTNESS: the parser REJECTS, never weakens. Every malformed or missing piece is a hard
error carrying its location: unparsable invariant lines / modes / ode equations, missing
required keys (`guard`, `evolve`, `next`, `ode`, `name`, `lambda_min`, `lambda_max`,
`state_vars`, `epsilon`), duplicate keys or sections, junk lines, unknown operators,
empty-argument s-expressions, malformed numerals. Assembly additionally validates: mode
names unique; every `next` entry resolves to a declared mode of the same system; the ode
left-hand sides cover the declared `state_vars` exactly (each variable exactly once);
variables used in odes/guards/evolves are declared in their system; invariant formulas use
only projected `x[l]`/`x[r]` variables declared on the respective side. The previous
lenient behavior (drop what fails to parse, default what is missing) could silently
certify a WEAKER reading of the file than the human sees — strictness removes that route.
-/
namespace RelCertifier.Parse

/-- String-returning slice helpers (Lean 4.31 `drop`/`dropRight`/`trim` yield `String.Slice`). -/
def tr (s : String) : String := s.trimAscii.toString
def dr (s : String) (n : Nat) : String := (s.drop n).toString
def drr (s : String) (n : Nat) : String := s.dropRight n

/-! ## String-keyed model IR -/

inductive PExpr where
  | var : String → PExpr
  | num : String → PExpr
  | bin : String → PExpr → PExpr → PExpr
  | neg : PExpr → PExpr
  deriving Repr, Inhabited, DecidableEq

inductive PForm where
  | tt  : PForm
  | cmp : String → PExpr → PExpr → PForm
  | and : PForm → PForm → PForm
  | or  : PForm → PForm → PForm
  | not : PForm → PForm
  deriving Repr, Inhabited, DecidableEq

structure PMode where
  name   : String
  odes   : List (String × PExpr)
  guard  : PForm
  evolve : PForm
  next   : List String
  deriving Repr, Inhabited, DecidableEq

structure PSystem where
  stateVars : List String
  epsilon   : String
  modes     : List PMode
  deriving Repr, Inhabited, DecidableEq

structure PProblem where
  name       : String
  lambdaMin  : String
  lambdaMax  : String
  L          : PSystem
  R          : PSystem
  invariants : List (String × PForm)
  deriving Repr, Inhabited, DecidableEq

/-! ## Lexing -/

def stripComment (s : String) : String := tr ((s.splitOn "#").headD "")

/-- Project a relational token `x[l]`/`x[r]` to `L_x`/`R_x`; else identity. -/
def normVar (t : String) : String :=
  if t.endsWith "[l]" then "L_" ++ (drr t 3)
  else if t.endsWith "[r]" then "R_" ++ (drr t 3)
  else if t.endsWith "[left]" then "L_" ++ (drr t 6)
  else if t.endsWith "[right]" then "R_" ++ (drr t 7)
  else t

def isNumTok (t : String) : Bool :=
  (t.data.headD 'a').isDigit || ((t.data.headD 'a') == '.') ||
  (t.startsWith "-" && ((t.data.getD 1 'a').isDigit || (t.data.getD 1 'a') == '.'))

/-- After splitting operators, `-`/`+` in **operand** position (following an operator or
comparator, or at the start) glued to a following number is a signed literal — merge them
back. NOT after `(` (the smt operator slot, where `(- a b)` is binary minus) nor after a
value (binary). Fixes `(* -1 psi)` → `-1` while keeping `(- 0.30 v)` as binary. -/
def signMergePos (prev : Option String) : Bool :=
  match prev with
  | none   => true
  | some p => ["*", "/", "+", "-", "<=", ">=", "<", ">", "="].contains p

partial def mergeSigns : Option String → List String → List String
  | _, [] => []
  | prev, a :: rest =>
      if (a == "-" || a == "+") && signMergePos prev then
        match rest with
        | b :: rest2 =>
            if isNumTok b && !b.startsWith "-" then
              let m := if a == "-" then "-" ++ b else b
              m :: mergeSigns (some m) rest2
            else a :: mergeSigns (some a) rest
        | [] => [a]
      else a :: mergeSigns (some a) rest

/-- Tokenize: separate parens and operators (so tightly-packed infix like
`1.125*e[l]*e[l]` — quadratic/product invariants — tokenizes), split on whitespace, then
re-merge signed numeric literals (`mergeSigns`). `[l]`/`[r]` brackets stay attached. -/
def tokenize (s : String) : List String :=
  let s := s.replace "(" " ( " |>.replace ")" " ) "
    |>.replace "*" " * " |>.replace "/" " / " |>.replace "+" " + " |>.replace "-" " - "
  mergeSigns none ((s.splitOn " ").filterMap (fun t => let t := tr t; if t.isEmpty then none else some t))

def atom (t : String) : PExpr :=
  if isNumTok t then PExpr.num t else PExpr.var (normVar t)

/-! ## smt2 prefix parser -/

def exprOps : List String := ["+", "-", "*", "/"]
def cmpOps : List String := ["<=", ">=", "<", ">", "="]

mutual
partial def parseSExpr : List String → Option (PExpr × List String)
  | [] => none
  | "(" :: op :: rest =>
      match parseSArgs rest with
      | some (args, rest') =>
          -- strict: known operators only; unary `-`; otherwise at least two arguments
          -- (no empty-argument default, no silent op-dropping on `(op x)`)
          match op, args with
          | "-", [a] => some (PExpr.neg a, rest')
          | _, a :: b :: as =>
              if exprOps.contains op then
                some ((b :: as).foldl (fun acc c => PExpr.bin op acc c) a, rest')
              else none
          | _, _ => none
      | none => none
  | ")" :: _ => none
  | t :: rest => some (atom t, rest)

partial def parseSArgs : List String → Option (List PExpr × List String)
  | ")" :: rest => some ([], rest)
  | [] => none
  | toks =>
      match parseSExpr toks with
      | some (e, rest) => (parseSArgs rest).map (fun (es, r) => (e :: es, r))
      | none => none
end

/-! ## Infix parser (left-assoc: +,- then *,/ then atom/paren/unary-) -/

/-- Index of the LAST top-level (depth 0) separator token, if any (for left-assoc). -/
def lastTopSep (toks : List String) (seps : List String) : Option Nat := Id.run do
  let mut depth := 0
  let mut best : Option Nat := none
  let mut i := 0
  for t in toks do
    if t == "(" then depth := depth + 1
    else if t == ")" then depth := depth - 1
    else if depth == 0 && seps.contains t && i > 0 then best := some i
    i := i + 1
  return best

partial def parseInfix (toks : List String) : Option PExpr :=
  match lastTopSep toks ["+","-"] with
  | some i =>
      match parseInfix (toks.take i), parseInfix (toks.drop (i+1)) with
      | some a, some b => some (PExpr.bin (toks.getD i "+") a b)
      | _, _ => none
  | none =>
    match lastTopSep toks ["*","/"] with
    | some i =>
        match parseInfix (toks.take i), parseInfix (toks.drop (i+1)) with
        | some a, some b => some (PExpr.bin (toks.getD i "*") a b)
        | _, _ => none
    | none =>
      match toks with
      | ["-", t] => some (PExpr.neg (atom t))
      | "-" :: rest => (parseInfix rest).map PExpr.neg
      | "(" :: rest => parseInfix rest.dropLast
      | [t] => some (atom t)
      | _ => none

def parseExpr (s : String) : Option PExpr :=
  let s := tr s
  if s.startsWith "smt2:" then
    -- STRICT (2026-07-19): reject trailing tokens (same discard pattern as
    -- the formula branch; see there).
    match parseSExpr (tokenize (dr s 5)) with
    | some (e, []) => some e
    | _ => none
  else parseInfix (tokenize s)

/-! ## Formula parser -/

/-- Split token list at the last top-level occurrence of a separator. -/
def splitLastTop (toks : List String) (seps : List String) :
    Option (List String × String × List String) :=
  match lastTopSep toks seps with
  | some i => some (toks.take i, toks.getD i "", toks.drop (i+1))
  | none => none

mutual
partial def parseSForm : List String → Option (PForm × List String)
  | "(" :: op :: rest =>
      if op == "and" || op == "or" then
        match parseSFormArgs rest with
        | some (f :: fs, rest') =>
            some (fs.foldl (fun acc g => if op == "and" then PForm.and acc g else PForm.or acc g) f, rest')
        | some ([], _) => none   -- strict: `(and)` is malformed, not ⊤
        | none => none
      else if op == "not" then
        (parseSForm rest).map (fun (f, r) => (PForm.not f, r))
      else if cmpOps.contains op then
        match parseSExpr rest with
        | some (a, r1) =>
            match parseSExpr r1 with
            | some (b, ")" :: r2) => some (PForm.cmp op a b, r2)
            | _ => none
        | none => none
      else none   -- strict: unknown head operator
  | _ => none
partial def parseSFormArgs : List String → Option (List PForm × List String)
  | ")" :: rest => some ([], rest)
  | toks =>
      match parseSForm toks with
      | some (f, rest) => (parseSFormArgs rest).map (fun (fs, r) => (f :: fs, r))
      | none => none
end

partial def parseFormula (s : String) : Option PForm :=
  let s := tr s
  if s.isEmpty then some PForm.tt
  else if s.startsWith "smt2:" then
    -- STRICT (2026-07-19): a trailing remainder after the s-expression was
    -- previously DISCARDED, silently weakening multi-conjunct lines of the
    -- form `smt2:(...) and smt2:(...)` to their first conjunct (found via a
    -- false CERTIFIED on a synthesized two-sided band; see relSynth
    -- results/bug/). Reject instead — never weaken. Multi-conjunct smt2
    -- lines must use a single `smt2:(and ...)`.
    match parseSForm (tokenize (dr s 5)) with
    | some (f, []) => some f
    | _ => none
  else
    let toks := tokenize s
    match splitLastTop toks ["and"] with
    | some (a, _, b) =>
        match parseFormula (String.intercalate " " a), parseFormula (String.intercalate " " b) with
        | some fa, some fb => some (PForm.and fa fb)
        | _, _ => none
    | none =>
      match splitLastTop toks ["or"] with
      | some (a, _, b) =>
          match parseFormula (String.intercalate " " a), parseFormula (String.intercalate " " b) with
          | some fa, some fb => some (PForm.or fa fb)
          | _, _ => none
      | none =>
        match splitLastTop toks ["<=",">=","<",">","="] with
        | some (a, op, b) =>
            match parseInfix a, parseInfix b with
            | some ea, some eb => some (PForm.cmp op ea eb)
            | _, _ => none
        | none => none

/-! ## Section reader + assembly (STRICT: `Except String`, reject-never-weaken) -/

/-- Read `[section]` blocks into `(name, [(key,value)])`. Strict: content before any
section header, lines without `=`, duplicate keys within a section, and duplicate
section names are all hard errors. -/
def readSectionsE (text : String) : Except String (List (String × List (String × String))) := Id.run do
  let mut secs : List (String × List (String × String)) := []
  let mut cur : String := ""
  let mut kvs : List (String × String) := []
  let mut lineNo := 0
  for raw in (text.splitOn "\n") do
    lineNo := lineNo + 1
    let line := stripComment raw
    if line.isEmpty then continue
    if line.startsWith "[" && line.endsWith "]" then
      if !cur.isEmpty then secs := secs ++ [(cur, kvs)]
      cur := tr (drr (dr line 1) 1)
      if cur.isEmpty then return .error s!"line {lineNo}: empty section name"
      if secs.any (fun p => p.1 == cur) then
        return .error s!"line {lineNo}: duplicate section [{cur}]"
      kvs := []
    else if !(line.splitOn "=").length.blt 2 then
      match line.splitOn "=" with
      | k :: rest =>
          let key := tr k
          if cur.isEmpty then
            return .error s!"line {lineNo}: key '{key}' before any [section]"
          if key.isEmpty then
            return .error s!"line {lineNo}: empty key"
          if kvs.any (fun p => p.1 == key) then
            return .error s!"line {lineNo}: duplicate key '{key}' in [{cur}]"
          kvs := kvs ++ [(key, tr (String.intercalate "=" rest))]
      | [] => pure ()
    else
      return .error s!"line {lineNo}: not a section header or key=value: '{line}'"
  if !cur.isEmpty then secs := secs ++ [(cur, kvs)]
  return .ok secs

def secGet (kvs : List (String × String)) (k : String) : Option String :=
  (kvs.find? (fun p => p.1 == k)).map Prod.snd

/-- Strict required-key lookup. -/
def secNeed (sec : String) (kvs : List (String × String)) (k : String) :
    Except String String :=
  match secGet kvs k with
  | some v => if (tr v).isEmpty then .error s!"[{sec}]: key '{k}' is empty" else .ok v
  | none => .error s!"[{sec}]: missing required key '{k}'"

/-- Parse a `[x, y, z]` list literal. -/
def parseList (s : String) : List String :=
  let s := tr s
  let s := if s.startsWith "[" then dr s 1 else s
  let s := if s.endsWith "]" then drr s 1 else s
  (s.splitOn ",").filterMap (fun t => let t := tr t; if t.isEmpty then none else some t)

/-- Variables of an expression / formula (for scope validation). -/
partial def exprVars : PExpr → List String
  | .var v => [v]
  | .num _ => []
  | .neg a => exprVars a
  | .bin _ a b => exprVars a ++ exprVars b

partial def formVars : PForm → List String
  | .tt => []
  | .cmp _ a b => exprVars a ++ exprVars b
  | .and a b | .or a b => formVars a ++ formVars b
  | .not a => formVars a

/-- Numeric literals of an expression / formula (for numeral validation). -/
partial def exprNums : PExpr → List String
  | .var _ => []
  | .num c => [c]
  | .neg a => exprNums a
  | .bin _ a b => exprNums a ++ exprNums b

partial def formNums : PForm → List String
  | .tt => []
  | .cmp _ a b => exprNums a ++ exprNums b
  | .and a b | .or a b => formNums a ++ formNums b
  | .not a => formNums a

/-- A well-formed decimal numeral: optional `-`, digits, at most one `.`, digits. -/
def numOk (c : String) : Bool :=
  let c := if c.startsWith "-" then dr c 1 else c
  let parts := c.splitOn "."
  !c.isEmpty && parts.length ≤ 2 &&
    parts.all (fun p => p.data.all Char.isDigit) &&
    (parts.headD "").length > 0

/-- Parse a mode section body, strictly: `ode`, `guard`, `evolve`, `next` required; every
`;`-separated ode equation must have a primed LHS and a parsable RHS; a `strengthen`
key is rejected outright (the field was removed; the checked-cut channel derives its
candidates from the guard conjuncts only). -/
def parseModeE (sec : String) (name : String) (kvs : List (String × String)) :
    Except String PMode := do
  let odeStr ← secNeed sec kvs "ode"
  let mut odes : List (String × PExpr) := []
  for eq in odeStr.splitOn ";" do
    let eq := tr eq
    if eq.isEmpty then continue
    match eq.splitOn "=" with
    | lhs :: rest@(_ :: _) =>
        let lhs := tr lhs
        if !lhs.endsWith "'" then
          throw s!"[{sec}]: ode LHS '{lhs}' lacks prime"
        let v := tr (drr lhs 1)
        if v.isEmpty then throw s!"[{sec}]: ode with empty variable"
        match parseExpr (String.intercalate "=" rest) with
        | some e => odes := odes ++ [(v, e)]
        | none => throw s!"[{sec}]: unparsable ode RHS for '{v}''"
    | _ => throw s!"[{sec}]: ode equation without '=': '{eq}'"
  let guardS ← secNeed sec kvs "guard"
  let guard ← match parseFormula guardS with
    | some f => pure f
    | none => throw s!"[{sec}]: unparsable guard"
  let evolveS ← secNeed sec kvs "evolve"
  let evolve ← match parseFormula evolveS with
    | some f => pure f
    | none => throw s!"[{sec}]: unparsable evolve"
  let nextS ← secNeed sec kvs "next"
  if (secGet kvs "strengthen").isSome then
    throw s!"[{sec}]: 'strengthen' is no longer supported (the checked-cut channel derives its candidates from the guard conjuncts only)"
  return { name := name, odes := odes, guard := guard, evolve := evolve,
           next := parseList nextS }

/-- Scope/numeral validation for one system: mode names unique; `next` resolves; ode LHS
cover `state_vars` exactly; variables in odes/guard/evolve are declared; numerals well
formed. -/
def validateSystem (sysName : String) (sys : PSystem) : Except String Unit := do
  if sys.stateVars.isEmpty then throw s!"[{sysName}]: empty state_vars"
  if sys.modes.isEmpty then throw s!"[{sysName}]: no modes"
  let names := sys.modes.map (·.name)
  if names.eraseDups.length != names.length then
    throw s!"[{sysName}]: duplicate mode names"
  for m in sys.modes do
    let sec := s!"{sysName}.mode.{m.name}"
    let lhs := m.odes.map Prod.fst
    if lhs.eraseDups.length != lhs.length then
      throw s!"[{sec}]: duplicate ode for a variable"
    for v in sys.stateVars do
      if !lhs.contains v then throw s!"[{sec}]: no ode for state var '{v}'"
    for v in lhs do
      if !sys.stateVars.contains v then throw s!"[{sec}]: ode for undeclared '{v}'"
    for q in m.next do
      if !names.contains q then throw s!"[{sec}]: next '{q}' is not a mode of {sysName}"
    let scopeOk (v : String) : Bool := sys.stateVars.contains v
    for (v, e) in m.odes do
      for u in exprVars e do
        if !scopeOk u then throw s!"[{sec}]: ode of '{v}' uses undeclared '{u}'"
    for u in formVars m.guard do
      if !scopeOk u then throw s!"[{sec}]: guard uses undeclared '{u}'"
    for u in formVars m.evolve do
      if !scopeOk u then throw s!"[{sec}]: evolve uses undeclared '{u}'"
    let nums := (m.odes.map (fun p => exprNums p.2)).flatten
      ++ formNums m.guard ++ formNums m.evolve
    for c in nums do
      if !numOk c then throw s!"[{sec}]: malformed numeral '{c}'"

/-- Assemble the full problem from sections, strictly. -/
def assembleE (secs : List (String × List (String × String))) : Except String PProblem := do
  let find (n : String) := (secs.find? (fun p => p.1 == n)).map Prod.snd
  let prob ← match find "problem" with
    | some kvs => pure kvs | none => throw "missing [problem] section"
  let lsys ← match find "Lsys" with
    | some kvs => pure kvs | none => throw "missing [Lsys] section"
  let rsys ← match find "Rsys" with
    | some kvs => pure kvs | none => throw "missing [Rsys] section"
  let modesOfE (sysName : String) : Except String (List PMode) := do
    let mut out : List PMode := []
    for (nm, kvs) in secs do
      if nm.startsWith (sysName ++ ".mode.") then
        out := out ++ [← parseModeE nm (dr nm (sysName.length + 6)) kvs]
    return out
  let name ← secNeed "problem" prob "name"
  let lambdaMin ← secNeed "problem" prob "lambda_min"
  let lambdaMax ← secNeed "problem" prob "lambda_max"
  if !numOk lambdaMin then throw s!"[problem]: malformed lambda_min '{lambdaMin}'"
  if !numOk lambdaMax then throw s!"[problem]: malformed lambda_max '{lambdaMax}'"
  let lVars ← secNeed "Lsys" lsys "state_vars"
  let rVars ← secNeed "Rsys" rsys "state_vars"
  let lEps ← secNeed "Lsys" lsys "epsilon"
  let rEps ← secNeed "Rsys" rsys "epsilon"
  if !numOk lEps then throw s!"[Lsys]: malformed epsilon '{lEps}'"
  if !numOk rEps then throw s!"[Rsys]: malformed epsilon '{rEps}'"
  let L : PSystem := { stateVars := parseList lVars, epsilon := lEps,
                       modes := ← modesOfE "Lsys" }
  let R : PSystem := { stateVars := parseList rVars, epsilon := rEps,
                       modes := ← modesOfE "Rsys" }
  validateSystem "Lsys" L
  validateSystem "Rsys" R
  let invKvs ← match find "relational_invariant" with
    | some kvs => pure kvs
    | none => throw "missing [relational_invariant] section"
  let mut invs : List (String × PForm) := []
  for (k, v) in invKvs do
    match parseFormula v with
    | some f => invs := invs ++ [(k, f)]
    | none => throw s!"[relational_invariant]: unparsable line for '{k}'"
  let modeNames := (L.modes.map (·.name)) ++ (R.modes.map (·.name))
  for (k, f) in invs do
    if !modeNames.contains k then
      throw s!"[relational_invariant]: '{k}' is not a mode name"
    for u in formVars f do
      if u.startsWith "L_" then
        if !L.stateVars.contains (dr u 2) then
          throw s!"[relational_invariant] {k}: '{dr u 2}[l]' not an Lsys state var"
      else if u.startsWith "R_" then
        if !R.stateVars.contains (dr u 2) then
          throw s!"[relational_invariant] {k}: '{dr u 2}[r]' not an Rsys state var"
      else
        throw s!"[relational_invariant] {k}: unprojected variable '{u}' (use x[l]/x[r])"
    for c in formNums f do
      if !numOk c then throw s!"[relational_invariant] {k}: malformed numeral '{c}'"
  return { name := name, lambdaMin := lambdaMin, lambdaMax := lambdaMax,
           L := L, R := R, invariants := invs }

/-- Strict entry point: a parse failure carries its reason. -/
def parseProblemE (text : String) : Except String PProblem := do
  assembleE (← readSectionsE text)

/-- Option-valued compatibility wrapper (verdict-level callers). -/
def parseProblem (text : String) : Option PProblem := (parseProblemE text).toOption

end RelCertifier.Parse
