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
  deriving Repr, Inhabited

inductive PForm where
  | tt  : PForm
  | cmp : String → PExpr → PExpr → PForm
  | and : PForm → PForm → PForm
  | or  : PForm → PForm → PForm
  | not : PForm → PForm
  deriving Repr, Inhabited

structure PMode where
  name   : String
  odes   : List (String × PExpr)
  guard  : PForm
  evolve : PForm
  next   : List String
  deriving Repr, Inhabited

structure PSystem where
  stateVars : List String
  epsilon   : String
  modes     : List PMode
  deriving Repr, Inhabited

structure PProblem where
  name       : String
  lambdaMin  : String
  lambdaMax  : String
  L          : PSystem
  R          : PSystem
  invariants : List (String × PForm)
  deriving Repr, Inhabited

/-! ## Lexing -/

def stripComment (s : String) : String := tr ((s.splitOn "#").headD "")

/-- Project a relational token `x[l]`/`x[r]` to `L_x`/`R_x`; else identity. -/
def normVar (t : String) : String :=
  if t.endsWith "[l]" then "L_" ++ (drr t 3)
  else if t.endsWith "[r]" then "R_" ++ (drr t 3)
  else if t.endsWith "[left]" then "L_" ++ (drr t 6)
  else if t.endsWith "[right]" then "R_" ++ (drr t 7)
  else t

/-- Tokenize: separate parens, split on whitespace. -/
def tokenize (s : String) : List String :=
  let s := s.replace "(" " ( " |>.replace ")" " ) "
  (s.splitOn " ").filterMap (fun t => let t := tr t; if t.isEmpty then none else some t)

def isNumTok (t : String) : Bool :=
  (t.data.headD 'a').isDigit || ((t.data.headD 'a') == '.') ||
  (t.startsWith "-" && ((t.data.getD 1 'a').isDigit || (t.data.getD 1 'a') == '.'))

def atom (t : String) : PExpr :=
  if isNumTok t then PExpr.num t else PExpr.var (normVar t)

/-! ## smt2 prefix parser -/

mutual
partial def parseSExpr : List String → Option (PExpr × List String)
  | [] => none
  | "(" :: op :: rest =>
      match parseSArgs rest with
      | some (args, rest') =>
          let e := match op, args with
            | "-", [a]     => PExpr.neg a
            | _,   a :: as => as.foldl (fun acc b => PExpr.bin op acc b) a
            | _,   []      => PExpr.num "0"
          some (e, rest')
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
    (parseSExpr (tokenize (dr s 5))).map Prod.fst
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
        | some ([], rest') => some (PForm.tt, rest')
        | none => none
      else if op == "not" then
        (parseSForm rest).map (fun (f, r) => (PForm.not f, r))
      else
        match parseSExpr rest with
        | some (a, r1) =>
            match parseSExpr r1 with
            | some (b, ")" :: r2) => some (PForm.cmp op a b, r2)
            | _ => none
        | none => none
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
  else if s.startsWith "smt2:" then (parseSForm (tokenize (dr s 5))).map Prod.fst
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

/-! ## Section reader + assembly -/

/-- Read `[section]` blocks into `(name, [(key,value)])`. -/
def readSections (text : String) : List (String × List (String × String)) := Id.run do
  let mut secs : List (String × List (String × String)) := []
  let mut cur : String := ""
  let mut kvs : List (String × String) := []
  for raw in (text.splitOn "\n") do
    let line := stripComment raw
    if line.isEmpty then continue
    if line.startsWith "[" && line.endsWith "]" then
      if !cur.isEmpty then secs := secs ++ [(cur, kvs)]
      cur := tr (drr (dr line 1) 1)
      kvs := []
    else match line.splitOn "=" with
      | k :: rest => kvs := kvs ++ [(tr k, tr (String.intercalate "=" rest))]
      | [] => pure ()
  if !cur.isEmpty then secs := secs ++ [(cur, kvs)]
  return secs

def secGet (kvs : List (String × String)) (k : String) : Option String :=
  (kvs.find? (fun p => p.1 == k)).map Prod.snd

/-- Parse a `[x, y, z]` list literal. -/
def parseList (s : String) : List String :=
  let s := tr s
  let s := if s.startsWith "[" then dr s 1 else s
  let s := if s.endsWith "]" then drr s 1 else s
  (s.splitOn ",").filterMap (fun t => let t := tr t; if t.isEmpty then none else some t)

/-- Parse a mode section body given its `qName`. -/
def parseMode (name : String) (kvs : List (String × String)) : Option PMode := do
  let odeStr := (secGet kvs "ode").getD ""
  -- ode = "v' = smt2:...;" possibly multiple ';'-separated
  let odes := (odeStr.splitOn ";").filterMap (fun eq =>
    let eq := tr eq
    if eq.isEmpty then none
    else match eq.splitOn "=" with
      | lhs :: rest =>
          let v := tr (drr (tr lhs) 1)   -- strip trailing '
          match parseExpr (String.intercalate "=" rest) with
          | some e => some (v, e)
          | none => none
      | [] => none)
  let guard ← parseFormula ((secGet kvs "guard").getD "")
  let evolve ← parseFormula ((secGet kvs "evolve").getD "")
  some { name := name, odes := odes, guard := guard, evolve := evolve,
         next := parseList ((secGet kvs "next").getD "[]") }

/-- Assemble the full problem from sections. -/
def assemble (secs : List (String × List (String × String))) : Option PProblem := do
  let find (n : String) := (secs.find? (fun p => p.1 == n)).map Prod.snd
  let prob ← find "problem"
  let lsys ← find "Lsys"
  let rsys ← find "Rsys"
  let modesOf (sysName : String) : List PMode :=
    secs.filterMap (fun (nm, kvs) =>
      if nm.startsWith (sysName ++ ".mode.") then
        parseMode (dr nm (sysName.length + 6)) kvs
      else none)
  let invs : List (String × PForm) :=
    match find "relational_invariant" with
    | some kvs => kvs.filterMap (fun (k, v) => (parseFormula v).map (fun f => (k, f)))
    | none => []
  some {
    name := (secGet prob "name").getD "?"
    lambdaMin := (secGet prob "lambda_min").getD "1.0"
    lambdaMax := (secGet prob "lambda_max").getD "1.0"
    L := { stateVars := parseList ((secGet lsys "state_vars").getD "[]")
           epsilon := (secGet lsys "epsilon").getD "1.0", modes := modesOf "Lsys" }
    R := { stateVars := parseList ((secGet rsys "state_vars").getD "[]")
           epsilon := (secGet rsys "epsilon").getD "1.0", modes := modesOf "Rsys" }
    invariants := invs }

def parseProblem (text : String) : Option PProblem := assemble (readSections text)

end RelCertifier.Parse
