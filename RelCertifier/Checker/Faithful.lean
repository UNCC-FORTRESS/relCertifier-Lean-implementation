/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `Faithful` — kernel-checked instance ↔ benchmark identity (seam #1 closure)

**Status.** Part of the settling / `Faithful` route (per-benchmark settling, terrain and
affine models of the legacy suite, kernel-certified against the parsed IR). Its
per-benchmark batteries (`SettlingInstances`, `TerrainInstances`, `AffineInstances`,
`FaithfulCerts`, `RealInstances`) were retired with the legacy suite (git history); the
suite_v2 theorems use the modal chain instead. The generic definitions and lemmas stay
compiled as part of the soundness development.

The settling/terrain/affine instances are transcriptions of benchmark R sides under
per-coordinate value scales and a time rescale. `Faithful` makes that identity a
DECIDABLE fact the kernel checks by `rfl`, against the PARSER-EMITTED IR literal
(`BenchIR.lean`, produced by `relcert --emit-ir` — the same parser that feeds the
certifier's queries, so both halves of the pipeline see one model). The runtime battery
re-parses each benchmark file and compares it to the embedded literal with the derived
`DecidableEq`, so a drifted literal fails loudly.

Conventions verified (exact ℚ, mirroring the retired `scripts/transcription_audit.py`):
with `u = (ε_R/λ)/dtQ` (real seconds per stored time unit) and `σᵢ` the value scales —

  frozen      f = 0
  constRate c f = A          with c = A·σᵢ·u
  contract    f = A + B·x    with B < 0, k = −B·u,  c = (A/−B)·σᵢ
  contractQ   likewise with k = kn/kd
  driven j    f = C·x_j      with C·σᵢ·u = σⱼ
  chase j k   f = C·x_j+B·x  with k = −B·u, C·σᵢ·u = σⱼ
  riccati b a f = A + B·x²   with b = A·σᵢ·u, a/10⁶ = −B·u/σᵢ
  pairSym j c h  f = A+B·x+C·x_j with −B·u = 1, h/1000 = C·u·σᵢ/σⱼ, c = (A/−B)·σᵢ
  drivenDamp  f = C·x_j·(1 − Σ (an/ad)·(x_d/σ_d)²·…) — the x_j coefficient obeys the
              driven law and each damper coefficient obeys (an/ad)·σ_d² = −coeff/C

plus: guard band ↔ [glo, ghi] (σ_g-scaled; terrain/affine variants below), envelope ↔
evolve per coordinate (including sidedness), succs ↔ next-minus-self as indices, inert
padding allowed (frozen + unconstrained extra coordinates), terrain sbands ↔ s-guards,
affine vtops ↔ guard tops.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Core.QFrac
import RelCertifier.Checker.AffineChecker
import RelCertifier.Checker.TerrainChecker

namespace RelCertifier
open RelCertifier.Parse

/-- Monomial: variables with exponents, kept sorted by name. -/
abbrev Mono := List (String × Nat)

/-- Pull variable `v`'s exponent out of a monomial (structural). -/
def monoExtract (v : String) : Mono → Option (Nat × Mono)
  | [] => none
  | (w, l) :: m =>
      if v == w then some (l, m)
      else (monoExtract v m).map (fun r => (r.1, (w, l) :: r.2))

/-- Multiset equality of monomials (order-insensitive, structural). -/
def monoEq : Mono → Mono → Bool
  | [], [] => true
  | [], _ => false
  | (v, k) :: a, b =>
      match monoExtract v b with
      | some (l, b') => k == l && monoEq a b'
      | none => false

def monoInsert (v : String) (k : Nat) : Mono → Mono
  | [] => [(v, k)]
  | (w, l) :: m => if v == w then (w, l + k) :: m else (w, l) :: monoInsert v k m

def monoMul : Mono → Mono → Mono
  | [], b => b
  | (v, k) :: a, b => monoMul a (monoInsert v k b)

/-- Polynomial: monomial ↦ coefficient (association list, nonzero coefficients). -/
abbrev QPoly := List (Mono × QF)

def polyInsert (m : Mono) (c : QF) : QPoly → QPoly
  | [] => if qIsZero c then [] else [(m, c)]
  | (n, d) :: p =>
      if monoEq m n then
        let e := qAdd c d
        if qIsZero e then p else (n, e) :: p
      else (n, d) :: polyInsert m c p

def polyAdd (a b : QPoly) : QPoly := b.foldl (fun acc md => polyInsert md.1 md.2 acc) a

def polyNeg (a : QPoly) : QPoly := a.map (fun p => (p.1, qNeg p.2))

def polyScale (q : QF) (a : QPoly) : QPoly :=
  if qIsZero q then [] else a.map (fun p => (p.1, qMul q p.2))

def polyMul (a b : QPoly) : QPoly :=
  a.foldl (fun acc mc =>
    polyAdd acc (b.map (fun nd => (monoMul mc.1 nd.1, qMul mc.2 nd.2)))) []

def polyConstOf (q : QF) : QPoly := if qIsZero q then [] else [([], q)]
def polyVarOf (v : String) : QPoly := [([(v, 1)], qOfInt 1)]

/-- IR expression → polynomial (division only by nonzero constants). -/
def exprPoly : PExpr → Option QPoly
  | .var v => some (polyVarOf v)
  | .num c => (parseQ c).map polyConstOf
  | .neg a => (exprPoly a).map polyNeg
  | .bin op a b => do
      let pa ← exprPoly a
      let pb ← exprPoly b
      match op with
      | "+" => return polyAdd pa pb
      | "-" => return polyAdd pa (polyNeg pb)
      | "*" => return polyMul pa pb
      | "/" =>
          match pb with
          | [([], d)] => if qIsZero d then none else return polyScale (qDiv (qOfInt 1) d) pa
          | _ => none
      | _ => none

def coeffOf (p : QPoly) (m : Mono) : QF :=
  (((p.find? (fun e => monoEq e.1 m))).map (·.2)).getD (qOfInt 0)

/-- Every monomial of `p` is one of `ms`. -/
def supportIn (p : QPoly) (ms : List Mono) : Bool :=
  p.all (fun e => ms.any (fun m => monoEq e.1 m))

/-! ## Bounds from conjunctive guard/evolve formulas -/

/-- One merge step of the `and`-fold: insert or interval-intersect entry `e`. Named (not a
lambda) so proofs can speak about it without restating the match. -/
def mergeBound (acc : List (String × Option QF × Option QF))
    (e : String × Option QF × Option QF) : List (String × Option QF × Option QF) :=
  match acc.find? (fun e2 => e2.1 == e.1) with
  | none => acc ++ [e]
  | some e0 =>
      let lo' := match e0.2.1, e.2.1 with
        | none, x => x | x, none => x
        | some x, some y => some (if qLt x y then y else x)
      let hi' := match e0.2.2, e.2.2 with
        | none, x => x | x, none => x
        | some x, some y => some (if qLt x y then x else y)
      acc.map (fun e2 => if e2.1 == e.1 then (e.1, lo', hi') else e2)

/-- Fold a conjunction of `var ⋈ const` atoms into per-variable interval bounds.
Non-conjunctive structure or non-(var,const) atoms → `none` (`Faithful` then fails). -/
def boundsOfForm : PForm → Option (List (String × Option QF × Option QF))
  | .tt => some []
  | .and a b => do
      let ba ← boundsOfForm a
      let bb ← boundsOfForm b
      return bb.foldl mergeBound ba
  | .cmp op a b =>
      match a, b with
      | .var v, .num c => do
          let q ← parseQ c
          match op with
          | ">=" | ">" => return [(v, some q, none)]
          | "<=" | "<" => return [(v, none, some q)]
          | _ => none
      | .num c, .var v => do
          let q ← parseQ c
          match op with
          | ">=" | ">" => return [(v, none, some q)]
          | "<=" | "<" => return [(v, some q, none)]
          | _ => none
      | _, _ => none
  | _ => none

def boundOf (bs : List (String × Option QF × Option QF)) (v : String) :
    Option QF × Option QF :=
  (((bs.find? (fun e => e.1 == v))).map (fun e => e.2)).getD (none, none)

/-! ## The transcription metadata: scales as DATA, not comments -/

/-- Per-instance transcription conventions. `lam` is the declared λ (`dt = ε_R/λ`);
`scales` the per-coordinate value scales (position `i` ↔ `stateVars[i]`). -/
structure TransMeta where
  lam    : QF
  scales : List QF
  deriving Repr

/-! ## Per-shape fidelity -/

/-- One coordinate's shape vs its parsed ode, under time unit `u` and scales `σ`. -/
def shapeFaithful (vs : List String) (σ : List QF) (u : QF) (i : Nat)
    (sh : CoordShape n) (p : QPoly) : Bool :=
  let v := vs.getD i ""
  let σi := σ.getD i (qOfInt 0)
  let xi : Mono := [(v, 1)]
  let x2 : Mono := [(v, 2)]
  let A := coeffOf p []
  let B := coeffOf p xi
  match sh with
  | CoordShape.frozen => p.isEmpty
  | CoordShape.constRate c =>
      supportIn p [[]] && qEq (qOfInt c) (qMul (qMul A σi) u)
  | CoordShape.contract k c =>
      supportIn p [[], xi] && qLt B (qOfInt 0) &&
      qEq (qOfInt k) (qMul (qNeg B) u) &&
      qEq (qOfInt c) (qMul (qDiv A (qNeg B)) σi)
  | CoordShape.contractQ kn kd c =>
      supportIn p [[], xi] && qLt B (qOfInt 0) && !(kd == 0) &&
      qEq (qDiv (qOfInt kn) (qOfInt kd)) (qMul (qNeg B) u) &&
      qEq (qOfInt c) (qMul (qDiv A (qNeg B)) σi)
  | CoordShape.driven j =>
      let w := vs.getD j.val ""
      let C := coeffOf p [(w, 1)]
      supportIn p [[(w, 1)]] && !(qIsZero C) &&
      qEq (qMul (qMul C σi) u) (σ.getD j.val (qOfInt 0))
  | CoordShape.chase j k =>
      let w := vs.getD j.val ""
      let C := coeffOf p [(w, 1)]
      supportIn p [xi, [(w, 1)]] && !(qIsZero C) &&
      qEq (qOfInt k) (qMul (qNeg B) u) &&
      qEq (qMul (qMul C σi) u) (σ.getD j.val (qOfInt 0))
  | CoordShape.riccati b a =>
      let Bq := coeffOf p x2
      supportIn p [[], x2] && !(qIsZero σi) &&
      qEq (qOfInt b) (qMul (qMul A σi) u) &&
      qEq (qDiv (qOfInt a) (qOfInt 1000000)) (qDiv (qMul (qNeg Bq) u) σi)
  | CoordShape.pairSym j c h =>
      let w := vs.getD j.val ""
      let C := coeffOf p [(w, 1)]
      supportIn p [[], xi, [(w, 1)]] && !(qIsZero (σ.getD j.val (qOfInt 0))) &&
      qEq (qMul (qNeg B) u) (qOfInt 1) &&
      qEq (qDiv (qOfInt h) (qOfInt 1000))
          (qDiv (qMul (qMul C u) σi) (σ.getD j.val (qOfInt 0))) &&
      qEq (qOfInt c) (qMul (qDiv A (qNeg B)) σi)
  | CoordShape.drivenDamp j dampers =>
      let w := vs.getD j.val ""
      let C := coeffOf p [(w, 1)]
      !(qIsZero C) && qEq (qMul (qMul C σi) u) (σ.getD j.val (qOfInt 0)) &&
      supportIn p ([(w, 1)] :: dampers.map (fun d =>
        monoMul [(w, 1)] [(vs.getD d.1.val "", 2)])) &&
      dampers.all (fun d =>
        let σd := σ.getD d.1.val (qOfInt 0)
        let coeff := coeffOf p (monoMul [(w, 1)] [(vs.getD d.1.val "", 2)])
        !(d.2.2 == 0) &&
        qEq (qMul (qDiv (qOfInt d.2.1) (qOfInt d.2.2)) (qMul σd σd))
            (qDiv (qNeg coeff) C))

/-! ## Envelope, guard-band, successor fidelity -/

/-- Envelope entry vs evolve bounds for one coordinate (sidedness must agree). -/
def envFaithful (σi : QF) (b : Band) (lo hi : Option QF) : Bool :=
  (match b.lo, lo with
   | none, none => true
   | some z, some q => qEq (qOfInt z) (qMul q σi)
   | _, _ => false) &&
  (match b.hi, hi with
   | none, none => true
   | some z, some q => qEq (qOfInt z) (qMul q σi)
   | _, _ => false)

/-- `succs` = `next` minus the self-loop, as indices in benchmark mode order. -/
def succsFaithful (names : List String) (self : Nat) (next : List String)
    (succs : List ℕ) : Bool :=
  let want := ((next.filterMap (fun q => names.idxOf? q)).filter (· ≠ self)).eraseDups
  succs.length == want.length &&
  want.all (fun q => succs.contains q) && succs.all (fun q => want.contains q)

/-- Mode fidelity WITHOUT the guard-band clause: odes/shapes, padding, envelope,
successors (shared by the settling/terrain/affine variants). -/
def modeCore {n : ℕ} (vs : List String) (σ : List QF) (u : QF)
    (names : List String) (self : Nat) (pm : PMode) (m : SettlingMode n)
    (env : Fin n → Band) : Bool :=
  ((List.range vs.length).all (fun i =>
    if h : i < n then
      match pm.odes.find? (fun o => o.1 == vs.getD i "") with
      | some o =>
          match exprPoly o.2 with
          | some p => shapeFaithful vs σ u i (m.shapes ⟨i, h⟩) p
          | none => false
      | none => false
    else false)) &&
  ((List.range n).all (fun i =>
    if h : i < n then
      if vs.length ≤ i then
        (match m.shapes ⟨i, h⟩ with | CoordShape.frozen => true | _ => false) &&
        (env ⟨i, h⟩).lo.isNone && (env ⟨i, h⟩).hi.isNone
      else true
    else true)) &&
  (match boundsOfForm pm.evolve with
   | none => false
   | some eb =>
       (List.range vs.length).all (fun i =>
         if h : i < n then
           let (lo, hi) := boundOf eb (vs.getD i "")
           envFaithful (σ.getD i (qOfInt 0)) (env ⟨i, h⟩) lo hi
         else false)) &&
  succsFaithful names self pm.next m.succs

/-- SETTLING band clause: the guard carries BOTH bounds on the gcoord, matching
`[glo, ghi]` under its scale. -/
def bandSettling {n : ℕ} (vs : List String) (σ : List QF) (pm : PMode)
    (m : SettlingMode n) : Bool :=
  match boundsOfForm pm.guard with
  | none => false
  | some gb =>
      let (glo, ghi) := boundOf gb (vs.getD m.gcoord.val "")
      (match glo with
       | some q => qEq (qOfInt m.glo) (qMul q (σ.getD m.gcoord.val (qOfInt 0)))
       | none => false) &&
      (match ghi with
       | some q => qEq (qOfInt m.ghi) (qMul q (σ.getD m.gcoord.val (qOfInt 0)))
       | none => false)

/-- TERRAIN band clause: where the guard bounds the gcoord (the v-caps), the band must
match it; where it does not, the band is the instance's DESIGN choice and must sit inside
the envelope. The terrain guard geometry itself lives in the s-bands (`sbandFaithful`). -/
def bandTerrain {n : ℕ} (vs : List String) (σ : List QF) (pm : PMode)
    (m : SettlingMode n) (env : Fin n → Band) : Bool :=
  match boundsOfForm pm.guard with
  | none => false
  | some gb =>
      if h : m.gcoord.val < n then
        let (glo, ghi) := boundOf gb (vs.getD m.gcoord.val "")
        let e := env ⟨m.gcoord.val, h⟩
        (match glo with
         | some q => qEq (qOfInt m.glo) (qMul q (σ.getD m.gcoord.val (qOfInt 0)))
         | none => match e.lo with
           | some z => decide (z ≤ m.glo)
           | none => true) &&
        (match ghi with
         | some q => qEq (qOfInt m.ghi) (qMul q (σ.getD m.gcoord.val (qOfInt 0)))
         | none => match e.hi with
           | some z => decide (m.ghi ≤ z)
           | none => true)
      else false

/-- TERRAIN s-band clause: `sc` names the guarded position; `slo`/`shi` are its guard
bounds under its scale (`shi = none` ↔ topless terminal segment). -/
def sbandFaithful {n : ℕ} (vs : List String) (σ : List QF) (pm : PMode)
    (sb : SBand n) : Bool :=
  match boundsOfForm pm.guard with
  | none => false
  | some gb =>
      let sv := vs.getD sb.sc.val ""
      let (lo, hi) := boundOf gb sv
      (match lo with
       | some q => qEq (qOfInt sb.slo) (qMul q (σ.getD sb.sc.val (qOfInt 0)))
       | none => false) &&
      (match sb.shi, hi with
       | none, none => true
       | some z, some q => qEq (qOfInt z) (qMul q (σ.getD sb.sc.val (qOfInt 0)))
       | _, _ => false)

/-- AFFINE band clause: guard lower bound ↔ `glo`; guard upper bound ↔ the mode's
`vtop` (`ghi` is a dummy in the affine guard map). -/
def bandAffine {n : ℕ} (vs : List String) (σ : List QF) (pm : PMode)
    (m : SettlingMode n) (top : Option ℤ) : Bool :=
  match boundsOfForm pm.guard with
  | none => false
  | some gb =>
      let (glo, ghi) := boundOf gb (vs.getD m.gcoord.val "")
      (match glo with
       | some q => qEq (qOfInt m.glo) (qMul q (σ.getD m.gcoord.val (qOfInt 0)))
       | none => false) &&
      (match top, ghi with
       | none, none => true
       | some z, some q => qEq (qOfInt z) (qMul q (σ.getD m.gcoord.val (qOfInt 0)))
       | _, _ => false)

/-- Shared frame: ε, u, lengths, per-mode core + a per-mode extra clause. -/
def faithfulFrame {n : ℕ} (P : PProblem) (mt : TransMeta) (M : SettlingModel n)
    (extra : Nat → PMode → SettlingMode n → Bool) : Bool :=
  let vs := P.R.stateVars
  let names := P.R.modes.map (·.name)
  match parseQ P.R.epsilon with
  | none => false
  | some εR =>
      !(qIsZero mt.lam) && !(M.dtQ == 0) &&
      decide (vs.length ≤ n) &&
      mt.scales.length == vs.length &&
      P.R.modes.length == M.modes.length &&
      ((List.range P.R.modes.length).all (fun q =>
        let u := qDiv (qDiv εR mt.lam) (qOfInt M.dtQ)
        match P.R.modes[q]?, M.modes[q]? with
        | some pm, some m =>
            modeCore vs mt.scales u names q pm m M.env && extra q pm m
        | _, _ => false))

/-- **Settling-family fidelity** (kernel-decidable; certified by `rfl` per benchmark
against the parser-emitted IR literal). -/
def faithfulSettling {n : ℕ} (P : PProblem) (mt : TransMeta)
    (M : SettlingModel n) : Bool :=
  faithfulFrame P mt M (fun _ pm m => bandSettling P.R.stateVars mt.scales pm m)

/-- **Terrain-family fidelity**: core + v-band policy + s-bands. -/
def faithfulTerrain {n : ℕ} (P : PProblem) (mt : TransMeta)
    (T : TerrainModel n) : Bool :=
  T.sbands.length == T.core.modes.length &&
  faithfulFrame P mt T.core (fun q pm m =>
    bandTerrain P.R.stateVars mt.scales pm m T.core.env &&
    (match T.sbands[q]? with
     | some sb => sbandFaithful P.R.stateVars mt.scales pm sb
     | none => false))

/-- **Affine-family fidelity**: core + glo/vtop policy. -/
def faithfulAffine {n : ℕ} (P : PProblem) (mt : TransMeta)
    (A : AffineModel n) : Bool :=
  A.vtops.length == A.core.modes.length &&
  faithfulFrame P mt A.core (fun q pm m =>
    match A.vtops[q]? with
    | some top => bandAffine P.R.stateVars mt.scales pm m top
    | none => false)

end RelCertifier
