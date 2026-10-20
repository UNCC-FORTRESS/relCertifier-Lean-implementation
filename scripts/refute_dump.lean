/-
Refutation finder support (untrusted): print, for a benchmark file, the LOWERED pieces the
refutation claim reads (`Emitted.Data`'s definitions, through the tool's own parser and
lowering), as SMT-LIB strings, one JSON object per line. The finder (`scripts/refute_finder.py`)
searches witnesses over exactly these formulas; the kernel re-checks every witness.

Usage: lake env lean --run scripts/refute_dump.lean <bench> <n> <input.txt>...
  <bench> names the suite benchmark whose cut certificate (`cutV2`) is used (the model's);
  each file's dump is preceded by a `{"kind": "file", "path": ...}` line.
-/
import RelCertifier.VerdictsV2.RunV2
import RelCertifier.Proofs.Encoding.Emitted.RefuteData
import RelCertifier.Trusted.KeyAudit
import RelCertifier.Proofs.Encoding.Emitted.Window

open RelCertifier RelCertifier.Parse RelCertifier.Run RelCertifier.Oracle RelCertifier.Emitted
  RelCertifier.Refute RelCertifier.VerdictsV2

def jstr (s : String) : String := "\"" ++ s ++ "\""
def jlist (xs : List String) : String := "[" ++ String.intercalate ", " xs ++ "]"
def optF {n : ℕ} (coord : Fin n → String) (o : Option (IForm n)) : String :=
  match o with
  | some f => jstr (f.toSmt coord)
  | none => "null"

def dumpOne (path bench : String) (n : ℕ) : IO Unit := do
    IO.println ("{\"kind\": \"file\", \"path\": " ++ jstr path ++ "}")
    match ← readProblemStrict path with
    | .error e => IO.println ("{\"kind\": \"error\", \"msg\": " ++ jstr (e.replace "\"" "'") ++ "}")
    | .ok p =>
      let cX := cutV2 bench
      let vs := vars p
      let coord : Fin n → String := fun i => vs.getD i.val s!"pad{i.val}"
      IO.println ("{\"kind\": \"head\", \"coords\": " ++
        jlist ((List.finRange n).map (fun i => jstr (coord i))) ++
        s!", \"nL\": {nL p}, \"nR\": {nR p}, \"rowsSame\": {rowsSame p}, " ++
        "\"domL\": " ++ optF coord (lowerF vs n Side.L (mLof p 0).evolve) ++
        ", \"domR\": " ++ optF coord (lowerF vs n Side.R (mRof p 0).evolve) ++ "}")
      for l in List.range (nL p) do
        let m := mLof p l
        let comps := (Oracle.invComponents vs n (rowOf p l)).getD []
        let dyn := (dynOf vs n Side.L m).map (fun f => (List.finRange n).map (fun i => jstr ((f i).toSmt coord)))
        IO.println ("{\"kind\": \"L\", \"idx\": " ++ toString l ++ ", \"name\": " ++ jstr m.name ++
          ", \"next\": " ++ jlist (((nextL p).getD l []).map toString) ++
          ", \"guard\": " ++ optF coord (lowerF vs n Side.L m.guard) ++
          ", \"dyn\": " ++ (match dyn with | some d => jlist d | none => "null") ++
          ", \"comps\": " ++ jlist (comps.map (fun g => jstr (g.toSmt coord))) ++
          ", \"compsOK\": " ++ toString (Oracle.invComponents vs n (rowOf p l)).isSome ++
          ", \"leftLie\": " ++ jlist (comps.map (fun g => match dynOf vs n Side.L m with
              | some f => jstr ((Bridge.ownLie Side.L g f).toSmt coord) | none => "null")) ++ "}")
      for q in List.range (nR p) do
        let m := mRof p q
        let atoms := cutAtomsOfX cX.R m.name
        IO.println ("{\"kind\": \"R\", \"idx\": " ++ toString q ++ ", \"name\": " ++ jstr m.name ++
          ", \"guard\": " ++ optF coord (lowerF vs n Side.R m.guard) ++
          ", \"cuts\": " ++ optF coord (NonConn.cutOfAtoms vs n (atoms.map (·.atom))) ++
          ", \"rigid\": " ++ jlist ((List.range (nL p)).map (fun l =>
              jlist (((Oracle.invComponents vs n (rowOf p l)).getD []).map (fun g =>
                optF coord (rigidQueryOf vs n g (mRof p 0) m))))) ++ "}")

def main (args : List String) : IO UInt32 := do
  match args with
  | bench :: nS :: paths =>
    for path in paths do dumpOne path bench nS.toNat!
    pure 0
  | _ => IO.eprintln "usage: refute_dump.lean <bench> <n> <input.txt>..."; pure 2
