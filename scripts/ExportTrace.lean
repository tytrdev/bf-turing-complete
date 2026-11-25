import BfTuringComplete.Exposition.Example

/-!
# Export the worked example's runs for the book's simulator

Run from the project root: `lake env lean scripts/ExportTrace.lean`.
Writes `book/data/swap-trace.json`: the compiled Brainfuck source, the flag layout of a block,
the TM run (every configuration), and the BF tape at the top of every pass of the main loop.
The book animates this data; its JS interpreter is tested against it (`book/test/`).
-/

open Turing BF BF.Exposition BF.Exposition.Example Lean

abbrev Fl := Flag (Fin 3) (Fin 4)

def flagName : Fl → String
  | .sym a => s!"sym {a}"
  | .state q => s!"state {q}"
  | .blank => "blank"
  | .write a => s!"write {a}"
  | .next q => s!"next {q}"
  | .left => "left"
  | .right => "right"
  | .run => "run"

/-- Flags in block order. -/
def layout : List String :=
  ((FinEnum.toList Fl).map fun f => (pos f, flagName f)).mergeSort (·.1 ≤ ·.1) |>.map (·.2)

def input : List (Fin 3) := [1, 2, 2]

/-- Blocks shown: two left of the input, two right of it. -/
def lo : ℤ := -2 * width
def hi : ℤ := (input.length + 2) * width

def window (t : Tape Cell) (p : ℤ) : Json :=
  Json.arr <| ((List.range (hi - lo).toNat).map fun i => toJson (t.nth (lo + i - p)).val).toArray

def tmWindow (T : Tape (Fin 3)) (p : ℤ) : Json :=
  Json.arr <| ((List.range (input.length + 4)).map fun i =>
    toJson (T.nth ((i : ℤ) - 2 - p)).val).toArray

/-- TM run: every configuration, with the head's absolute position. -/
partial def tmRun (c : TM0.Cfg (Fin 3) (Fin 4)) (p : ℤ) (acc : Array Json) : Array Json :=
  let j := Json.mkObj [("q", toJson c.q.val), ("head", toJson p), ("tape", tmWindow c.Tape p)]
  match TM0.step swap c with
  | none => acc.push j
  | some c' =>
    let p' := match swap c.q c.Tape.head with
      | some (_, .move .left) => p - 1
      | some (_, .move .right) => p + 1
      | _ => p
    tmRun c' p' (acc.push j)

/-- The rule table of `swap`, as text. -/
def rules : Json := Json.arr <| ((List.finRange 4).map fun q => Json.arr <| ((List.finRange 3).map fun a =>
  match swap q a with
  | none => Json.str "halt"
  | some (q', .move .left) => Json.str s!"move left, go to {q'}"
  | some (q', .move .right) => Json.str s!"move right, go to {q'}"
  | some (q', .write b) => Json.str s!"write {b}, go to {q'}").toArray).toArray

/-- Top-level statements after the main loop (the walk back from `run`'s cell). -/
def backLen : ℕ := (swapBF.reverse.takeWhile fun s => match s with | .loop _ => false | _ => true).length

def isTop (c : Cfg) : Bool := match c.code with
  | .loop _ :: rest => rest.length == backLen
  | _ => false

/-- What follows the main loop's body: the walk back to `run`, the loop itself, the walk home. -/
def tailCode : Program :=
  mv (pos (Flag.run : Fl)) ++ [mainLoop swap] ++ swapBF.drop (swapBF.length - backLen)

/-- Each phase starts when the code left to run is exactly that phase onwards. -/
def phaseStarts : List (String × Program) :=
  let co := (commit (Γ := Fin 3) (Λ := Fin 4)).compile ++ tailCode
  let mo := (move (Γ := Fin 3) (Λ := Fin 4)).compile ++ co
  let fl := (flush (Γ := Fin 3) (Λ := Fin 4)).compile ++ mo
  let di := (dispatch swap).compile ++ fl
  [("dispatch", di), ("write", fl), ("move", mo), ("commit", co)]

def phaseKeys : List (String × ℕ × String) := phaseStarts.map fun (name, k) => (name, k.length, render k)

/-- Phase `i` starts here. The code left to run alone is ambiguous (just after a `when` body ends,
the code left is again `mv (pos f) ++ [loop ...] ++ ...`, the same list as where the phase began),
so phases are matched in order, the first match after the previous phase. -/
def phaseAt (i : ℕ) (c : Cfg) : Option String :=
  match phaseKeys[i]? with
  | some (name, n, r) => if c.code.length == n && render c.code == r then some name else none
  | none => none

/-- BF run: tape at the top of each pass of the main loop, plus step counts. -/
partial def bfRun (c : Cfg) (p : ℤ) (n : ℕ) (acc : Array Json) (ph : Array Json := #[])
    (i : ℕ := 4) : Array Json × ℕ × Json × Array Json :=
  let (acc, i) := if isTop c then
      (acc.push (Json.mkObj [("step", toJson n), ("head", toJson p), ("tape", window c.tape p)]), 0)
    else (acc, i)
  let (ph, i) := match phaseAt i c with
    | some name => (ph.push (Json.mkObj [("step", toJson n), ("phase", toJson name), ("head", toJson p),
        ("tape", window c.tape p)]), i + 1)
    | none => (ph, i)
  match step c with
  | none => (acc, n, window c.tape p, ph)
  | some c' =>
    let p' := match c.code with
      | .left :: _ => p - 1
      | .right :: _ => p + 1
      | _ => p
    bfRun c' p' (n + 1) acc ph i

def main : IO Unit := do
  let tm := tmRun (TM0.init input) 0 #[]
  let (passes, steps, final, phases) := bfRun (init swapBF (input.flatMap (code (Λ := Fin 4)).enc)) 0 0 #[]
  let j := Json.mkObj [
    ("program", toJson (render swapBF)),
    ("width", toJson width),
    ("layout", toJson layout),
    ("input", toJson (input.map (·.val))),
    ("encodedInput", toJson ((input.flatMap (code (Λ := Fin 4)).enc).map (·.val))),
    ("windowStart", toJson lo),
    ("tm", Json.arr tm),
    ("passes", Json.arr passes),
    ("bfSteps", toJson steps),
    ("rules", rules),
    ("phases", Json.arr phases),
    ("final", final)]
  IO.FS.createDirAll "book/data"
  IO.FS.writeFile "book/data/swap-trace.json" j.compress
  IO.println s!"TM steps {tm.size - 1}, BF steps {steps}, main-loop passes {passes.size}, phase starts {phases.size}"

#eval main
