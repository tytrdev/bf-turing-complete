import BfTuringComplete.Basic

/-! Executable sanity checks for the semantics (not part of the proof). -/

namespace BF

open Turing

/-- Run at most `fuel` steps; return the final config if the program halted. -/
def runFuel : ℕ → Cfg → Option Cfg
  | 0, _ => none
  | n + 1, c => match step c with
    | none => some c
    | some c' => runFuel n c'

/-- Cells `lo .. hi` of the tape relative to the head. -/
def window (t : Tape Cell) (lo hi : ℤ) : List ℕ :=
  (List.range (hi - lo + 1).toNat).map fun i ↦ (t.nth (lo + i)).val

def test (p : Program) (l : List Cell) (fuel := 10000) : Option (List ℕ) :=
  (runFuel fuel (init p l)).map fun c ↦ window c.tape (-3) 3

open Stmt

-- `+++` on a blank tape
#guard test [inc, inc, inc] [] = some [0, 0, 0, 3, 0, 0, 0]
-- `-` wraps 0 to 255
#guard test [dec] [] = some [0, 0, 0, 255, 0, 0, 0]
-- `[->+<]` moves cell 0 into cell 1
#guard test [loop [dec, right, inc, left]] [5] = some [0, 0, 0, 0, 5, 0, 0]
-- `+[]` never halts
#guard test [inc, loop []] [] = none

end BF
