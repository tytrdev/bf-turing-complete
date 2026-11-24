import BfTuringComplete.Exposition.Main

/-!
# A worked example

The compiler is an ordinary, computable Lean function, so we can run it. Here is a small machine:
symbols `0` (blank), `1`, `2`; it swaps `1 ↔ 2` in every cell up to the first blank, walks back to
the start, and halts.

| state | reads `0`         | reads `1`             | reads `2`             |
|-------|-------------------|-----------------------|-----------------------|
| 0     | move left, go 2   | write `2`, go 1       | write `1`, go 1       |
| 1     | move right, go 0  | move right, go 0      | move right, go 0      |
| 2     | move right, go 3  | move left, go 2       | move left, go 2       |
| 3     | halt              | halt                  | halt                  |
-/

namespace BF.Exposition.Example
open Turing

/-- The swapping machine. -/
def swap : TM0.Machine (Fin 3) (Fin 4)
  | 0, 0 => some (2, .move .left)
  | 0, 1 => some (1, .write 2)
  | 0, 2 => some (1, .write 1)
  | 1, _ => some (0, .move .right)
  | 2, 0 => some (3, .move .right)
  | 2, _ => some (2, .move .left)
  | _, _ => none

/-! ## The Brainfuck program -/

/-- Brainfuck source text. -/
partial def render : Program → String
  | [] => ""
  | .inc :: p => "+" ++ render p
  | .dec :: p => "-" ++ render p
  | .left :: p => "<" ++ render p
  | .right :: p => ">" ++ render p
  | .loop b :: p => "[" ++ render b ++ "]" ++ render p

/-- The compiled program. -/
def swapBF : Program := program swap

/-- Each TM cell becomes a block of this many BF cells, one per flag. -/
def width : ℕ := FinEnum.card (Flag (Fin 3) (Fin 4))

#eval width                         -- 18
#eval (render swapBF).length
#eval (render swapBF).take 300

/-! ## Running both machines

Brainfuck's `eval` is a `Part`, defined for every program but not something we can execute. To
watch the program run we iterate the same `step` function with a step budget. -/

/-- Run Brainfuck for at most `fuel` steps; `none` if it has not halted by then. -/
def runBF : ℕ → Cfg → Option Cfg
  | 0, _ => none
  | fuel + 1, c => match step c with
    | none => some c
    | some c' => runBF fuel c'

/-- Run the TM for at most `fuel` steps. -/
def runTM : ℕ → TM0.Cfg (Fin 3) (Fin 4) → Option (TM0.Cfg (Fin 3) (Fin 4))
  | 0, _ => none
  | fuel + 1, c => match TM0.step swap c with
    | none => some c
    | some c' => runTM fuel c'

/-- The first `n` symbols of a TM tape, from the head. -/
def readTM (n : ℕ) (T : Tape (Fin 3)) : List (Fin 3) := (List.range n).map fun i ↦ T.nth i

/-- Decode block `j` of a BF tape: the symbol whose flag is raised, or the blank. -/
def decodeBlock (t : Tape Cell) (j : ℕ) : Fin 3 :=
  ((FinEnum.toList (Fin 3)).find? fun a ↦
    t.nth (width * j + pos (Flag.sym a : Flag (Fin 3) (Fin 4))) = 1).getD 0

/-- The first `n` symbols stored on a BF tape. -/
def readBF (n : ℕ) (t : Tape Cell) : List (Fin 3) := (List.range n).map (decodeBlock t)

/-- The TM's output on `input`. -/
def tmOutput (input : List (Fin 3)) : Option (List (Fin 3)) :=
  (runTM 1000 (TM0.init input)).map fun c ↦ readTM (input.length + 1) c.Tape

/-- The BF program's output on the encoded `input`, decoded. -/
def bfOutput (input : List (Fin 3)) : Option (List (Fin 3)) :=
  (runBF 10000000 (init swapBF (input.flatMap (code (Λ := Fin 4)).enc))).map fun c ↦
    readBF (input.length + 1) c.tape

#eval tmOutput [1, 2, 2]            -- some [2, 1, 1, 0]
#eval bfOutput [1, 2, 2]            -- some [2, 1, 1, 0]

#guard bfOutput [1, 2, 2] = tmOutput [1, 2, 2]
#guard bfOutput [2, 2, 1, 1] = tmOutput [2, 2, 1, 1]
#guard bfOutput [] = tmOutput []

end BF.Exposition.Example
