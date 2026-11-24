import BfTuringComplete.Reference.Compile
import BfTuringComplete.Reference.Test

/-! Differential tests: compiled BF vs. Mathlib's TM0 `step`, on small machines. -/

namespace BF

open Turing

def tmRun {Γ Λ} [Inhabited Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) :
    ℕ → TM0.Cfg Γ Λ → Option (TM0.Cfg Γ Λ)
  | 0, _ => none
  | k + 1, c => match TM0.step M c with
    | none => some c
    | some c' => tmRun M k c'

/-- First `k` cells from the head rightwards, from (a) running BF on the encoded input and
(b) running the TM and encoding its output. `none` = didn't halt within fuel. -/
def compare (n m : ℕ) (M : TM0.Machine (Fin (n + 1)) (Fin (m + 1))) (l : List (Fin (n + 1)))
    (k : ℕ) (fuel : ℕ := 200000) : Option (List ℕ) × Option (List ℕ) :=
  let bf := (runFuel fuel (init (compile n m M) (l.flatMap (encSym n m)))).map fun c ↦
    (List.range k).map fun i ↦ (c.tape.right₀.nth i).val
  let tm := (tmRun M fuel (TM0.init l)).map fun c ↦
    (List.range k).map fun i ↦
      ((c.Tape.right₀.flatMap (encSym n m) ⟨Layout.width n m, encSym_default n m⟩).nth i).val
  (bf, tm)

/-- Unary addition: `1^a 0 1^b ↦ 1^(a+b)`, head back at the start. -/
def addM : TM0.Machine (Fin 2) (Fin 6)
  | 0, 1 => some (0, .move .right)
  | 0, 0 => some (1, .write 1)
  | 1, 1 => some (1, .move .right)
  | 1, 0 => some (2, .move .left)
  | 2, 1 => some (3, .write 0)
  | 3, 0 => some (4, .move .left)
  | 4, 1 => some (4, .move .left)
  | 4, 0 => some (5, .move .right)
  | _, _ => none

/-- Three symbols, left moves past the input's start. -/
def leftM : TM0.Machine (Fin 3) (Fin 4)
  | 0, _ => some (1, .write 2)
  | 1, 2 => some (2, .move .left)
  | 2, 0 => some (3, .write 1)
  | _, _ => none

/-- Loops forever. -/
def loopM : TM0.Machine (Fin 2) (Fin 1)
  | _, _ => some (0, .move .right)

#guard let r := compare 1 5 addM [1, 1, 0, 1] (14 * 5); r.1 == r.2
#guard let r := compare 1 5 addM [] (14 * 2); r.1 == r.2
#guard let r := compare 2 3 leftM [1] (14 * 2); r.1 == r.2
#guard let r := compare 1 0 loopM [1] 4 (fuel := 5000); r.1 == r.2

end BF

namespace BF
-- halting runs must actually halt (not just agree on `none`)
#guard (compare 1 5 addM [1, 1, 0, 1] 1).1.isSome
#guard (compare 2 3 leftM [1] 1).1.isSome
end BF
