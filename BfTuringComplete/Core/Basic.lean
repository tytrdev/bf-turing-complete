import Mathlib.Computability.TuringMachine.Tape
import Mathlib.Computability.StateTransition

/-!
# Brainfuck: syntax and small-step semantics

Design decisions:
* Cells are 8-bit and wrap (`Fin 256`), the weakest common BF variant.
* The tape is Mathlib's `Turing.Tape`, unbounded in both directions, blank = 0.
* Programs are syntax trees, so brackets are balanced by construction.
* No `,` / `.`: input is the initial tape, output is the final tape (as for TM0).
* Small-step semantics in Mathlib's `σ → Option σ` style, so `StateTransition.eval`
  and the `Respects` simulation lemmas apply directly.
-/

namespace BF

open Turing

/-- A tape cell: an 8-bit wrapping byte. -/
abbrev Cell := Fin 256

/-- BF statements. `loop body` is `[body]`. -/
inductive Stmt
  | inc
  | dec
  | left
  | right
  | loop (body : List Stmt)
  deriving Repr

abbrev Program := List Stmt

/-- A machine configuration: the code still to run, and the tape. -/
structure Cfg where
  code : Program
  tape : Tape Cell

/-- One step of execution. `none` means the program has halted.
A loop whose head cell is nonzero unrolls one copy of its body in front of itself. -/
def step : Cfg → Option Cfg
  | ⟨[], _⟩ => none
  | ⟨.inc :: k, t⟩ => some ⟨k, t.write (t.head + 1)⟩
  | ⟨.dec :: k, t⟩ => some ⟨k, t.write (t.head - 1)⟩
  | ⟨.left :: k, t⟩ => some ⟨k, t.move .left⟩
  | ⟨.right :: k, t⟩ => some ⟨k, t.move .right⟩
  | ⟨.loop b :: k, t⟩ =>
      if t.head = 0 then some ⟨k, t⟩ else some ⟨b ++ .loop b :: k, t⟩

/-- Start running `p` with `l` written on the tape, head on its first cell. -/
def init (p : Program) (l : List Cell) : Cfg := ⟨p, Tape.mk₁ l⟩

/-- Run `p` on input `l`. Defined iff the program halts; the result is the tape
from the head rightwards, matching `Turing.TM0.eval`. -/
def eval (p : Program) (l : List Cell) : Part (ListBlank Cell) :=
  (StateTransition.eval step (init p l)).map fun c ↦ c.tape.right₀

end BF
