import BfTuringComplete.Basic
import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# Compiling a TM0 machine to BF

We compile machines over `Fin (n+1)` symbols (0 = blank) and `Fin (m+1)` states
(0 = initial). The general case reduces to this by relabelling.

## Block layout (one block per TM cell, width `w = 2n + 2m + 6`)

| cells              | meaning                                   |
|--------------------|-------------------------------------------|
| `sym a`, a = 1..n  | one-hot symbol (blank = all zero)         |
| `xsym a`           | pending symbol (written at flush)         |
| `st q`, q = 0..m   | one-hot state (head block only)           |
| `pend q`           | pending next state                        |
| `T`                | "symbol is blank" detector                |
| `ML`, `MR`         | pending move                              |
| `R`                | running flag; main loop condition         |

Every gadget starts and ends at offset 0 ("home") of the head block.
All scratch cells hold 0 or 1, and are 0 outside the head block.
-/

namespace BF

open Turing

section Codegen

/-- Move the pointer by `o` cells. -/
def mv : ℤ → Program
  | .ofNat n => List.replicate n .right
  | .negSucc n => List.replicate (n + 1) .left

/-- Increment the cell at offset `o` from home, then return home. -/
def incAt (o : ℤ) : Program := mv o ++ [.inc] ++ mv (-o)

/-- Decrement the cell at offset `o` from home, then return home. -/
def decAt (o : ℤ) : Program := mv o ++ [.dec] ++ mv (-o)

/-- `while cell[o] ≠ 0 { cell[o] -= 1; body }`, where `body` runs from home and returns home.
On 0/1 flags whose body doesn't re-set the flag, this is `if cell[o] = 1 then clear; body`. -/
def ifAt (o : ℤ) (body : Program) : Program :=
  mv o ++ [.loop ([.dec] ++ mv (-o) ++ body ++ mv o)] ++ mv (-o)

end Codegen

variable (n m : ℕ)

namespace Layout

def sym (a : ℕ) : ℕ := a - 1          -- a ∈ 1..n
def xsym (a : ℕ) : ℕ := n + a - 1
def st (q : ℕ) : ℕ := 2 * n + q       -- q ∈ 0..m
def pend (q : ℕ) : ℕ := 2 * n + (m + 1) + q
def T : ℕ := 2 * n + 2 * (m + 1)
def ML : ℕ := T n m + 1
def MR : ℕ := T n m + 2
def R : ℕ := T n m + 3
def width : ℕ := 2 * n + 2 * (m + 1) + 4

end Layout

open Layout

variable (M : TM0.Machine (Fin (n + 1)) (Fin (m + 1)))

/-- Set the pending symbol to `a` (blank needs no flag). -/
def setSym (a : Fin (n + 1)) : Program :=
  if a.val = 0 then [] else incAt (xsym n a.val)

/-- The action for TM state `q` reading `a`, as pending flags. -/
def act (q : Fin (m + 1)) (a : Fin (n + 1)) : Program :=
  match M q a with
  | none => setSym n a                                   -- halt: just restore the symbol
  | some (q', s) =>
    (match s with
      | .move .left => setSym n a ++ incAt (ML n m)
      | .move .right => setSym n a ++ incAt (MR n m)
      | .write b => setSym n b)
    ++ incAt (pend n m q'.val) ++ incAt (R n m)

/-- Branch on the symbol, given that we are in state `q`. -/
def dispatchSym (q : Fin (m + 1)) : Program :=
  incAt (T n m)
  ++ ((List.finRange n).flatMap fun i ↦
        ifAt (sym (i.val + 1)) (decAt (T n m) ++ act n m M q i.succ))
  ++ ifAt (T n m) (act n m M q 0)

def dispatch : Program :=
  (List.finRange (m + 1)).flatMap fun q ↦ ifAt (st n q.val) (dispatchSym n m M q)

def flush : Program :=
  (List.finRange n).flatMap fun i ↦ ifAt (xsym n (i.val + 1)) (incAt (sym (i.val + 1)))

/-- If `flag` is set, carry pending state and `R` to the block at `d` (= ±width), and go there. -/
def moveGadget (flag : ℤ) (d : ℤ) : Program :=
  ifAt flag <|
    ((List.finRange (m + 1)).flatMap fun q ↦
        ifAt (pend n m q.val) (incAt ((pend n m q.val : ℤ) + d)))
    ++ ifAt (R n m) (incAt ((R n m : ℤ) + d))
    ++ mv d

def commit : Program :=
  (List.finRange (m + 1)).flatMap fun q ↦ ifAt (pend n m q.val) (incAt (st n q.val))

def stepBody : Program :=
  dispatch n m M ++ flush n ++
    moveGadget n m (ML n m) (-(width n m : ℤ)) ++ moveGadget n m (MR n m) (width n m) ++
    commit n m

/-- The compiled program. -/
def compile : Program :=
  incAt (st n 0) ++ incAt (R n m) ++ ifAt (R n m) (stepBody n m M)

/-- The block encoding of a symbol. -/
def encSym (a : Fin (n + 1)) : List Cell :=
  (List.range (width n m)).map fun i ↦ if a.val ≠ 0 ∧ i + 1 = a.val then 1 else 0

end BF

namespace BF

theorem encSym_default (n m : ℕ) :
    encSym n m default = List.replicate (Layout.width n m) default := by
  simp [encSym, List.map_const', default]

end BF
