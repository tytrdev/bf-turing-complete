import VersoManual
import Book.Widgets

open Verso.Genre Manual
open Verso.Code.External
open Book.Widgets

set_option pp.rawOnError true
set_option verso.exampleProject "../"
set_option verso.exampleModule "BfTuringComplete.Core.Statement"

#doc (Manual) "What We Claim" =>

Before any of the machinery, it is worth being precise about what is being proved, because "BF can
simulate any Turing machine" can be made true by cheating. For instance, a "simulation" that
stores the answer somewhere strange, or leaves junk on the tape, or only works for machines that
halt, proves much less than it sounds.

# In words

For every Turing machine with finitely many states and symbols, there are two things:

1. a _block code_: a way of spelling each symbol as a fixed-width block of Brainfuck cells, and
2. a Brainfuck program,

such that for every input: if you spell the input with the block code, write it on a Brainfuck
tape, and run the program, the result is exactly the machine's output spelled the same way. And if
the machine runs forever, so does the program.

The block code has to play fair:

* *Fixed width.* Every symbol takes the same number of cells, so the tape can be read block by block.
* *Injective.* Different symbols get different blocks. Otherwise one block could stand for two
  symbols and the program could "forget" which.
* *Blank is all zeros.* A Turing machine's tape is blank forever in both directions; a Brainfuck
  tape is 0 forever. Spelling blank as zeros makes those two infinities line up.

"Exactly the output" is strict on purpose. The program may use extra cells as scratch space while it
runs (it will use plenty), but when it stops, every scratch cell must be back to 0 and the
pointer must be where the machine's head is.

# In Lean

Here is the complete statement, as it appears in the project. This file and the definition of
Brainfuck's behaviour (`Core/Basic.lean`) are everything you need to trust; the rest of the project
is proof, and Lean checks the proof.

```module
import BfTuringComplete.Core.Basic
import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# The target theorem

The definitions for the main theorem (proved in `Main.lean`): every finite TM0 machine
is simulated by a BF program, where each TM symbol is
stored as a fixed-width block of BF cells. The block code must be injective
(no hiding information) and send blank to all-zero cells (so the infinite blank
parts of the tapes line up). The final BF tape must be *exactly* the encoded
final TM tape: scratch cleaned up, head back in place.
-/

namespace BF

open Turing

example : (default : Cell) = 0 := rfl

/-- A fixed-width, injective, blank-preserving encoding of symbols as BF cells. -/
structure BlockCode (Γ : Type*) [Inhabited Γ] where
  width : ℕ
  enc : Γ → List Cell
  length_enc : ∀ a, (enc a).length = width
  enc_default : enc default = List.replicate width default
  injective : Function.Injective enc

/-- Encode a whole (blank-extended) tape half, symbol by symbol. -/
def BlockCode.encTape {Γ : Type*} [Inhabited Γ] (c : BlockCode Γ) (L : ListBlank Γ) :
    ListBlank Cell :=
  L.flatMap c.enc ⟨c.width, c.enc_default⟩

end BF

namespace BF

open Turing

/-- **The claim.** BF simulates every finite TM0 machine: for some injective, fixed-width,
blank-to-zero block code and some program, running the program on the encoded input gives
exactly the encoded TM output, and runs forever exactly when the TM does.
Every proof version must prove this. -/
def Claim.{u, v} : Prop :=
  ∀ {Γ : Type u} {Λ : Type v} [Inhabited Γ] [Inhabited Λ] [Fintype Γ] [Fintype Λ]
    (M : TM0.Machine Γ Λ), ∃ (c : BlockCode Γ) (p : Program),
      ∀ l : List Γ, eval p (l.flatMap c.enc) = (TM0.eval M l).map c.encTape

end BF
```

Reading it from the top, for someone who programs but has not used Lean:

* `structure BlockCode (Γ : Type*)` is like a record type, generic in the alphabet `Γ`. It bundles
  the `width`, the encoding function `enc` (a symbol to a list of cells), and three _proofs_:
  `length_enc` (every block has length `width`), `enc_default` (the blank, Lean's `default`, becomes
  `width` zeros), and `injective`. In Lean, a structure can require proofs as fields, so a value of
  this type can only exist if it is a fair code.
* `encTape` spells out a whole tape, symbol by symbol (`flatMap` is "map, then concatenate").
  `ListBlank` is a list that is implicitly followed by blanks forever.
* `Claim` reads as a formula: for all alphabets `Γ` and state sets `Λ` that are finite (`Fintype`)
  and have a default element (`Inhabited`: the blank symbol and the start state), and every machine
  `M`, there exist a code `c` and a program `p` such that for every input list `l`, running `p` on
  the spelled-out input equals the machine's result, spelled out.
* `eval` returns a `Part`: Lean's type for "a value, if the computation finishes". Saying two
  `Part`s are equal says both halt with the same result, or both run forever. That is how the
  "runs forever exactly when the machine does" condition is built in, for free.

```predict
Why does the claim need the blank to be all zeros? What would go wrong if blank were, say, the block 1 0 0?
The input is finite but the machine's tape is blank forever, so the encoded input would have to be followed by infinitely many 1 0 0 blocks. A Brainfuck tape starts as zeros forever, so the program would first have to write infinitely many blocks, which it cannot do. With blank as zeros, the endless blank parts of both tapes are the same thing.
```

The rest of the Tour shows how to build the block code and the program. Part II proves they work.
