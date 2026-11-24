import VersoManual
import Book.FlagMachines
import Book.OneStep
import Book.WholeRun
import Book.Example

open Verso.Genre Manual
open Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "Brainfuck Simulates Turing Machines" =>
%%%
authors := ["Tyler Tracey"]
shortTitle := "BF ⊇ TM"
%%%

This book walks through a Lean proof that every finite Turing machine can be simulated by a
Brainfuck program. The statement is exact: the program, run on the encoded input, leaves exactly
the encoded output, and it runs forever exactly when the machine does.

The code shown here is drawn from the
[`Exposition/`](https://github.com/tytrdev/bf-turing-complete/tree/main/BfTuringComplete/Exposition)
version of the proof and is checked by Lean whenever the book is built.

The proof has two layers. The first chapter builds a tiny language of _flags_ and proves that
Brainfuck runs it. The second writes one Turing machine step in that language. The third loops the
step and proves the claim, and the last compiles and runs a concrete machine.

{include 1 Book.FlagMachines}

{include 1 Book.OneStep}

{include 1 Book.WholeRun}

{include 1 Book.Example}
