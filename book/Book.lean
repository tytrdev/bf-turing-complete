import VersoManual
import Book.Tour
import Book.Proof

open Verso.Genre Manual
open Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "Brainfuck Simulates Turing Machines" =>
%%%
authors := ["Ty Tracey"]
shortTitle := "BF ⊇ TM"
%%%

This book walks through a Lean proof that every finite Turing machine can be simulated by a
Brainfuck program. The statement is exact: the program, run on the encoded input, leaves exactly
the encoded output, and it runs forever exactly when the machine does.

There are two ways in. *Part I* is a tour for programmers who have never met Brainfuck, Turing
machines or Lean, with simulators you can run in the page. *Part II* is the proof itself, for
readers who already know the background.

{include 1 Book.Tour}

{include 1 Book.Proof}
