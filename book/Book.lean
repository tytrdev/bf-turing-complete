import VersoManual
import Book.Tour
import Book.Proof

open Verso.Genre Manual
open Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "Brainfuck Simulates Turing Machines" =>
%%%
authors := ["Ty Tracey"]
authorshipNote := some "written with heavy use of Claude (Anthropic)"
shortTitle := "BF ⊇ TM"
%%%

This book walks through a Lean proof that every finite Turing machine can be simulated by a
Brainfuck program. The statement is exact: the program, run on the encoded input, leaves exactly
the encoded output, and it runs forever exactly when the machine does.

There are two ways in. *Part I* is a tour for programmers who have never met Brainfuck, Turing
machines or Lean, with simulators you can run in the page. *Part II* is the proof itself, for
readers who already know the background.

*How this was made.* This project was built with heavy use of Claude, Anthropic's AI model, working
in Claude Code: Claude wrote most of the Lean proofs, this book's text and its simulators, under Ty
Tracey's direction. You don't have to take the result on trust: Lean checks every proof, and the
statements it checks are short enough to read yourself ("What Lean Checked" in Part I says exactly
which parts those are). The prose and the simulators are not checked by Lean;
the simulators are tested against Lean's own runs.

{include 1 Book.Tour}

{include 1 Book.Proof}
