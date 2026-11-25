import VersoManual
import Book.Tour.Brainfuck
import Book.Tour.TuringMachines
import Book.Tour.Claim
import Book.Tour.Encoding
import Book.Tour.Flags
import Book.Tour.OneStep
import Book.Tour.WholeRun
import Book.Tour.Checked

open Verso.Genre Manual

#doc (Manual) "Part I. The Tour" =>
%%%
file := "tour"
%%%

This part assumes you can program but nothing else: no Brainfuck, no Turing machines, no Lean.
It explains the ideas with pictures and small simulators you can run in the page. Part II is the
precise version, with the Lean code that proves each step.

{include 1 Book.Tour.Brainfuck}

{include 1 Book.Tour.TuringMachines}

{include 1 Book.Tour.Claim}

{include 1 Book.Tour.Encoding}

{include 1 Book.Tour.Flags}

{include 1 Book.Tour.OneStep}

{include 1 Book.Tour.WholeRun}

{include 1 Book.Tour.Checked}
