import VersoManual

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Conclusion" =>

# What we proved

`BF.Exposition.claim : Claim`: for every Turing machine with finitely many states and symbols there is
a fair block code and a Brainfuck program such that, on every input, the program leaves exactly the
machine's output on the tape, spelled with the block code, and runs forever exactly when the machine
does. Lean's kernel checked the proof, which uses only the three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

# How the argument fits together

The proof is three statements, each standing on the one before:

1. *Brainfuck runs flag programs* (`compile_spec`, "Flag Machines"). After this, no Brainfuck cell
   appears again; the rest of the proof is about which flags are raised in which block.
2. *One pass of the step program is one machine step* (`step_den`, "One Step"). The four phases
   each get a lemma of the form "from these flags, the phase produces those flags", and the lemmas
   compose.
3. *The main loop follows the machine* (`respects` and `eval_eq`, "The Whole Run"). Each pass of the
   loop matches one step, halting included, and Mathlib's simulation lemmas turn that into equality
   of the two `eval`s.

Two decisions did most of the work. Separating the layers means the Turing machine part is proved
about sets of flags, where every phase is a short set equation, rather than about cell offsets.
Separating _deciding_ from _doing_ inside a step (dispatch records a plan, the other phases carry it
out) removes the one trap in the obvious construction: a flag written early in a pass being read
again later in the same pass.

# What this does not cover

* *Computing functions.* The claim is about simulating TM0 machines. Saying Brainfuck computes every
  partial recursive function needs one more link, which Mathlib already provides in its own chain
  of reductions (`PartrecToTM2`, then `TM2to1` and `TM1to0`); it is not connected here.
* *Classic Brainfuck details.* Our tape is unbounded in both directions, and `.` and `,` are left out:
  input and output are the tape itself. Cells are 8-bit and wrap around, the most restrictive common
  choice, and the construction only ever stores 0 and 1 in them.
* *Speed.* The compiler is written to be easy to prove correct. The worked example needs about 880
  Brainfuck instructions per machine step, mostly walking between flags.

# Other versions in the repository

The same claim is proved four times, each ending in a theorem of type `Claim`:
`Reference/` (the first proof, about 15,800 Lean tokens), `Golf/` (as short as possible, about 9,600),
`Elegant/` (the two-layer design, about 10,200) and `Exposition/` (the version in this book, with
prose throughout). `Binary/` adds a reduction: if Brainfuck simulates every machine over a two-letter
alphabet, it simulates every machine, using Mathlib's own `TM0to1`, `TM1to1` and `TM1to0`. It turned
out shorter to handle every alphabet directly, as this book does, than to pay for gluing those
reductions together.

# Where to go from here

To check the result yourself, read the two files you have to trust (`Core/Basic.lean` and
`Core/Statement.lean`) and run `lake build`. To see the construction move, Part I has simulators
that run the compiled program in the page, checked against Lean's own run.
