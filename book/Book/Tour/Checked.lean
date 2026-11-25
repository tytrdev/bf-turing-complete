import VersoManual
import Book.Widgets

open Verso.Genre Manual
open Book.Widgets

set_option pp.rawOnError true

#doc (Manual) "What Lean Checked, and What You Have to Trust" =>

Everything in the Tour so far was explanation. What makes it a proof is that the same construction
is written in Lean, a programming language whose type checker also checks mathematical proofs, and
Lean accepts that the program really does what the claim says, for every machine and every input.

# What the checker guarantees

The project ends with a theorem, `BF.Exposition.claim : Claim`, stating exactly the claim from
"What We Claim". Lean's kernel, a small program whose only job is to check proofs, has checked every
step of its proof. Lean can also report which basic assumptions (axioms) a theorem uses:

```
#print axioms BF.Exposition.claim
-- 'BF.Exposition.claim' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Those three are the standard foundations of Lean's mathematics library: two basic rules of logic
and the axiom of choice. In particular, no `sorry` (Lean's "trust me" placeholder) and nothing
specific to this project.

# What you have to trust

A checked proof only proves the statement that was written down. So the parts you have to read
and agree with yourself are the definitions the statement uses:

* *What Brainfuck does*: `Core/Basic.lean`, about 60 lines: cells are bytes that wrap around,
  the tape is endless in both directions, and the exact effect of each instruction.
* *What is claimed*: `Core/Statement.lean`, shown in full in "What We Claim".
* *What a Turing machine is*: the `TM0` definitions in Mathlib, Lean's community mathematics
  library, which are used and reviewed far beyond this project.

The rest, every lemma about flags, phases, loops and encodings, is checked, so you don't need to
read it to believe the result. You read it to understand _why_ it is true, which is what Part II is
for.

# What is not checked

The prose of this book, and the simulators in it. The simulators are tested instead: the program
they run is the one Lean compiled, the runs they show were computed by Lean, and an automated test
checks that the in-page interpreter reproduces Lean's run of the example exactly (all 9709 steps,
and the tape at every phase boundary). When you press a "Run Brainfuck" button, the page compares
its result with Lean's and shows ✓ when they agree.

# Checking it yourself

With Lean installed, clone the repository and run `lake build`. If it finishes without errors, the
proof is correct. That's the whole procedure. There are four versions of the proof in the repository
(`Reference`, `Golf`, `Elegant`, `Exposition`), each ending in its own theorem of type `Claim`;
Part II walks through `Exposition`.
