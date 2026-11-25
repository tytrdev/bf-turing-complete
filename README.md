# Brainfuck simulates Turing machines, in Lean

A Lean 4 + Mathlib proof that Brainfuck simulates every finite Turing machine.

The statement is `BF.Claim` in [`Core/Statement.lean`](BfTuringComplete/Core/Statement.lean). For every finite Mathlib `TM0.Machine` there is
- an injective, fixed-width block code for its symbols that sends the blank to zero cells, and
- a Brainfuck program,

such that running the program on the encoded input gives exactly the encoded TM output, and runs forever exactly when the TM does. Brainfuck semantics (8-bit wrapping cells, tape unbounded in both directions, no I/O) are in [`Core/Basic.lean`](BfTuringComplete/Core/Basic.lean). These two files are all you need to trust.

Three independent proofs of the claim, each self-contained:

- **`Reference/`**: the first proof.
- **`Golf/`**: as few Lean tokens as possible (`scripts/count.py`).
- **`Elegant/`**: two layers. Brainfuck implements a small flag-machine language, proved once, and one TM step is a short flag program whose correctness is a set equation per phase.
- **`Exposition/`**: the Elegant proof as a literate document, with prose throughout and a computable compiler. Start at [`Exposition/Flags.lean`](BfTuringComplete/Exposition/Flags.lean). [`Example.lean`](BfTuringComplete/Exposition/Example.lean) compiles a small Turing machine, prints the Brainfuck, runs it, and checks the result against the machine.

Plus a reduction: **`Binary/`** proves that if Brainfuck simulates every finite machine over `Bool`, it simulates every finite machine (`claim_of_binary`), using Mathlib's `TM0to1`, `TM1to1` and `TM1to0` reductions.

Scope: this is simulation of TM0 machines, not yet "computes every partial recursive function" (Mathlib's `PartrecToTM2` chain would bridge that). The tape is two-sided, unlike classic left-bounded Brainfuck. The compiler in `Exposition/` is computable for any explicitly enumerated (`FinEnum`) alphabet and state set.

Build: `lake build`.

The proof is also written up as a book, built with [Verso](https://github.com/leanprover/verso) from `book/` (`cd book && lake exe book`) and published at https://tytrdev.github.io/bf-turing-complete/. Part I is a tour for programmers with no background in Brainfuck, Turing machines or Lean, with simulators that run in the page; Part II is the proof, with code drawn from `Exposition/` and checked on every build. The simulators replay runs that Lean computes (`scripts/ExportTrace.lean` writes `book/data/`), and `book/test/golden.mjs` checks the in-page interpreter reproduces Lean's run exactly; CI runs both.
