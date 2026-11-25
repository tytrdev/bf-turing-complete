import VersoManual
import Book.Widgets

open Verso.Genre Manual
open Book.Widgets

set_option pp.rawOnError true

#doc (Manual) "A Tiny Language of Flags" =>

Writing the whole simulation directly in Brainfuck would be miserable: every instruction would be
about cell offsets like "17 cells to the left". Instead, the proof introduces a small language in
between, whose programs talk about flags and blocks, and compiles it to Brainfuck. This is the same
trick as writing in C instead of assembly.

# Five instructions

A _flag program_ is built from:

* `set f`: raise flag `f` in the current block.
* `clr f`: lower flag `f` in the current block.
* `shift d`: move to the block `d` blocks to the right (left if `d` is negative).
* `p ⨾ q`: run `p`, then `q`.
* `when f p`: if `f` is raised in the current block, lower it and run `p` once; otherwise do nothing.

`when` is the only way to make a decision, and it always consumes the flag it tests. That keeps the
loop structure trivial: every loop runs zero times or once.

# Compiling to Brainfuck

Every instruction compiles to a few Brainfuck instructions. Inside a block, flag `f` is at a fixed
offset, `pos f`. The compiler walks to the flag's cell, acts, and walks back:

* `set f` becomes _walk to_ `f`, `[-]+`, _walk back_.
* `clr f` becomes _walk to_ `f`, `[-]`, _walk back_.
* `shift d` becomes `>` (or `<`) repeated _width × d_ times.
* `p ⨾ q` becomes the code for `p` followed by the code for `q`.
* `when f p` becomes _walk to_ `f`, `[[-]` _walk back_, the code for `p`, _walk to_ `f`, `]`, _walk back_.

These are exactly the three patterns from the first chapter. Take blocks of three flags `a`, `b`,
`c` (offsets 0, 1, 2) and the program `when a (set c)`. It compiles to `[[-]>>[-]+<<]`. Run it with
`a` raised and then with `a` lowered:

```bfPlayground
input: 1 0 0
[[-]>>[-]+<<]
```

With input `1 0 0` the result is `0 0 1`: `a` was consumed and `c` raised. Change the input to
`0 0 0` and nothing happens. Now `shift 1 ⨾ set b`, which moves one block (three cells) right and
raises `b` there:

```bfPlayground
>>>>[-]+<
```

(The compiler emits `>>>` for the shift, then `>` to reach `b`, `[-]+`, and `<` back to the start of
the block.)

```predict
What does `when a (shift 1)` do when `a` is raised, and why is that a problem for the loop?
It lowers `a` and moves one block right. But the compiled loop ends with "walk to `a`, check", and that check now looks at the `a` flag of the new block. If `a` happens to be raised there, the loop runs again. So a `when` body may move, but it must finish in a block where the tested flag is down. The proof builds this into the meaning of `when` (`den_when_on` in Part II), and the step program relies on it: its move phase is `when left` followed by a body that shifts one block left, where `left` is down.
```

# Why bother

The payoff is in the proof. Part II proves once that each flag instruction does what it says on any
tape (`compile_spec`). After that, the proof never looks at a Brainfuck cell again: everything is
about which flags are raised in which block. The rest of the Tour works at that level too.
