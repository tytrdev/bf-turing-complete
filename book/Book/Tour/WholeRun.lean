import VersoManual
import Book.Widgets

open Verso.Genre Manual
open Book.Widgets

set_option pp.rawOnError true

#doc (Manual) "The Whole Run" =>

One step is done. Running the machine means repeating it until the machine halts, and that is what
the `run` flag is for.

# The program

The whole Brainfuck program is:

1. Raise `state 0` and `run` in block 0, where the head starts.
2. Walk to `run`'s cell and loop: _while `run` is raised, lower it, walk back to the start of the
   block, do one step, and walk to `run`'s cell again._
3. Walk back to the start of the block.

The loop is a `when run` that keeps going, because each step re-raises `run` in the block under
the new head position, which is exactly where the loop looks next. When the machine halts, the plan
contains no `run`, so the next check finds it lowered and the loop ends.

# Why the output is exact

At the moment the loop ends, look at what is left on the tape. Dispatch consumed the `state` flag.
The plan for a halting cell was only `write a`, and the write phase turned that back into the
symbol. Nothing raised `next`, `left`, `right` or `run`, and the scratch flag `blank` is always
lowered by the end of dispatch. So only symbol flags remain: the tape is exactly the machine's final
tape, spelled with the block code, and the pointer is back at the start of the head's block. That is
the strict "exactly the output" the claim demands.

And if the machine never halts, every step raises `run` again, so the loop never ends either.

# The full run

Here is the whole run of the swap machine on `1 2 2`. *Next* and *Prev* jump one machine step;
*Run Brainfuck to next step* runs the real program to the next one.

```bfPlayer
data/swap-trace.json
```

The machine takes 11 steps. The Brainfuck program takes 9709: a little under 900 Brainfuck
instructions per machine step, most of them walks between flags. Nothing here is optimised; the
compiler aims to be easy to prove correct, not fast.

```predict
The machine takes 11 steps, but the main loop checks `run` 13 times. Where do the other two come from?
The halting step is a pass of its own: the machine is in state 3, dispatch finds no rule, raises only `write`, and that pass runs too. That makes 12 passes that run the step program. The 13th check finds `run` lowered and leaves the loop.
```
