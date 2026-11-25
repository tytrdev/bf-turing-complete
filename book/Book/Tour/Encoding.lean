import VersoManual
import Book.Widgets

open Verso.Genre Manual
open Book.Widgets

set_option pp.rawOnError true

#doc (Manual) "Spelling a Tape in Brainfuck Cells" =>

The first design decision is the block code: how one Turing machine cell becomes Brainfuck cells.

# One cell per flag

Each machine cell becomes one _block_ of Brainfuck cells, and each Brainfuck cell in the block is a
_flag_: it holds 1 (raised) or 0 (lowered). A block has one flag for every fact the simulation
might need to record about that position:

* `sym a` for each symbol `a`: "this cell holds `a`". The blank gets no flag of its own: a blank
  cell is a block with nothing raised, which is exactly the "blank is all zeros" rule.
* `state q` for each state `q`: "the head is here, and the machine is in state `q`".
* `run`: "the machine has not halted yet".
* `write a`, `next q`, `left`, `right`: plans for the current step, explained in the chapter after
  next.
* `blank`: scratch space for one test.

For the swap machine (3 symbols, 4 states) that is 3 + 4 + 1 + 3 + 4 + 2 + 1 = 18 flags, so every
block is 18 cells wide. Here is the input `1 2 2` spelled out. Each column is one block; the names
on the right say which flag each row is. Hover over a cell to see its value.

```encoding
data/swap-trace.json
```

Spelling a symbol this way (one flag per possible value, exactly one of them raised) is called a
_one-hot_ encoding. It is wasteful: 18 cells to store one of three values. But it makes every
question the program asks a yes/no question about a single cell, and Brainfuck's loop is
precisely a yes/no test on a single cell.

```predict
The machine starts in state 0 with its head on the first cell. Which flags does the program raise before its first step, and in which block?
Two: `state 0` and `run`, both in block 0, the block under the head. The input on the tape only has symbol flags; the program adds the state and the "keep going" flag itself.
```

# Why the code is fair

Look back at the rules from the last chapter. Every block has the same width (18). Different
symbols raise different flags, so different symbols give different blocks. The blank raises
nothing, so it is all zeros. The block code is fixed before the input is known, so nothing about
the input is hidden in it.

The extra flags (`state`, `run`, the plans and the scratch flag) only ever appear while the program
is running. At the end, the program has to lower all of them again, so that the final tape holds
symbol flags only: exactly the spelled-out output.
