import VersoManual
import Book.Widgets

open Verso.Genre Manual
open Book.Widgets

set_option pp.rawOnError true

#doc (Manual) "Brainfuck in Five Minutes" =>

Brainfuck is a programming language with eight instructions. It is deliberately tiny, which is what
makes it interesting here: if something this small can compute anything a Turing machine can, the
proof has to show exactly how.

A Brainfuck program works on a _tape_: an endless row of cells, each holding a number from 0 to 255.
All cells start at 0. A _pointer_ marks the current cell. The instructions are:

* `+` adds 1 to the current cell (255 wraps around to 0).
* `-` subtracts 1 (0 wraps around to 255).
* `>` moves the pointer one cell right; `<` moves it one cell left.
* `[` ... `]` is a loop: if the current cell is 0, skip past the matching `]`; otherwise run the
  inside, then come back to the `[` and check again.

Real Brainfuck also has `.` and `,` for printing and reading characters. Our proof leaves them out:
the input is written on the tape before the program starts, and the output is whatever is on the
tape when it stops. Everything else in this book uses only `+ - < > [ ]`.

# Try it

The program below adds the first cell into the second. Read it as: _while the current cell is
not 0, subtract 1 from it, step right, add 1, step back._ Press *Step* to run one instruction at a
time; the highlighted instruction is the one about to run, and the outlined cell is the pointer.

```bfPlayground
input: 3 4
[->+<]
```

When the first cell reaches 0, the loop's check fails and the program stops, leaving 0 and 7.
Editing the program or the starting cells and pressing *Reset* runs your version instead.

# Three patterns worth knowing

Almost everything the compiler in this book produces is built from three patterns.

*Clear a cell.* `[-]` subtracts until the cell is 0, whatever it held.

*Set a cell to 1.* `[-]+` clears it, then adds 1. The compiler uses cells as on/off switches
(we will call them _flags_), so this is how a flag is raised.

*Do something only if a flag is up.* `[-` _body_ `]` runs the body at most once when the cell
holds 0 or 1: if the flag is up, it is lowered and the body runs; when control returns to `[`,
the cell is 0, so the loop ends. (The body must leave the pointer back on the same cell.)

```bfPlayground
input: 1 0 0
[->>+<<]>[->+<]
```

Here the first cell is a flag. Because it is up, the first loop runs once and raises the third
cell; the second loop sits on a flag that is down, so its body never runs. Try starting with
`0 1 0` instead.

# What "simulating" will mean

A Turing machine also has a tape and a head, but its cells hold symbols from some alphabet, and it
has a finite set of _states_ that decide what to do next. The claim of this book is that for every
such machine there is a Brainfuck program that does the same job: write the machine's input on the
tape (each symbol spelled out as a fixed block of cells), run the program, and the tape ends up
holding exactly the machine's output, spelled the same way. The program runs forever exactly when
the machine does.

The next chapters build that program. The idea is that each block of cells stores one tape symbol
plus a handful of flags (which state the machine is in, whether the head is here, what to write
next), and a fixed loop of flag patterns like the ones above performs one machine step at a time.
