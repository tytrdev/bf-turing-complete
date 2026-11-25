import VersoManual
import Book.Widgets

open Verso.Genre Manual
open Book.Widgets

set_option pp.rawOnError true

#doc (Manual) "Turing Machines" =>

A Turing machine is the simplest model of a general-purpose computer. Like Brainfuck it has a tape
and a head, but where Brainfuck has a program, a Turing machine has a _rule table_.

* The tape is an endless row of cells. Each cell holds a _symbol_ from a fixed, finite alphabet.
  One symbol is the _blank_; every cell starts blank except the input.
* The head sits on one cell. The machine also has a current _state_, one of finitely many.
* The rule table says, for each state and each symbol the head might be reading, what to do:
  either write a symbol, or move one cell left or right; and which state to go to next.
  If there is no rule for the current state and symbol, the machine _halts_.

That's all. A run starts in state 0 with the head on the first input cell and applies rules until it
halts, possibly never. What it leaves on the tape is its output. (This flavour, where each rule
either writes or moves but not both, is the one Lean's mathematics library calls `TM0`.)

# A machine that swaps 1s and 2s

Our running example has three symbols, `0` (the blank, shown as `·`), `1` and `2`, and four states.
It swaps `1` and `2` in every cell up to the first blank, walks back to the start, and halts:

* State 0 is "at a cell to process": swap the symbol, or on reaching a blank turn around.
* State 1 is "just swapped": step right to the next cell.
* State 2 is "walking back": keep moving left until the blank before the input.
* State 3 is "done": it has no rules, so the machine halts.

Press *Step* to apply one rule. The highlighted entry in the table is the rule about to fire.

```tmStepper
data/swap-trace.json
```

```predict
On input 1 2 2, how many steps does the machine take before it halts?
Eleven. Three swaps of one step each, three moves right, the turn at the blank (one move left), three moves left to walk back, and one move right off the blank before the input. Stepping through above confirms it.
```

# Why this model matters

Nobody writes software as rule tables. The point of Turing machines is that they are simple enough
to reason about and yet, as far as anyone knows, they can compute anything that any computer can.
So to show that some other system is just as powerful ("Turing complete"), it is enough to show that
it can imitate every Turing machine. That is what this book does for Brainfuck.

The machines we handle are _finite_: finitely many states and symbols. That is no restriction;
every Turing machine is finite in this sense. The tape is what is unbounded.
