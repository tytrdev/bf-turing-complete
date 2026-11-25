import VersoManual
import Book.Widgets

open Verso.Genre Manual
open Book.Widgets

set_option pp.rawOnError true

#doc (Manual) "One Step, in Four Phases" =>

Now the heart of the construction: a flag program that performs one step of the machine. It runs
with the pointer at the block under the head, where `state q` is raised.

# The obvious program, and why it fails

The obvious approach is a big case analysis: _for each state `q` and symbol `a`, when `state q` and
`sym a` are raised, do the rule for (`q`, `a`)._

The trouble is that flag programs test one flag at a time, in a fixed order. Suppose the rule for
(state 0, symbol 1) writes `2`. If the program carries it out at once, it raises `sym 2`, and a few
instructions later the program reaches its test for (state 0, symbol 2), finds `sym 2` raised, and
applies a second rule in the same step. New state flags cause the same problem.

# Decide first, then act

The fix is to split the step into a phase that only _decides_ and phases that _act_. The decision is
recorded in flags that the deciding phase never tests:

* `write a`: "the cell should end up holding `a`",
* `left` or `right`: "the head should move",
* `next q`: "the next state should be `q`",
* `run`: "the machine has not halted".

The four phases are then:

1. *Dispatch.* For each state `q`: when `state q` is raised (consuming it), find the symbol. To do
   that, raise the scratch flag `blank`; for each symbol `a`, when `sym a` is raised (consuming it),
   lower `blank` and raise the plan for (`q`, `a`); finally, if `blank` is still raised, the cell
   was blank, so raise the plan for (`q`, blank). The _plan_ is: `write` the symbol the cell should
   hold (for a "move" rule, the symbol it already had, since testing consumed it), the direction if
   any, `next q'`, and `run`. A cell with no rule gets only `write a`: no `run`, because the
   machine halts.
2. *Write.* For each symbol `a`: when `write a` is raised, raise `sym a` (nothing for the blank).
3. *Move.* When `left` is raised, carry `run` and the `next` flag one block left, then follow them;
   the same for `right`. The symbol flags stay where they are: only the head moves.
4. *Commit.* For each state `q`: when `next q` is raised, raise `state q`.

After commit, the tape holds the new symbol, and the block under the new head position holds the new
`state` flag and `run`: exactly the encoding of the machine's next configuration.

```predict
Dispatch consumes the symbol flag when it tests it. Why doesn't that lose the symbol in a "move" rule, which isn't supposed to change the cell?
Because the plan for a move rule also includes `write a` with the old symbol `a`. The write phase puts it straight back. For a halting cell the plan is only `write a`, which restores the symbol and raises nothing else.
```

# Watch the phases

This is the swap machine again, now with a *Next phase* button. Each press runs the real Brainfuck
program in your browser up to the start of the next phase, shows what that phase is about to do,
and checks the tape against the one Lean computed at that moment. Watch the flags in the outlined
block: the orange `state` flag disappears in dispatch, green `write` and purple `next` flags appear,
then the symbol comes back, the plan moves one block over in a "move" step, and commit turns
`next` into `state`.

```bfPhases
data/swap-trace.json
```

```predict
In which phase does the outlined block (the head's position) change?
In move, and only for a move rule. Dispatch, write and commit all work in the block under the head.
```

Part II states each phase as a lemma ("from these flags, this phase produces those flags") and
composes the four into the theorem that one pass of the step program is one step of the machine.
