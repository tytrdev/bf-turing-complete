import VersoManual

open Verso.Genre Manual
open Verso.Code.External

set_option pp.rawOnError true
set_option verso.exampleProject "../"
set_option verso.exampleModule "BfTuringComplete.Exposition.Machine"

#doc (Manual) "One Step" =>

The previous chapter gave us flag programs, which Brainfuck runs faithfully. Here we write one
step of a Turing machine as a flag program and prove it correct. From now on we never look at a
Brainfuck cell: everything is about which flags are raised in which block.

# The encoding

Each cell of the Turing machine's tape becomes one block, and these are its flags:

```anchor Flag
inductive Flag (Γ Λ : Type*)
  | sym (a : Γ)
  | state (q : Λ)
  | blank
  | write (a : Γ)
  | next (q : Λ)
  | left
  | right
  | run
  deriving DecidableEq
```

* `sym a` says the cell holds symbol `a`. The blank symbol has no flag, so a blank cell is an
  all-zero block. That is what lets the infinite blank parts of the two tapes match.
* `state q` marks the head, and says the machine is in state `q`.
* `run` says the machine has not halted. The main loop repeats while it is raised.
* `write a`, `next q`, `left` and `right` are _pending_ actions of the current transition.
* `blank` is scratch space for one test.

A configuration "state `q`, tape `T`" becomes the symbol flags of `T`, plus `state q` in block 0.

# Why the step has four phases

The obvious program, "for each state and symbol, if they match, do the transition", has a trap.
Flag programs test flags one at a time, in a fixed order. If the transition for symbol `a` writes
symbol `b`, a later test of `sym b` in the same pass fires as well and applies a second transition.

The cure is to separate _deciding_ from _doing_. The first phase only records what the transition
will do, using pending flags that nothing in that phase tests:

```anchor pend
def pend : Option (Λ × TM0.Stmt Γ) → Γ → List Fl
  | none, a => [.write a]
  | some (q, .write b), _ => [.write b, .next q, .run]
  | some (q, .move d), a => [.write a, .dir d, .next q, .run]
```

A transition that moves or halts still writes back the symbol it read, because dispatch consumed the
symbol's flag. The four phases are:

```anchor stepProg
def stepProg : FProg Fl := dispatch M ⨾ flush ⨾ move ⨾ commit
```

# Dispatch

For each state `q`: if `state q` is raised, lower it and find the symbol. Symbols have flags only
when they are not blank, so the blank case is caught by elimination. Raise the scratch flag
`blank`, let whichever `sym a` is present lower it, and if `blank` survives, the cell was blank.

```anchor dispatch
def dispatch : FProg Fl := all fun q ↦ .when (.state q) <|
  .set .blank ⨾ (all fun a ↦ .when (.sym a) (.clr .blank ⨾ raise (pend (M q a) a))) ⨾
    .when .blank (raise (pend (M q default) default))
```

# Flush, move, commit

Flush turns the pending symbol into the cell's symbol, or nothing if it is the blank:

```anchor flush
def put (a : Γ) : FProg Fl := if a = default then .skip else .set (.sym a)

/-- Phase 2: turn the pending symbol into the cell's symbol. -/
def flush : FProg Fl := all fun a ↦ .when (.write a) (put a)
```

To move in direction `d`, the pending state and `run` hop one block over and the head follows them.
On the tape this is a change of coordinates: block `j + d` becomes block `j`, which is exactly what
moving a Turing machine's head does.

```anchor carry
def carry (d : ℤ) : FProg Fl := (all fun q ↦ hop (.next q) d) ⨾ hop .run d ⨾ .shift d
```

```anchor move
def move : FProg Fl := .when .left (carry (-1)) ⨾ .when .right (carry 1)
```

Finally the pending state becomes the state:

```anchor commit
def commit : FProg Fl := all fun q ↦ .when (.next q) (.set (.state q))
```

# The step theorem

Each phase has a lemma of the form "from these flags, the phase produces those flags", and the
flags are always written as some tape plus a short list at the head. Chained together they give the
theorem of this chapter. If the machine halts, the state flag is gone and the tape is unchanged.
Otherwise we get the next configuration, with `run` raised.

```anchor step_den
theorem step_den (c : TM0.Cfg Γ Λ) :
    (stepProg M).den (cfgSet c) =
      some ((TM0.step M c).elim (tapeSet c.Tape)
        fun c' ↦ tapeSet c'.Tape ∪ here [.state c'.q, .run]) := by
```
