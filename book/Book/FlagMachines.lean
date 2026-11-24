import VersoManual

open Verso.Genre Manual
open Verso.Code.External

set_option pp.rawOnError true
set_option verso.exampleProject "../"
set_option verso.exampleModule "BfTuringComplete.Exposition.Flags"

#doc (Manual) "Flag Machines" =>

Brainfuck has only `+ - < > [ ]`, and nearly everything it does is arithmetic on positions.
A direct proof that some Brainfuck program simulates a Turing machine becomes a proof about offsets
and has to show again and again that cell 37 is not cell 38.

So we split the work in two. First we build a small language whose data is _flags_: yes/no facts
such as "this cell holds the symbol `a`" or "the head is here, in state `q`". We prove once and for
all that Brainfuck runs that language correctly. After that, the Turing machine part never mentions
a Brainfuck cell again.

# The language

Fix a finite type of flags. The tape of a flag machine is a sequence of blocks, and each block holds
some subset of the flags. A flag program has five instructions:

```anchor FProg
inductive FProg (F : Type*)
  | skip
  | set (f : F)
  | clr (f : F)
  | shift (d : ℤ)
  | seq (p q : FProg F)
  | when (f : F) (p : FProg F)
```

Its meaning is a function on flag sets, partial in exactly one way: `when f p`
must not leave `f` raised, or the Brainfuck loop it compiles to would run `p` a second time.

```anchor den
noncomputable def den : FProg F → Set (ℤ × F) → Option (Set (ℤ × F))
  | skip, P => some P
  | set f, P => some (insert (0, f) P)
  | clr f, P => some (P \ {(0, f)})
  | shift d, P => some ((fun x ↦ (x.1 + d, x.2)) ⁻¹' P)
  | p ⨾ q, P => (p.den P).bind q.den
  | when f p, P =>
    if (0, f) ∈ P then (p.den (P \ {(0, f)})).bind fun Q ↦ if (0, f) ∈ Q then none else some Q
    else some P
```

# Running it on Brainfuck

Each block is a run of cells, one per flag, holding 1 or 0. Setting a flag is `[-]+` on its cell and
clearing it is `[-]`. Both are correct whatever the cell held, so neither needs a precondition.
`when f p` is the loop `[ [-] p ]` on the flag's cell.

```anchor compile
def compile : FProg F → Program
  | skip => []
  | set f => atFlag f [.loop [.dec], .inc]
  | clr f => atFlag f [.loop [.dec]]
  | shift d => mv (card F * d)
  | p ⨾ q => p.compile ++ q.compile
  | when f p => atFlag f [.loop (.loop [.dec] :: mv (-pos f) ++ p.compile ++ mv (pos f))]
```

The main theorem of this chapter says that compiled code does to the tape what the program does to
the flag set:

```anchor compile_spec
theorem compile_spec : ∀ (p : FProg F) {P Q : Set (ℤ × F)} {t : Tape Cell},
    p.den P = some Q → Holds 0 P t → ∃ u, Holds 0 Q u ∧ Runs p.compile t u
```
