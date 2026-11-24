import VersoManual

open Verso.Genre Manual
open Verso.Code.External

set_option pp.rawOnError true
set_option verso.exampleProject "../"
set_option verso.exampleModule "BfTuringComplete.Exposition.Main"

#doc (Manual) "The Whole Run" =>

One run of the step program performs one step of the machine. The full Brainfuck program raises
the initial state and `run`, then loops on `run`:

```anchor program
def program : Program :=
  (FProg.set (Flag.state default : Fl) ⨾ .set .run).compile ++ atFlag (Flag.run : Fl) [mainLoop M]
```

# Matching the two runs

The claim asks for two things. On an input where the machine halts, the program halts with exactly
the encoded output. On an input where the machine runs forever, so does the program. Mathlib
packages this kind of statement as `Turing.Respects`: give a relation between configurations of the
two machines, show that every step of one is matched by one or more steps of the other, and their
`eval`s agree. Our relation says that while the machine runs, the program sits at the top of its
main loop with the configuration's flags on the tape, and once the machine has halted, the program
has finished and the tape holds exactly the machine's tape:

```anchor Tracks
def Tracks (c : TM0.Cfg Γ Λ) (b : Cfg) : Prop :=
  TM0.step M c = none ∧ (∃ t, Holds 0 (tapeSet c.Tape : Set (ℤ × Fl)) t ∧ b = ⟨[], t⟩) ∨
  (TM0.step M c).isSome ∧ ∃ t, Running c t ∧ b = ⟨mainLoop M :: mv (-pos (Flag.run : Fl)), t⟩
```

# The block code

A symbol is written as the block of its flags: one cell per flag, with only the `sym a` cell set, or
nothing at all for the blank. Different symbols differ in the cell of the non-blank one, so the code
is injective, as the claim demands.

```anchor code
def code [FinEnum Γ] [FinEnum Λ] : BlockCode Γ where
  width := card Fl
  enc := enc (Λ := Λ)
  length_enc _ := block_length _
  enc_default := by simp [enc, block, symFlags, List.map_const', default]
  injective := enc_injective
```

# The claim

The claim speaks of arbitrary finite types, while the compiler wants an explicit enumeration of the
symbols and states. Converting one into the other is the only noncomputable step in the proof. For
any concretely listed alphabet and set of states, the compiler is an ordinary function we can run,
as the next chapter shows.

```anchor claim
theorem claim : Claim := by
  intro Γ Λ _ _ _ _ M
  classical
  let _ : FinEnum Γ := .ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
  let _ : FinEnum Λ := .ofEquiv (Fin (Fintype.card Λ)) (Fintype.equivFin Λ)
  exact ⟨code, program M, eval_eq M⟩
```
