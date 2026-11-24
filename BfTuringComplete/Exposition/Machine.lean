import BfTuringComplete.Exposition.Flags

/-!
# Brainfuck simulates Turing machines, part 2: one step

Part 1 gave us flag programs, which Brainfuck runs faithfully. Here we write one step of a
Turing machine `M` as a flag program and prove it correct. From now on we never look at a
Brainfuck cell: everything is about which flags are raised in which block.

## The encoding

Each cell of the TM tape is one block. Its flags (`Flag Γ Λ`) are:

* `sym a`: the cell holds symbol `a`. The blank symbol gets no flag at all, so a blank cell is an
  all-zero block. That is what lets the infinite blank parts of the two tapes match.
* `state q`: the head is on this cell, and the machine is in state `q`.
* `run`: the machine has not halted. The main loop in part 3 repeats while this is raised.
* `write a`, `next q`, `left`, `right`: *pending* actions of the current transition.
* `blank`: scratch space for one test.

So the configuration "state `q`, tape `T`" is the flag set `cfgSet ⟨q, T⟩`: the symbol flags of
`T`, plus `state q` in block 0, where the head is.

## Why the step needs four phases

The obvious program, "for each state and symbol, if they match, do the transition", has a trap.
Flag programs test flags one at a time, in a fixed order. If the transition for symbol `a` writes
symbol `b`, a later test of `sym b` in the same pass would fire as well and apply a second
transition. Likewise, a state flag raised for the next step could be mistaken for the current
state.

The cure is to separate *deciding* from *doing*. The first phase only records what the transition
will do, using flags that no test in that phase looks at. Later phases carry it out:

1. **dispatch**: find the current state and symbol, consume both, and raise the pending flags
   (`write a`, a direction, `next q`, `run`);
2. **flush**: turn `write a` into the cell's symbol `sym a`;
3. **move**: carry `next q` and `run` one block left or right, and move the head with them;
4. **commit**: turn `next q` into `state q`.

Each phase gets a lemma of the form "from these flags, the phase produces those flags". We always
describe the flags as some TM tape plus a short list of flags at the head:
`tapeSet T ∪ here [...]`. Composed, the four lemmas say that one step of the flag program is one
step of the machine (`step_den`).
-/

namespace BF.Exposition
open Turing FinEnum FProg

/-- The flags of one block. -/
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

variable {Γ Λ : Type*}

local notation "Fl" => Flag Γ Λ

/-- All flags, listed. This order fixes each flag's cell within a block. Listing them explicitly,
rather than using an abstract `Fintype`, is what keeps the compiler computable. -/
instance [FinEnum Γ] [FinEnum Λ] : FinEnum Fl :=
  .ofList ((toList Γ).map .sym ++ (toList Λ).map .state ++ [.blank] ++ (toList Γ).map .write ++
    (toList Λ).map .next ++ [.left, .right, .run]) fun f ↦ by cases f <;> simp

instance : Nonempty Fl := ⟨.run⟩

/-! ## Flags at the head, and the pending flags of a transition

`here L` is the set of flags `L` in block 0, and `raise L` raises them. A transition's effect is
recorded by `pend`. Note that a transition that moves or halts still writes back the symbol it
read: dispatch consumed the symbol flag, so the symbol has to be put back.
-/

/-- The flags `L`, in the block under the head. -/
def here (L : List Fl) : Set (ℤ × Fl) := {x | x.1 = 0 ∧ x.2 ∈ L}

/-- Raise each flag of `L` in the block under the head. -/
def raise (L : List Fl) : FProg Fl := L.foldr (fun f p ↦ .set f ⨾ p) .skip

theorem den_raise (L : List Fl) (P : Set (ℤ × Fl)) : (raise L).den P = some (P ∪ here L) := by
  induction L generalizing P with
  | nil => simp [raise, here]
  | cons f L ih =>
    simp only [raise, List.foldr_cons] at ih ⊢
    simp only [den, Option.bind_some, ih, Option.some.injEq]
    ext ⟨j, g⟩; simp [here]; tauto

/-- The flag for a direction. -/
def Flag.dir : Dir → Fl
  | .left => .left
  | .right => .right

/-- The pending flags of a transition from a cell holding `a`: the symbol to write, then (unless
the machine halts) the direction, the next state and `run`. -/
def pend : Option (Λ × TM0.Stmt Γ) → Γ → List Fl
  | none, a => [.write a]
  | some (q, .write b), _ => [.write b, .next q, .run]
  | some (q, .move d), a => [.write a, .dir d, .next q, .run]

@[simp] theorem sym_notMem_pend {o : Option (Λ × TM0.Stmt Γ)} {a b : Γ} : .sym b ∉ pend o a := by
  rcases o with _ | ⟨_, d | _⟩ <;> (try cases d) <;> simp [pend, Flag.dir]

@[simp] theorem state_notMem_pend {o : Option (Λ × TM0.Stmt Γ)} {a : Γ} {q : Λ} :
    .state q ∉ pend o a := by
  rcases o with _ | ⟨_, d | _⟩ <;> (try cases d) <;> simp [pend, Flag.dir]

@[simp] theorem blank_notMem_pend {o : Option (Λ × TM0.Stmt Γ)} {a : Γ} : .blank ∉ pend o a := by
  rcases o with _ | ⟨_, d | _⟩ <;> (try cases d) <;> simp [pend, Flag.dir]

/-! ## The flag sets of TM configurations

Two tactics do all the routine set reasoning in this file. Because flags are constructors, a
statement like "`(0, next q')` is not in this set" unfolds to a disjunction of constructor
equations, which `simp` and `aesop` settle. Equality of two flag sets is checked one flag
constructor at a time.
-/

variable [Inhabited Γ]

/-- The flags of a cell holding `a`: its symbol flag, unless `a` is the blank. -/
abbrev symFlags (a : Γ) (f : Fl) : Prop := f = .sym a ∧ a ≠ default

/-- The symbols of tape `T`, as flags. -/
def tapeSet (T : Tape Γ) : Set (ℤ × Fl) := {x | symFlags (T.nth x.1) x.2}

/-- The flags of a TM configuration: its tape, and its state at the head. -/
def cfgSet (c : TM0.Cfg Γ Λ) : Set (ℤ × Fl) := tapeSet c.Tape ∪ here [.state c.q]

set_option hygiene false in
/-- Membership goals about flag sets: unfold, then close by logic. -/
macro "mem" : tactic =>
  `(tactic| (simp [tapeSet, symFlags, here, Tape.write_nth, Flag.dir] <;> aesop))

set_option hygiene false in
/-- Equality of flag sets, by cases on the flag. -/
macro "flags" : tactic => `(tactic| (ext ⟨j, f⟩; cases f <;> mem))

/-! ## Phase 1: dispatch

For each state `q`: if `state q` is raised (it is for exactly one `q`), lower it, and then find the
symbol. Symbols have flags only when they are not blank, so the blank case is caught by elimination.
Raise the scratch flag `blank`, let whichever `sym a` is present lower it, and if `blank` survives,
the cell was blank.

The lemma reads: starting from tape `T` in state `q`, dispatch leaves tape `T` with its head cell
emptied (`T.write default`), plus the pending flags of the transition `M q T.head`.
-/

section Dispatch
variable [Inhabited Λ] [FinEnum Γ] [FinEnum Λ] (M : TM0.Machine Γ Λ)

/-- Phase 1: consume the state and the symbol under the head, raising the pending flags.
The scratch flag `blank` catches the case that no symbol flag is set. -/
def dispatch : FProg Fl := all fun q ↦ .when (.state q) <|
  .set .blank ⨾ (all fun a ↦ .when (.sym a) (.clr .blank ⨾ raise (pend (M q a) a))) ⨾
    .when .blank (raise (pend (M q default) default))

theorem dispatch_den (q : Λ) (T : Tape Γ) :
    (dispatch M).den (tapeSet T ∪ here [.state q]) =
      some (tapeSet (T.write default) ∪ here (pend (M q T.head) T.head)) := by
  refine den_all _ q (den_when_on (by mem) ?_ (by mem))
    fun q' hq ↦ ⟨den_when_off (by mem), den_when_off (by mem)⟩
  rw [show (tapeSet T ∪ here [.state q]) \ {(0, .state q)} = tapeSet T by flags,
    den_seq, den_set, Option.bind_some, den_seq]
  by_cases ha : T.head = default
  · rw [den_all_skip _ fun a ↦ den_when_off (by mem), Option.bind_some,
      den_when_on (by mem) (den_raise _ _) (by mem), ← ha, Tape.write_self]
    congr 2; flags
  · rw [den_all _ T.head (den_when_on (by mem)
        (by rw [den_seq, den_clr, Option.bind_some, den_raise])
        (by mem)) fun a h ↦ ⟨den_when_off (by mem), den_when_off (by mem)⟩,
      Option.bind_some, den_when_off (by mem)]
    congr 2; flags

end Dispatch

/-! ## Phase 2: flush

Exactly one `write b` is pending. It becomes the cell's symbol flag, or nothing if `b` is blank, so
the head cell now holds `b`.
-/

section Flush
variable [FinEnum Γ]

/-- Write symbol `a` into the current block (the blank needs no flag). -/
def put (a : Γ) : FProg Fl := if a = default then .skip else .set (.sym a)

/-- Phase 2: turn the pending symbol into the cell's symbol. -/
def flush : FProg Fl := all fun a ↦ .when (.write a) (put a)

theorem flush_den (T : Tape Γ) (b : Γ) (L : List Fl) (hL : ∀ c, .write c ∉ L)
    (hs : ∀ c, .sym c ∉ L) :
    flush.den (tapeSet (T.write default) ∪ here (.write b :: L)) =
      some (tapeSet (T.write b) ∪ here L) := by
  refine den_all _ b (den_when_on (by mem) ?_ (by mem))
    fun c h ↦ ⟨den_when_off (by mem), den_when_off (by mem)⟩
  unfold put; split_ifs with hb
  · subst hb; rw [den_skip]; congr 1; flags
  · rw [den_set]; congr 1; flags

end Flush

/-! ## Phases 3 and 4: move and commit

To move in direction `d`, `carry d` hops the pending state and `run` one block over and then
shifts the head after them. The effect on the tape is a change of coordinates: block `j + d`
becomes block `j`, which is what `Tape.move` does to a TM tape. If no direction is pending,
nothing moves. Finally `commit` turns the pending state into the state flag.
-/

section Move
variable [FinEnum Λ]

/-- Carry the pending state and `run` one block in direction `d`, then follow them. -/
def carry (d : ℤ) : FProg Fl := (all fun q ↦ hop (.next q) d) ⨾ hop .run d ⨾ .shift d

theorem carry_den {d : ℤ} (hd : d ≠ 0) (q : Λ) (T : Tape Γ) :
    (carry d).den (tapeSet T ∪ here [.next q, .run]) =
      some ((fun x ↦ (x.1 + d, x.2)) ⁻¹' tapeSet T ∪ here [.next q, .run]) := by
  rw [carry, den_seq, den_all (fun q ↦ hop (Flag.next q) d) q (den_hop hd (by mem)) fun q' h ↦
      ⟨den_when_off (by mem), den_when_off (by mem)⟩, Option.bind_some, den_seq,
    den_hop hd (by mem), Option.bind_some, den_shift]
  congr 1; flags

/-- Phase 3: move. -/
def move : FProg Fl := .when .left (carry (-1)) ⨾ .when .right (carry 1)

theorem move_den_stay (T : Tape Γ) (L : List Fl) (hl : .left ∉ L) (hr : .right ∉ L) :
    move.den (tapeSet T ∪ here L) = some (tapeSet T ∪ here L) := by
  rw [move, den_seq, den_when_off (by mem), Option.bind_some, den_when_off (by mem)]

theorem move_den (d : Dir) (q : Λ) (T : Tape Γ) :
    move.den (tapeSet T ∪ here [.dir d, .next q, .run]) =
      some (tapeSet (T.move d) ∪ here [.next q, .run]) := by
  cases d <;> simp only [Flag.dir]
  · rw [move, den_seq, den_when_on (by mem) (by
        rw [show (tapeSet T ∪ here [.left, .next q, .run]) \ {(0, .left)} =
          tapeSet T ∪ here [.next q, .run] by flags]
        exact carry_den (by simp) q T) (by mem), Option.bind_some, den_when_off (by mem)]
    congr 2; ext ⟨j, f⟩; simp [tapeSet, symFlags, Tape.move_left_nth, sub_eq_add_neg]
  · rw [move, den_seq, den_when_off (by mem), Option.bind_some, den_when_on (by mem) (by
        rw [show (tapeSet T ∪ here [.right, .next q, .run]) \ {(0, .right)} =
          tapeSet T ∪ here [.next q, .run] by flags]
        exact carry_den (by simp) q T) (by mem)]
    congr 2; ext ⟨j, f⟩; simp [tapeSet, symFlags, Tape.move_right_nth]

/-- Phase 4: the pending state becomes the state. -/
def commit : FProg Fl := all fun q ↦ .when (.next q) (.set (.state q))

theorem commit_den (q : Λ) (T : Tape Γ) :
    commit.den (tapeSet T ∪ here [.next q, .run]) = some (tapeSet T ∪ here [.state q, .run]) := by
  refine den_all _ q (den_when_on (by mem) ?_ (by mem)) fun q' h ↦ ⟨den_when_off (by mem),
    den_when_off (by mem)⟩
  rw [den_set]; congr 1; flags

end Move

/-! ## One step

Chain the four phases. There are three cases, according to the transition `M q T.head`:

* none (the machine halts): the symbol is written back, nothing moves, no state is committed. The
  result is the bare tape `T` with no `run` flag, so the main loop stops.
* write `b`: flush writes `b`, nothing moves, and commit raises `state q'` and `run`.
* move `d`: flush writes back the old symbol, the move shifts everything, and commit raises
  `state q'` and `run` in the new block.
-/

variable [Inhabited Λ] [FinEnum Γ] [FinEnum Λ] (M : TM0.Machine Γ Λ)

/-- One TM step. -/
def stepProg : FProg Fl := dispatch M ⨾ flush ⨾ move ⨾ commit

/-- **Layer B.** One run of `stepProg` performs one TM step: if the machine halts, the state
flag is gone and the tape unchanged; otherwise the new configuration, with `run` raised. -/
theorem step_den (c : TM0.Cfg Γ Λ) :
    (stepProg M).den (cfgSet c) =
      some ((TM0.step M c).elim (tapeSet c.Tape)
        fun c' ↦ tapeSet c'.Tape ∪ here [.state c'.q, .run]) := by
  obtain ⟨q, T⟩ := c
  rw [stepProg, cfgSet, den_seq, dispatch_den, Option.bind_some, den_seq]
  simp only [TM0.step]
  rcases h : M q T.head with _ | ⟨q', d | b⟩
  · rw [pend, flush_den _ _ _ (by simp) (by simp), Option.bind_some, den_seq,
      move_den_stay _ _ (by simp) (by simp), Option.bind_some, commit,
      den_all_skip _ fun q' ↦ den_when_off (by mem), Tape.write_self]
    simp [here]
  · rw [pend, flush_den _ _ _ (by cases d <;> simp [Flag.dir]) (by cases d <;> simp [Flag.dir]),
      Option.bind_some, den_seq, move_den, Option.bind_some, commit_den, Tape.write_self]
    rfl
  · rw [pend, flush_den _ _ _ (by simp) (by simp), Option.bind_some, den_seq,
      move_den_stay _ _ (by simp) (by simp), Option.bind_some, commit_den]
    rfl

end BF.Exposition
