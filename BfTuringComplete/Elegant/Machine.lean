import BfTuringComplete.Elegant.Flags
import Mathlib.Data.Fintype.Sum

/-!
# Layer B: flag machines implement TM0

Each TM cell becomes a block of flags. `sym a` records the cell's symbol (the blank has no flag,
so blank cells are all zero) and `state q` marks the head. One TM step is a flag program in four
phases:

1. **dispatch** on the state and symbol under the head, consuming both and raising the
   transition's *pending* flags (`write a`, `next q`, `left`/`right`, `run`);
2. **flush** the pending symbol into the cell;
3. **move**: carry `next q` and `run` to the neighbouring block and shift there;
4. **commit** the pending state.

The pending flags keep a phase from reacting to flags raised earlier in the same phase.
-/

noncomputable section
namespace BF.Elegant
open Turing Classical Fintype FProg

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

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Fintype Γ] [Fintype Λ]

local notation "Fl" => Flag Γ Λ

/-- Flags embed into a sum of finite types, so there are finitely many. -/
def Flag.code : Fl → Γ ⊕ Λ ⊕ Γ ⊕ Λ ⊕ Fin 4
  | .sym a => .inl a
  | .state q => .inr (.inl q)
  | .write a => .inr (.inr (.inl a))
  | .next q => .inr (.inr (.inr (.inl q)))
  | .blank => .inr (.inr (.inr (.inr 0)))
  | .left => .inr (.inr (.inr (.inr 1)))
  | .right => .inr (.inr (.inr (.inr 2)))
  | .run => .inr (.inr (.inr (.inr 3)))

instance : Fintype Fl :=
  have : Finite Fl := Finite.of_injective Flag.code fun x y h ↦ by
    cases x <;> cases y <;> first | rfl | simp_all [Flag.code] | (simp [Flag.code] at h; omega)
  Fintype.ofFinite _

instance : Nonempty Fl := ⟨.run⟩

/-! ## Running one program per element of a finite type -/

/-- Run `g x` for every `x`, in some fixed order. -/
def all {α : Type*} [Fintype α] (g : α → FProg Fl) : FProg Fl :=
  (Finset.univ : Finset α).toList.foldr (fun x p ↦ g x ⨾ p) .skip

theorem den_foldr_skip {α : Type*} (L : List α) (g : α → FProg Fl) {P : Set (ℤ × Fl)}
    (h : ∀ x ∈ L, (g x).den P = some P) : (L.foldr (fun x p ↦ g x ⨾ p) .skip).den P = some P := by
  induction L with
  | nil => rfl
  | cons x L ih => simp [den, h x (by simp), ih fun y hy ↦ h y (by simp [hy])]

theorem den_foldr_one {α : Type*} (L : List α) (hL : L.Nodup) (g : α → FProg Fl) (a : α)
    (ha : a ∈ L) {P Q : Set (ℤ × Fl)} (hA : (g a).den P = some Q)
    (h : ∀ x, x ≠ a → (g x).den P = some P ∧ (g x).den Q = some Q) :
    (L.foldr (fun x p ↦ g x ⨾ p) .skip).den P = some Q := by
  induction L with
  | nil => simp at ha
  | cons x L ih =>
    obtain ⟨hx, hL⟩ := List.nodup_cons.1 hL
    by_cases e : x = a
    · subst e
      simp [den, hA, den_foldr_skip L g fun y hy ↦ (h y fun e ↦ hx (e ▸ hy)).2]
    · simp [den, (h x e).1, ih hL (by simpa [Ne.symm e] using ha)]

/-- If `g x` changes nothing for every `x`, neither does `all g`. -/
theorem den_all_skip {α : Type*} [Fintype α] (g : α → FProg Fl) {P : Set (ℤ × Fl)}
    (h : ∀ x, (g x).den P = some P) : (all g).den P = some P :=
  den_foldr_skip _ g fun x _ ↦ h x

/-- If only `g a` does anything, `all g` does what `g a` does. -/
theorem den_all {α : Type*} [Fintype α] (g : α → FProg Fl) (a : α) {P Q : Set (ℤ × Fl)}
    (hA : (g a).den P = some Q) (h : ∀ x, x ≠ a → (g x).den P = some P ∧ (g x).den Q = some Q) :
    (all g).den P = some Q :=
  den_foldr_one _ (Finset.nodup_toList _) g a (by simp) hA h

theorem den_when_off {f : Fl} {p : FProg Fl} {P : Set (ℤ × Fl)} (h : (0, f) ∉ P) :
    (when f p).den P = some P := by simp [den, h]

theorem den_when_on {f : Fl} {p : FProg Fl} {P Q : Set (ℤ × Fl)} (h : (0, f) ∈ P)
    (hp : p.den (P \ {(0, f)}) = some Q) (hQ : (0, f) ∉ Q) : (when f p).den P = some Q := by
  simp [den, h, hp, hQ]

/-! ## The step program -/

/-- The flags `L`, in the block under the head. -/
def here (L : List Fl) : Set (ℤ × Fl) := {x | x.1 = 0 ∧ x.2 ∈ L}

/-- Raise each flag of `L` in the block under the head. -/
def raise (L : List Fl) : FProg Fl := L.foldr (fun f p ↦ .set f ⨾ p) .skip

theorem den_raise (L : List Fl) (P : Set (ℤ × Fl)) : (raise L).den P = some (P ∪ here L) := by
  induction L generalizing P with
  | nil => simp [raise, den, here]
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

variable (M : TM0.Machine Γ Λ)

/-- Phase 1: consume the state and the symbol under the head, raising the pending flags.
The scratch flag `blank` catches the case that no symbol flag is set. -/
def dispatch : FProg Fl := all fun q ↦ .when (.state q) <|
  .set .blank ⨾ (all fun a ↦ .when (.sym a) (.clr .blank ⨾ raise (pend (M q a) a))) ⨾
    .when .blank (raise (pend (M q default) default))

/-- Write symbol `a` into the current block (the blank needs no flag). -/
def put (a : Γ) : FProg Fl := if a = default then .skip else .set (.sym a)

/-- Phase 2: turn the pending symbol into the cell's symbol. -/
def flush : FProg Fl := all fun a ↦ .when (.write a) (put a)

/-- If `f` is raised here, move it to the block `d` away. -/
def hop (f : Fl) (d : ℤ) : FProg Fl := .when f (.shift d ⨾ .set f ⨾ .shift (-d))

/-- Carry the pending state and `run` one block in direction `d`, then follow them. -/
def carry (d : ℤ) : FProg Fl := (all fun q ↦ hop (.next q) d) ⨾ hop .run d ⨾ .shift d

/-- Phase 3: move. -/
def move : FProg Fl := .when .left (carry (-1)) ⨾ .when .right (carry 1)

/-- Phase 4: the pending state becomes the state. -/
def commit : FProg Fl := all fun q ↦ .when (.next q) (.set (.state q))

/-- One TM step. -/
def stepProg : FProg Fl := dispatch M ⨾ flush ⨾ move ⨾ commit

/-! ## The flag sets of TM configurations -/

/-- The flags of a cell holding `a`: its symbol flag, unless `a` is the blank. -/
def symFlags (a : Γ) (f : Fl) : Prop := f = .sym a ∧ a ≠ default

/-- The symbols of tape `T`, as flags. -/
def tapeSet (T : Tape Γ) : Set (ℤ × Fl) := {x | symFlags (T.nth x.1) x.2}

set_option hygiene false in
/-- Membership goals about flag sets: unfold, then close by logic. -/
macro "mem" : tactic => `(tactic| (simp [tapeSet, symFlags, here, Tape.write_nth, Flag.dir] <;> aesop))

set_option hygiene false in
/-- Equality of flag sets, by cases on the flag. -/
macro "flags" : tactic => `(tactic| (ext ⟨j, f⟩; cases f <;> mem))

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
  · rw [den_all _ T.head (den_when_on (by mem) (by rw [den_seq, den_clr, Option.bind_some, den_raise])
        (by mem)) fun a h ↦ ⟨den_when_off (by mem), den_when_off (by mem)⟩,
      Option.bind_some, den_when_off (by mem)]
    congr 2; flags

theorem flush_den (T : Tape Γ) (b : Γ) (L : List Fl) (hL : ∀ c, .write c ∉ L)
    (hs : ∀ c, .sym c ∉ L) :
    flush.den (tapeSet (T.write default) ∪ here (.write b :: L)) = some (tapeSet (T.write b) ∪ here L) := by
  refine den_all _ b (den_when_on (by mem) ?_ (by mem)) fun c h ↦ ⟨den_when_off (by mem), den_when_off (by mem)⟩
  unfold put; split_ifs with hb
  · subst hb; rw [den_skip]; congr 1; flags
  · rw [den_set]; congr 1; flags

theorem den_hop {f : Fl} {d : ℤ} (hd : d ≠ 0) {P : Set (ℤ × Fl)} (h : (0, f) ∈ P) :
    (hop f d).den P = some (insert (d, f) (P \ {(0, f)})) := by
  refine den_when_on h ?_ (by simp [Ne.symm hd])
  simp only [den_seq, den_shift, den_set, Option.bind_some, Option.some.injEq]
  ext ⟨j, g⟩
  simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff,
    Prod.mk.injEq, neg_add_cancel_right]
  constructor
  · rintro (⟨h1, rfl⟩ | h1)
    · left; exact ⟨by omega, rfl⟩
    · right; exact h1
  · rintro (⟨rfl, rfl⟩ | h1)
    · left; simp
    · right; exact h1

theorem carry_den {d : ℤ} (hd : d ≠ 0) (q : Λ) (T : Tape Γ) :
    (carry d).den (tapeSet T ∪ here [.next q, .run]) =
      some ((fun x ↦ (x.1 + d, x.2)) ⁻¹' tapeSet T ∪ here [.next q, .run]) := by
  rw [carry, den_seq, den_all (fun q ↦ hop (.next q) d) q (den_hop hd (by mem)) fun q' h ↦
      ⟨den_when_off (by mem), den_when_off (by mem)⟩, Option.bind_some, den_seq,
    den_hop hd (by mem), Option.bind_some, den_shift]
  congr 1; flags

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

theorem commit_den (q : Λ) (T : Tape Γ) :
    commit.den (tapeSet T ∪ here [.next q, .run]) = some (tapeSet T ∪ here [.state q, .run]) := by
  refine den_all _ q (den_when_on (by mem) ?_ (by mem)) fun q' h ↦ ⟨den_when_off (by mem),
    den_when_off (by mem)⟩
  rw [den_set]; congr 1; flags

/-! ## One step -/

/-- The flags of a TM configuration: its tape, and its state at the head. -/
def cfgSet (c : TM0.Cfg Γ Λ) : Set (ℤ × Fl) := tapeSet c.Tape ∪ here [.state c.q]

/-- **Layer B.** One run of `stepProg` performs one TM step: if the machine halts, the state
flag is gone and the tape unchanged; otherwise the new configuration, with `run` raised. -/
theorem step_den (c : TM0.Cfg Γ Λ) :
    (stepProg M).den (cfgSet c) =
      some ((TM0.step M c).elim (tapeSet c.Tape) fun c' ↦ tapeSet c'.Tape ∪ here [.state c'.q, .run]) := by
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

end BF.Elegant
