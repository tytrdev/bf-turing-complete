import BfTuringComplete.Core.Statement
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Layer A: Brainfuck implements flag machines

A *flag machine* has a tape of blocks, and each block holds a set of flags drawn from a finite
type `F`. Its state is therefore a set `P : Set (ℤ × F)` of (block, flag) pairs, relative to the
block under the head. It has four instructions: set a flag, clear a flag, shift the head by whole
blocks, and `when f p`, which runs `p` once if flag `f` is set (clearing `f` first).

Brainfuck implements this directly: block `j` is `card F` consecutive cells, the cell for flag `f`
holds 1 or 0, `set` is `[-]+`, `clr` is `[-]` (both correct whatever the cell held), and
`when f p` is the loop `[ [-] p ]` on `f`'s cell. The single theorem `compile_spec` says compiled
code does to the tape what the flag program does to the flag set.
-/

noncomputable section
namespace BF.Elegant
open Turing StateTransition Relation Classical Fintype

/-! ## Running code -/

/-- Code `p` takes tape `t` to tape `u`, whatever code follows it. -/
def Runs (p : Program) (t u : Tape Cell) : Prop := ∀ k, Reaches step ⟨p ++ k, t⟩ ⟨k, u⟩

variable {p q B : Program} {t u v : Tape Cell}

theorem Runs.nil : Runs [] t t := fun _ ↦ .refl

theorem Runs.seq (h : Runs p t u) (g : Runs q u v) : Runs (p ++ q) t v := fun k ↦ by
  rw [List.append_assoc]; exact (h _).trans (g k)

theorem Runs.cons {c : Stmt} (h : ∀ k, step ⟨c :: k, t⟩ = some ⟨k, u⟩) (g : Runs p u v) :
    Runs (c :: p) t v := fun k ↦ .head (h _) (g k)

/-- A loop whose head cell is zero is skipped. -/
theorem Runs.loopSkip (h : t.head = 0) : Runs [.loop B] t t :=
  fun _ ↦ .single (by simp [step, h])

/-- A loop whose body runs once and leaves the head cell zero. -/
theorem Runs.loopOnce (h : t.head ≠ 0) (g : Runs B t u) (h' : u.head = 0) : Runs [.loop B] t u :=
  fun k ↦ .head (b := ⟨B ++ .loop B :: k, t⟩) (by simp [step, h]) ((g _).trans ((Runs.loopSkip h') k))

/-- `[-]` clears the head cell, whatever it holds. -/
theorem Runs.clear (t : Tape Cell) : Runs [.loop [.dec]] t (t.write 0) := by
  suffices ∀ n (t : Tape Cell), t.head.val = n → Runs [.loop [.dec]] t (t.write 0) from this _ t rfl
  intro n
  induction n with
  | zero =>
    intro t h
    have h0 : t.head = 0 := Fin.ext h
    rw [← h0, Tape.write_self]; exact Runs.loopSkip h0
  | succ n ih =>
    intro t h
    have hne : t.head ≠ 0 := fun h0 ↦ by simp [h0] at h
    have := ih (t.write (t.head - 1)) (by
      show (t.head - 1).val = n; rw [Fin.coe_sub]; have := t.head.isLt; simp; omega)
    exact fun k ↦ .head (b := ⟨.dec :: .loop [.dec] :: k, t⟩) (by simp [step, hne])
      (.head rfl (this k))

theorem Runs.replicate (c : Stmt) (g : Tape Cell → Tape Cell) (s : ℤ)
    (hc : ∀ k t, step ⟨c :: k, t⟩ = some ⟨k, g t⟩) (hg : ∀ t i, (g t).nth i = t.nth (i + s)) :
    ∀ (n : ℕ) (t : Tape Cell), ∃ u, Runs (.replicate n c) t u ∧ ∀ i, u.nth i = t.nth (i + n * s)
  | 0, t => ⟨t, Runs.nil, by simp⟩
  | n + 1, t => by
    obtain ⟨u, h, e⟩ := Runs.replicate c g s hc hg n (g t)
    exact ⟨u, Runs.cons (hc · t) h, fun i ↦ by rw [e, hg]; congr 1; push_cast; ring⟩

/-- Move the head `x` cells (right if positive). -/
def mv (x : ℤ) : Program :=
  if 0 ≤ x then .replicate x.toNat .right else .replicate (-x).toNat .left

theorem Runs.mv (x : ℤ) (t : Tape Cell) : ∃ u, Runs (mv x) t u ∧ ∀ i, u.nth i = t.nth (i + x) := by
  unfold BF.Elegant.mv; split_ifs
  · obtain ⟨u, r, e⟩ := Runs.replicate .right (·.move .right) 1 (fun _ _ ↦ rfl) (by simp) x.toNat t
    exact ⟨u, r, fun i ↦ by rw [e]; congr 1; omega⟩
  · obtain ⟨u, r, e⟩ := Runs.replicate .left (·.move .left) (-1) (fun _ _ ↦ rfl)
      (by simp [sub_eq_add_neg]) (-x).toNat t
    exact ⟨u, r, fun i ↦ by rw [e]; congr 1; omega⟩

/-! ## Flag sets on the tape -/

variable {F : Type*} [Fintype F]

/-- The cell of flag `f` within its block. -/
def pos (f : F) : ℕ := equivFin F f

theorem pos_lt (f : F) : pos f < card F := (equivFin F f).isLt

/-- The only arithmetic in the development: cell `card F * j + pos g` is the cell of `f` in block
0 exactly when `j = 0` and `g = f`. -/
theorem cell_eq {j : ℤ} {f g : F} : (card F : ℤ) * j + pos g - pos f = 0 ↔ j = 0 ∧ g = f := by
  have hf := pos_lt f; have hg := pos_lt g
  constructor
  · intro h
    have hj : j = 0 := by
      rcases lt_trichotomy j 0 with hj | hj | hj
      · nlinarith
      · exact hj
      · nlinarith
    subst hj
    rw [mul_zero, zero_add, sub_eq_zero, Nat.cast_inj] at h
    exact ⟨rfl, (equivFin F).injective (Fin.ext h)⟩
  · rintro ⟨rfl, rfl⟩; simp

/-- Tape `t` stores flag set `P`, with the head `b` cells into block 0. -/
def Holds (b : ℤ) (P : Set (ℤ × F)) (t : Tape Cell) : Prop :=
  ∀ j f, t.nth (card F * j + pos f - b) = if (j, f) ∈ P then 1 else 0

variable {P Q : Set (ℤ × F)}

theorem Holds.mv {b : ℤ} (h : Holds b P t) (x : ℤ) : ∃ u, Holds (b + x) P u ∧ Runs (mv x) t u := by
  obtain ⟨u, r, e⟩ := Runs.mv x t
  exact ⟨u, fun j f ↦ by rw [e, ← h j f]; congr 1; ring, r⟩

theorem Holds.head {f : F} (h : Holds (pos f) P t) : t.head = if (0, f) ∈ P then 1 else 0 := by
  simpa using h 0 f

/-- Writing `f`'s cell changes exactly the membership of `(0, f)`. -/
theorem Holds.write {f : F} (h : Holds (pos f) P t) (hQ : ∀ x, x ≠ (0, f) → (x ∈ Q ↔ x ∈ P)) :
    Holds (pos f) Q (t.write (if (0, f) ∈ Q then 1 else 0)) := fun j g ↦ by
  rw [Tape.write_nth]
  by_cases hc : (card F : ℤ) * j + pos g - pos f = 0
  · obtain ⟨rfl, rfl⟩ := cell_eq.1 hc; simp
  · rw [if_neg hc, h j g, hQ (j, g) fun e ↦ hc (cell_eq.2 (by simpa using e))]

/-- Code run on `f`'s cell: move there, run `c`, move back. -/
def atFlag (f : F) (c : Program) : Program := mv (pos f) ++ c ++ mv (-pos f)

theorem Holds.atFlag {f : F} {c : Program} (h : Holds 0 P t)
    (hc : ∀ t, Holds (pos f) P t → ∃ u, Holds (pos f) Q u ∧ Runs c t u) :
    ∃ u, Holds 0 Q u ∧ Runs (atFlag f c) t u := by
  obtain ⟨t₁, h₁, r₁⟩ := h.mv (pos f)
  obtain ⟨t₂, h₂, r₂⟩ := hc t₁ (by simpa using h₁)
  obtain ⟨t₃, h₃, r₃⟩ := h₂.mv (-pos f)
  exact ⟨t₃, by simpa using h₃, (r₁.seq r₂).seq r₃⟩

/-! ## Flag programs -/

/-- Flag programs over the flag type `F`. -/
inductive FProg (F : Type*)
  | skip
  | set (f : F)
  | clr (f : F)
  | shift (d : ℤ)
  | seq (p q : FProg F)
  | when (f : F) (p : FProg F)

@[inherit_doc] infixr:60 " ⨾ " => FProg.seq

namespace FProg

/-- What a flag program does to the flag set. `when f p` clears `f` and runs `p` if `f` is set;
it fails (`none`) if `p` sets `f` again, since the Brainfuck loop would then repeat. -/
def den : FProg F → Set (ℤ × F) → Option (Set (ℤ × F))
  | skip, P => some P
  | set f, P => some (insert (0, f) P)
  | clr f, P => some (P \ {(0, f)})
  | shift d, P => some ((fun x ↦ (x.1 + d, x.2)) ⁻¹' P)
  | p ⨾ q, P => (p.den P).bind q.den
  | when f p, P =>
    if (0, f) ∈ P then (p.den (P \ {(0, f)})).bind fun Q ↦ if (0, f) ∈ Q then none else some Q
    else some P

@[simp] theorem den_skip (P : Set (ℤ × F)) : (skip : FProg F).den P = some P := rfl
@[simp] theorem den_set (f : F) (P : Set (ℤ × F)) : (set f).den P = some (insert (0, f) P) := rfl
@[simp] theorem den_clr (f : F) (P : Set (ℤ × F)) : (clr f).den P = some (P \ {(0, f)}) := rfl
@[simp] theorem den_shift (d : ℤ) (P : Set (ℤ × F)) :
    (shift d).den P = some ((fun x ↦ (x.1 + d, x.2)) ⁻¹' P) := rfl
@[simp] theorem den_seq (p q : FProg F) (P : Set (ℤ × F)) : (p ⨾ q).den P = (p.den P).bind q.den :=
  rfl

/-- The Brainfuck code of a flag program. -/
def compile : FProg F → Program
  | skip => []
  | set f => atFlag f [.loop [.dec], .inc]
  | clr f => atFlag f [.loop [.dec]]
  | shift d => mv (card F * d)
  | p ⨾ q => p.compile ++ q.compile
  | when f p => atFlag f [.loop (.loop [.dec] :: mv (-pos f) ++ p.compile ++ mv (pos f))]

/-- **Layer A.** Compiled code does to the tape what the program does to the flag set. -/
theorem compile_spec : ∀ (p : FProg F) {P Q : Set (ℤ × F)} {t : Tape Cell},
    p.den P = some Q → Holds 0 P t → ∃ u, Holds 0 Q u ∧ Runs p.compile t u
  | skip, P, Q, t, e, h => by cases e; exact ⟨t, h, Runs.nil⟩
  | set f, P, Q, t, e, h => by
    cases e
    refine h.atFlag fun t ht ↦ ⟨_, ht.write (Q := insert (0, f) P) fun x hx ↦ by simp [hx], ?_⟩
    rw [if_pos (by simp)]
    exact (Runs.clear t).seq (Runs.cons (fun _ ↦ rfl) Runs.nil)
  | clr f, P, Q, t, e, h => by
    cases e
    refine h.atFlag fun t ht ↦ ⟨_, ht.write (Q := P \ {(0, f)}) fun x hx ↦ by simp [hx], ?_⟩
    rw [if_neg (by simp)]
    exact Runs.clear t
  | shift d, P, Q, t, e, h => by
    cases e
    obtain ⟨u, hu, r⟩ := h.mv (card F * d)
    exact ⟨u, fun j f ↦ by simp only [Set.mem_preimage]; rw [← hu (j + d) f]; congr 1; ring, r⟩
  | p ⨾ q, P, Q, t, e, h => by
    obtain ⟨R, e₁, e₂⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨u, hu, r⟩ := compile_spec p e₁ h
    obtain ⟨v, hv, r'⟩ := compile_spec q e₂ hu
    exact ⟨v, hv, r.seq r'⟩
  | when f p, P, Q, t, e, h => by
    refine h.atFlag fun t ht ↦ ?_
    unfold den at e
    split_ifs at e with hf
    · obtain ⟨R, e₁, e₂⟩ := Option.bind_eq_some_iff.1 e
      split_ifs at e₂ with hR
      cases e₂
      have hc := ht.write (Q := P \ {(0, f)}) fun x hx ↦ by simp [hx]
      rw [if_neg (by simp)] at hc
      obtain ⟨t₁, h₁, r₁⟩ := hc.mv (-pos f)
      obtain ⟨t₂, h₂, r₂⟩ := compile_spec p e₁ (by simpa using h₁)
      obtain ⟨t₃, h₃, r₃⟩ := h₂.mv (pos f)
      have h₃' : Holds (pos f) Q t₃ := by simpa using h₃
      exact ⟨t₃, h₃', Runs.loopOnce (by simp [ht.head, hf])
        ((Runs.clear t).seq ((r₁.seq r₂).seq r₃)) (by simp [h₃'.head, hR])⟩
    · cases e; exact ⟨t, ht, Runs.loopSkip (by simp [ht.head, hf])⟩

end FProg
end BF.Elegant
