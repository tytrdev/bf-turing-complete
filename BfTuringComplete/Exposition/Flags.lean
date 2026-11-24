import BfTuringComplete.Core.Statement
import Mathlib.Data.FinEnum
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

namespace BF.Exposition
open Turing StateTransition Relation FinEnum
attribute [local instance] Classical.propDecidable

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
  fun k ↦ .head (b := ⟨B ++ .loop B :: k, t⟩) (by simp [step, h])
    ((g _).trans ((Runs.loopSkip h') k))

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
      change (t.head - 1).val = n; rw [Fin.val_sub]; have := t.head.isLt; simp; omega)
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
  unfold BF.Exposition.mv; split_ifs
  · obtain ⟨u, r, e⟩ := Runs.replicate .right (·.move .right) 1 (fun _ _ ↦ rfl) (by simp) x.toNat t
    exact ⟨u, r, fun i ↦ by rw [e]; congr 1; omega⟩
  · obtain ⟨u, r, e⟩ := Runs.replicate .left (·.move .left) (-1) (fun _ _ ↦ rfl)
      (by simp [sub_eq_add_neg]) (-x).toNat t
    exact ⟨u, r, fun i ↦ by rw [e]; congr 1; omega⟩

/-! ## Flag programs -/

section Programs
variable {F : Type*}


/-- Flag programs over the flag type `F`. -/
inductive FProg (F : Type*)
  | skip
  | set (f : F)
  | clr (f : F)
  | shift (d : ℤ)
  | seq (p q : FProg F)
  | when (f : F) (p : FProg F)

/-- `p ⨾ q`: run `p`, then `q`. -/
infixr:60 " ⨾ " => FProg.seq

namespace FProg

/-- What a flag program does to the flag set. `when f p` clears `f` and runs `p` if `f` is set;
it fails (`none`) if `p` sets `f` again, since the Brainfuck loop would then repeat. -/
noncomputable def den : FProg F → Set (ℤ × F) → Option (Set (ℤ × F))
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

/-! ### Derived forms -/

/-- Run `g x` for every `x`, in some fixed order. -/
def all {α : Type*} [FinEnum α] (g : α → FProg F) : FProg F :=
  (toList α).foldr (fun x p ↦ g x ⨾ p) .skip

theorem den_foldr_skip {α : Type*} (L : List α) (g : α → FProg F) {P : Set (ℤ × F)}
    (h : ∀ x ∈ L, (g x).den P = some P) : (L.foldr (fun x p ↦ g x ⨾ p) .skip).den P = some P := by
  induction L with
  | nil => rfl
  | cons x L ih => simp [h x (by simp), ih fun y hy ↦ h y (by simp [hy])]

theorem den_foldr_one {α : Type*} (L : List α) (hL : L.Nodup) (g : α → FProg F) (a : α)
    (ha : a ∈ L) {P Q : Set (ℤ × F)} (hA : (g a).den P = some Q)
    (h : ∀ x, x ≠ a → (g x).den P = some P ∧ (g x).den Q = some Q) :
    (L.foldr (fun x p ↦ g x ⨾ p) .skip).den P = some Q := by
  induction L with
  | nil => simp at ha
  | cons x L ih =>
    obtain ⟨hx, hL⟩ := List.nodup_cons.1 hL
    by_cases e : x = a
    · subst e
      simp [hA, den_foldr_skip L g fun y hy ↦ (h y fun e ↦ hx (e ▸ hy)).2]
    · simp [(h x e).1, ih hL (by simpa [Ne.symm e] using ha)]

/-- If `g x` changes nothing for every `x`, neither does `all g`. -/
theorem den_all_skip {α : Type*} [FinEnum α] (g : α → FProg F) {P : Set (ℤ × F)}
    (h : ∀ x, (g x).den P = some P) : (all g).den P = some P :=
  den_foldr_skip _ g fun x _ ↦ h x

/-- If only `g a` does anything, `all g` does what `g a` does. -/
theorem den_all {α : Type*} [FinEnum α] (g : α → FProg F) (a : α) {P Q : Set (ℤ × F)}
    (hA : (g a).den P = some Q) (h : ∀ x, x ≠ a → (g x).den P = some P ∧ (g x).den Q = some Q) :
    (all g).den P = some Q :=
  den_foldr_one _ nodup_toList g a (mem_toList a) hA h

theorem den_when_off {f : F} {p : FProg F} {P : Set (ℤ × F)} (h : (0, f) ∉ P) :
    (when f p).den P = some P := by simp [den, h]

theorem den_when_on {f : F} {p : FProg F} {P Q : Set (ℤ × F)} (h : (0, f) ∈ P)
    (hp : p.den (P \ {(0, f)}) = some Q) (hQ : (0, f) ∉ Q) : (when f p).den P = some Q := by
  simp [den, h, hp, hQ]

/-- If `f` is raised here, move it to the block `d` away. -/
def hop (f : F) (d : ℤ) : FProg F := .when f (.shift d ⨾ .set f ⨾ .shift (-d))

theorem den_hop {f : F} {d : ℤ} (hd : d ≠ 0) {P : Set (ℤ × F)} (h : (0, f) ∈ P) :
    (hop f d).den P = some (insert (d, f) (P \ {(0, f)})) := by
  refine den_when_on h ?_ (by simp [Ne.symm hd])
  simp only [den_seq, den_shift, den_set, Option.bind_some, Option.some.injEq]
  ext ⟨j, g⟩
  simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff,
    Prod.mk.injEq, neg_add_cancel_right]
  constructor
  · rintro (⟨h1, rfl⟩ | h1)
    · left; exact ⟨by omega, rfl⟩
    · right; exact h1
  · rintro (⟨rfl, rfl⟩ | h1)
    · left; simp
    · right; exact h1

end FProg
end Programs

/-! ## Flag sets on the tape -/

variable {F : Type*} [FinEnum F]

/-- The cell of flag `f` within its block. -/
def pos (f : F) : ℕ := equiv f

theorem pos_lt (f : F) : pos f < card F := (equiv f).isLt

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
    exact ⟨rfl, (equiv (α := F)).injective (Fin.ext h)⟩
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
  · rw [ite_eq_right hc, h j g, hQ (j, g) fun e ↦ hc (cell_eq.2 (by simpa using e))]

/-- Code run on `f`'s cell: move there, run `c`, move back. -/
def atFlag (f : F) (c : Program) : Program := mv (pos f) ++ c ++ mv (-pos f)

theorem Holds.atFlag {f : F} {c : Program} (h : Holds 0 P t)
    (hc : ∀ t, Holds (pos f) P t → ∃ u, Holds (pos f) Q u ∧ Runs c t u) :
    ∃ u, Holds 0 Q u ∧ Runs (atFlag f c) t u := by
  obtain ⟨t₁, h₁, r₁⟩ := h.mv (pos f)
  obtain ⟨t₂, h₂, r₂⟩ := hc t₁ (by simpa using h₁)
  obtain ⟨t₃, h₃, r₃⟩ := h₂.mv (-pos f)
  exact ⟨t₃, by simpa using h₃, (r₁.seq r₂).seq r₃⟩

/-! ## Tapes of blocks

A tape of symbols becomes a tape of cells by writing each symbol as the block of its flags. -/

/-- The cells of a block whose raised flags are `S`. -/
def block (S : F → Prop) [DecidablePred S] : List Cell :=
  (List.finRange (card F)).map fun i ↦ if S ((equiv (α := F)).symm i) then 1 else 0

theorem block_length (S : F → Prop) [DecidablePred S] : (block S).length = card F := by simp [block]

theorem block_getI (S : F → Prop) [DecidablePred S] (f : F) : (block S).getI (pos f) = if S f then 1 else 0 := by
  rw [block, List.getI_eq_getElem _ (by simpa using pos_lt f)]; simp [pos]

theorem block_empty : block (fun _ : F ↦ False) = List.replicate (card F) default := by
  simp [block, List.map_const', default]

theorem card_pos [Nonempty F] : 0 < card F := (equiv (Classical.arbitrary F)).pos

/-- Cell `card F * j + pos f` is flag `f` of block `j`, and every cell is one of these. -/
theorem cell_split [Nonempty F] (i : ℕ) : ∃ (j : ℕ) (f : F), i = card F * j + pos f :=
  ⟨i / card F, (equiv (α := F)).symm ⟨i % card F, Nat.mod_lt _ card_pos⟩,
    by simp [pos, Nat.div_add_mod]⟩

variable {α : Type*} [Inhabited α] (cells : α → F → Prop) [∀ a, DecidablePred (cells a)]

theorem flatMap_block_getI (hd : ∀ f, ¬cells default f) (l : List α) (j : ℕ) (f : F) :
    (l.flatMap (fun a ↦ block (cells a))).getI (card F * j + pos f) =
      if cells (l.getI j) f then 1 else 0 := by
  induction l generalizing j with
  | nil =>
    rw [List.flatMap_nil, List.getI_nil, List.getI_nil]
    simp [hd]
  | cons a l ih =>
    rw [List.flatMap_cons]
    rcases j with _ | j
    · rw [List.getI_append _ _ _ (by simpa [block_length] using pos_lt f), mul_zero, zero_add,
        block_getI, List.getI_cons_zero]
    · rw [List.getI_append_right _ _ _ (by simp [block_length]; nlinarith [pos_lt f]),
        block_length, show card F * (j + 1) + pos f - card F = card F * j + pos f by
          rw [Nat.mul_succ]; omega, ih, List.getI_cons_succ]

theorem mk₁_nth (l : List α) (k : ℕ) : (Tape.mk₁ l).nth k = l.getI k := by
  simp [Tape.mk₁, Tape.mk₂, ListBlank.nth_mk]

theorem mk₁_nth_neg (l : List α) {i : ℤ} (hi : i < 0) : (Tape.mk₁ l).nth i = default := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = Int.negSucc k := ⟨(-i - 1).toNat, by rw [Int.negSucc_eq]; omega⟩
  rfl

/-- The encoded input tape stores the flags of the input. -/
theorem holds_mk₁ (hd : ∀ f, ¬cells default f) (l : List α) :
    Holds 0 {x | cells ((Tape.mk₁ l).nth x.1) x.2} (Tape.mk₁ (l.flatMap (fun a ↦ block (cells a)))) := by
  intro j f
  rw [sub_zero, Set.mem_ofPred_eq]
  rcases lt_or_ge j 0 with hj | hj
  · have : (card F : ℤ) * j + pos f < 0 := by
      nlinarith [pos_lt f, mul_le_mul_of_nonneg_left (show j ≤ -1 by omega)
        (Nat.cast_nonneg (α := ℤ) (card F))]
    simp [mk₁_nth_neg _ this, mk₁_nth_neg _ hj, hd]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    rw [show (card F : ℤ) * k + pos f = ((card F * k + pos f : ℕ) : ℤ) by push_cast; ring,
      mk₁_nth, flatMap_block_getI cells hd, mk₁_nth]
    congr

theorem block_default (hd : ∀ f, ¬cells default f) :
    ∃ n, (fun a ↦ block (cells a)) default = List.replicate n default :=
  ⟨card F, by simp [block, hd, List.map_const', default]⟩

/-- A tape storing the flags of `T` reads, from the head rightwards, as `T` encoded. -/
theorem right₀_eq [Nonempty F] (hd : ∀ f, ¬cells default f) (T : Tape α) (t : Tape Cell)
    (h : Holds 0 {x | cells (T.nth x.1) x.2} t) :
    t.right₀ = T.right₀.flatMap (fun a ↦ block (cells a)) (block_default cells hd) := by
  apply ListBlank.ext
  intro i
  obtain ⟨j, f, rfl⟩ := cell_split (F := F) i
  have key : ∀ L : ListBlank α, (L.flatMap (fun a ↦ block (cells a)) (block_default cells hd)).nth
      (card F * j + pos f) = if cells (L.nth j) f then 1 else 0 := fun L ↦ L.induction_on fun l ↦ by
    simp only [ListBlank.flatMap_mk, ListBlank.nth_mk, flatMap_block_getI cells hd]; congr
  have := h j f
  rw [sub_zero, show (card F : ℤ) * j + pos f = ((card F * j + pos f : ℕ) : ℤ) by push_cast; ring]
    at this
  rw [Tape.right₀_nth, this, key, Tape.right₀_nth, Set.mem_ofPred_eq]
  congr

/-! ## Compiling flag programs -/

namespace FProg

/-- The Brainfuck code of a flag program. -/
def compile : FProg F → Program
  | skip => []
  | set f => atFlag f [.loop [.dec], .inc]
  | clr f => atFlag f [.loop [.dec]]
  | shift d => mv (card F * d)
  | p ⨾ q => p.compile ++ q.compile
  | when f p => atFlag f [.loop (.loop [.dec] :: mv (-pos f) ++ p.compile ++ mv (pos f))]

/-- The Brainfuck loop that `when f p` compiles to, run from `f`'s cell. -/
def loopCode (f : F) (p : FProg F) : Stmt :=
  .loop (.loop [.dec] :: mv (-pos f) ++ p.compile ++ mv (pos f))

theorem compile_when (f : F) (p : FProg F) : (when f p).compile = atFlag f [loopCode f p] := rfl

/-- **Layer A.** Compiled code does to the tape what the program does to the flag set. -/
theorem compile_spec : ∀ (p : FProg F) {P Q : Set (ℤ × F)} {t : Tape Cell},
    p.den P = some Q → Holds 0 P t → ∃ u, Holds 0 Q u ∧ Runs p.compile t u
  | skip, P, Q, t, e, h => by cases e; exact ⟨t, h, Runs.nil⟩
  | set f, P, Q, t, e, h => by
    cases e
    refine h.atFlag fun t ht ↦ ⟨_, ht.write (Q := insert (0, f) P) fun x hx ↦ by simp [hx], ?_⟩
    rw [ite_eq_left (by simp)]
    exact (Runs.clear t).seq (Runs.cons (fun _ ↦ rfl) Runs.nil)
  | clr f, P, Q, t, e, h => by
    cases e
    refine h.atFlag fun t ht ↦ ⟨_, ht.write (Q := P \ {(0, f)}) fun x hx ↦ by simp [hx], ?_⟩
    rw [ite_eq_right (by simp)]
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
      obtain ⟨u, hu, r⟩ := pass p hf e₁ ht
      exact ⟨u, hu, Runs.loopOnce (by simp [ht.head, hf]) r (by simp [hu.head, hR])⟩
    · cases e; exact ⟨t, ht, Runs.loopSkip (by simp [ht.head, hf])⟩
where
  /-- One pass of the loop body: clear `f`, run `p` from the block start, return to `f`. -/
  pass (p : FProg F) {f : F} {P R : Set (ℤ × F)} {t : Tape Cell} (hf : (0, f) ∈ P)
      (e : p.den (P \ {(0, f)}) = some R) (ht : Holds (pos f) P t) :
      ∃ u, Holds (pos f) R u ∧
        Runs (.loop [.dec] :: mv (-pos f) ++ p.compile ++ mv (pos f)) t u := by
    have hc := ht.write (Q := P \ {(0, f)}) fun x hx ↦ by simp [hx]
    rw [ite_eq_right (by simp)] at hc
    obtain ⟨t₁, h₁, r₁⟩ := hc.mv (-pos f)
    obtain ⟨t₂, h₂, r₂⟩ := compile_spec p e (by simpa using h₁)
    obtain ⟨t₃, h₃, r₃⟩ := h₂.mv (pos f)
    exact ⟨t₃, by simpa using h₃, (Runs.clear t).seq ((r₁.seq r₂).seq r₃)⟩

/-- The loop of `when f p` as a `while` loop: if `f` is set, one pass of the body. -/
theorem loop_pass (p : FProg F) {f : F} {P R : Set (ℤ × F)} {t : Tape Cell} (hf : (0, f) ∈ P)
    (e : p.den (P \ {(0, f)}) = some R) (ht : Holds (pos f) P t) (k : Program) :
    ∃ u, Holds (pos f) R u ∧
      TransGen (fun a b ↦ b ∈ step a) ⟨loopCode f p :: k, t⟩ ⟨loopCode f p :: k, u⟩ := by
  obtain ⟨u, hu, r⟩ := compile_spec.pass p hf e ht
  exact ⟨u, hu, .head' (by simp [step, loopCode, ht.head, hf]) (r _)⟩

/-- … and if `f` is clear, the loop ends. -/
theorem loop_exit (p : FProg F) {f : F} {P : Set (ℤ × F)} {t : Tape Cell} (hf : (0, f) ∉ P)
    (ht : Holds (pos f) P t) (k : Program) : Reaches step ⟨loopCode f p :: k, t⟩ ⟨k, t⟩ :=
  .single (by simp [step, loopCode, ht.head, hf])

end FProg
end BF.Exposition
