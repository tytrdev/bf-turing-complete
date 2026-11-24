import BfTuringComplete.Reference.Compile

/-!
# `Runs`: big-step reasoning derived from the small-step semantics

`Runs p t t'` says: whatever code `k` follows, running `p ++ k` from tape `t` reaches
`k` with tape `t'`. It is defined from `step`, so it needs no separate equivalence proof.

Tapes are reasoned about through `Tape.nth : ℤ → Cell` (the tape as a function,
relative to the head), with `Tape.ext_nth` to turn `nth` equalities into tape equalities.
-/

namespace BF

open Turing StateTransition Relation

/-! ## Tapes as functions -/

theorem Tape.ext_nth {t₁ t₂ : Tape Cell} (h : ∀ i, t₁.nth i = t₂.nth i) : t₁ = t₂ := by
  obtain ⟨a₁, L₁, R₁⟩ := t₁
  obtain ⟨a₂, L₂, R₂⟩ := t₂
  have ha := h 0
  have hR : R₁ = R₂ := ListBlank.ext fun n ↦ h ((n + 1 : ℕ) : ℤ)
  have hL : L₁ = L₂ := ListBlank.ext fun n ↦ h (-((n + 1 : ℕ) : ℤ))
  simp_all [Turing.Tape.nth]

/-- Move the head by `o` cells (the tape-level meaning of `mv o`). -/
def moveBy : ℤ → Tape Cell → Tape Cell
  | .ofNat n => (Tape.move .right)^[n]
  | .negSucc n => (Tape.move .left)^[n + 1]

theorem iter_right_nth (n : ℕ) (t : Tape Cell) (i : ℤ) :
    ((Tape.move .right)^[n] t).nth i = t.nth (i + n) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, Tape.move_right_nth]; congr 1; push_cast; omega

theorem iter_left_nth (n : ℕ) (t : Tape Cell) (i : ℤ) :
    ((Tape.move .left)^[n] t).nth i = t.nth (i - n) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, Tape.move_left_nth]; congr 1; push_cast; omega

@[simp] theorem moveBy_nth (o : ℤ) (t : Tape Cell) (i : ℤ) :
    (moveBy o t).nth i = t.nth (i + o) := by
  cases o with
  | ofNat n => simp [moveBy, iter_right_nth]
  | negSucc n => simp only [moveBy, iter_left_nth, Int.negSucc_eq]; congr 1

@[simp] theorem moveBy_moveBy (a b : ℤ) (t : Tape Cell) :
    moveBy a (moveBy b t) = moveBy (a + b) t :=
  Tape.ext_nth fun i ↦ by simp [add_assoc]

@[simp] theorem moveBy_zero (t : Tape Cell) : moveBy 0 t = t := rfl

/-- Apply `f` to the cell at offset `o`; head stays put. -/
def modAt (o : ℤ) (f : Cell → Cell) (t : Tape Cell) : Tape Cell :=
  moveBy (-o) ((moveBy o t).write (f (moveBy o t).head))

@[simp] theorem modAt_nth (o : ℤ) (f : Cell → Cell) (t : Tape Cell) (i : ℤ) :
    (modAt o f t).nth i = if i = o then f (t.nth o) else t.nth i := by
  simp only [modAt, moveBy_nth, Tape.write_nth]
  have : (moveBy o t).head = t.nth o := by simpa using moveBy_nth o t 0
  rw [this]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/-! ## `Runs` -/

/-- Running `p` from tape `t` ends with tape `t'`, whatever code follows. -/
def Runs (p : Program) (t t' : Tape Cell) : Prop :=
  ∀ k, Reaches step ⟨p ++ k, t⟩ ⟨k, t'⟩

theorem Runs.nil (t : Tape Cell) : Runs [] t t := fun _ ↦ ReflTransGen.refl

theorem Runs.append {p q : Program} {t t' t'' : Tape Cell}
    (h₁ : Runs p t t') (h₂ : Runs q t' t'') : Runs (p ++ q) t t'' := fun k ↦ by
  rw [List.append_assoc]; exact (h₁ (q ++ k)).trans (h₂ k)

theorem Runs.eq {p : Program} {t t₁ t₂ : Tape Cell} (h : Runs p t t₁) (e : t₁ = t₂) :
    Runs p t t₂ := e ▸ h

theorem Runs.inc (t : Tape Cell) : Runs [.inc] t (t.write (t.head + 1)) :=
  fun _ ↦ ReflTransGen.single rfl

theorem Runs.dec (t : Tape Cell) : Runs [.dec] t (t.write (t.head - 1)) :=
  fun _ ↦ ReflTransGen.single rfl

theorem Runs.right (t : Tape Cell) : Runs [.right] t (t.move .right) :=
  fun _ ↦ ReflTransGen.single rfl

theorem Runs.left (t : Tape Cell) : Runs [.left] t (t.move .left) :=
  fun _ ↦ ReflTransGen.single rfl

theorem Runs.loop_zero {b : Program} {t : Tape Cell} (h : t.head = 0) :
    Runs [.loop b] t t :=
  fun _ ↦ ReflTransGen.single (by simp [step, h])

theorem Runs.loop_iter {b : Program} {t t₁ t' : Tape Cell} (h : t.head ≠ 0)
    (hb : Runs b t t₁) (hl : Runs [.loop b] t₁ t') : Runs [.loop b] t t' := fun k ↦ by
  refine ReflTransGen.head (b := ⟨b ++ .loop b :: k, t⟩) (by simp [step, h]) ?_
  exact (hb (.loop b :: k)).trans (hl k)

/-! ## Gadgets -/

theorem Runs.replicate_right (n : ℕ) (t : Tape Cell) :
    Runs (List.replicate n .right) t ((Tape.move .right)^[n] t) := by
  induction n generalizing t with
  | zero => exact Runs.nil t
  | succ n ih =>
    rw [List.replicate_succ, Function.iterate_succ_apply]
    exact (Runs.right t).append (p := [_]) (ih _)

theorem Runs.replicate_left (n : ℕ) (t : Tape Cell) :
    Runs (List.replicate n .left) t ((Tape.move .left)^[n] t) := by
  induction n generalizing t with
  | zero => exact Runs.nil t
  | succ n ih =>
    rw [List.replicate_succ, Function.iterate_succ_apply]
    exact (Runs.left t).append (p := [_]) (ih _)

theorem runs_mv (o : ℤ) (t : Tape Cell) : Runs (mv o) t (moveBy o t) := by
  cases o with
  | ofNat n => exact Runs.replicate_right n t
  | negSucc n => exact Runs.replicate_left (n + 1) t

theorem runs_incAt (o : ℤ) (t : Tape Cell) : Runs (incAt o) t (modAt o (· + 1) t) :=
  ((runs_mv o t).append (Runs.inc _)).append (runs_mv (-o) _)

theorem runs_decAt (o : ℤ) (t : Tape Cell) : Runs (decAt o) t (modAt o (· - 1) t) :=
  ((runs_mv o t).append (Runs.dec _)).append (runs_mv (-o) _)

/-- `ifAt` on a clear flag does nothing. -/
theorem runs_ifAt_zero {o : ℤ} {body : Program} {t : Tape Cell} (h : t.nth o = 0) :
    Runs (ifAt o body) t t := by
  have hh : (moveBy o t).head = 0 := by simpa using (moveBy_nth o t 0).trans (by simpa using h)
  refine (((runs_mv o t).append (Runs.loop_zero hh)).append (runs_mv (-o) _)).eq ?_
  simp

/-- `ifAt` on a set flag clears it and runs the body once, provided the body
leaves the flag clear. -/
theorem runs_ifAt_one {o : ℤ} {body : Program} {t t₁ : Tape Cell} (h : t.nth o = 1)
    (hb : Runs body (modAt o (· - 1) t) t₁) (h₁ : t₁.nth o = 0) :
    Runs (ifAt o body) t t₁ := by
  have hh : (moveBy o t).head ≠ 0 := by
    rw [show (moveBy o t).head = t.nth o by simpa using moveBy_nth o t 0, h]; decide
  have hh₁ : (moveBy o t₁).head = 0 := by
    rw [show (moveBy o t₁).head = t₁.nth o by simpa using moveBy_nth o t₁ 0, h₁]
  have hbody : Runs ([.dec] ++ mv (-o) ++ body ++ mv o) (moveBy o t) (moveBy o t₁) :=
    (((Runs.dec _).append (runs_mv (-o) _)).append hb).append (runs_mv o _)
  have hloop := Runs.loop_iter hh hbody (Runs.loop_zero hh₁)
  exact (((runs_mv o t).append hloop).append (runs_mv (-o) _)).eq (by simp)

end BF
