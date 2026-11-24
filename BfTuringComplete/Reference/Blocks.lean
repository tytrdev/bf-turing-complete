import BfTuringComplete.Reference.Runs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The block view of a BF tape

Cell `w * j + r` (with `r < w`) is offset `r` of block `j`. `Holds w blk t` says the
tape `t` (relative to its head) has contents `blk j r` at block `j`, offset `r`.
-/

namespace BF

open Turing

/-- The tape `t` has block contents `blk`, in blocks of width `w`. -/
def Holds (w : ℕ) (blk : ℤ → ℕ → Cell) (t : Tape Cell) : Prop :=
  ∀ (j : ℤ) (r : ℕ), r < w → t.nth (w * j + r) = blk j r

/-- The only arithmetic fact we need: in-block offsets only hit block 0. -/
theorem block_eq_iff {w : ℕ} {j : ℤ} {r o : ℕ} (hr : r < w) (ho : o < w) :
    (w * j + r : ℤ) = o ↔ j = 0 ∧ r = o := by
  constructor
  · intro h
    rcases lt_trichotomy j 0 with hj | rfl | hj
    · have : (w : ℤ) * j ≤ -w := by nlinarith
      omega
    · simp at h; omega
    · have : (w : ℤ) * j ≥ w := by nlinarith
      omega
  · rintro ⟨rfl, rfl⟩; simp

/-- General form: offsets within blocks `j` and `d`. -/
theorem block_eq_iff' {w : ℕ} {j d : ℤ} {r o : ℕ} (hr : r < w) (ho : o < w) :
    (w * j + r : ℤ) = w * d + o ↔ j = d ∧ r = o := by
  constructor
  · intro h
    rcases lt_trichotomy j d with hj | rfl | hj
    · have : (w : ℤ) * j + w ≤ w * d := by nlinarith
      omega
    · simp at h; omega
    · have : (w : ℤ) * d + w ≤ w * j := by nlinarith
      omega
  · rintro ⟨rfl, rfl⟩; rfl

/-- Modifying an in-block offset changes only that cell of block 0. -/
theorem Holds.modAt {w : ℕ} {blk : ℤ → ℕ → Cell} {t : Tape Cell} (h : Holds w blk t)
    {o : ℕ} (ho : o < w) (f : Cell → Cell) :
    Holds w (Function.update blk 0 (Function.update (blk 0) o (f (blk 0 o))))
      (BF.modAt o f t) := by
  intro j r hr
  rw [modAt_nth]
  split_ifs with e
  · obtain ⟨rfl, rfl⟩ := (block_eq_iff hr ho).1 e
    have := h 0 r hr
    simp_all
  · rw [h j r hr]
    by_cases hj : j = 0
    · subst hj
      have : r ≠ o := fun hro ↦ e (by simp [hro])
      simp [this]
    · simp [hj]

/-- Shifting the head by `d` whole blocks relabels the blocks. -/
theorem Holds.shift {w : ℕ} {blk : ℤ → ℕ → Cell} {t : Tape Cell} (h : Holds w blk t) (d : ℤ) :
    Holds w (fun j ↦ blk (j + d)) (moveBy (w * d) t) := by
  intro j r hr
  rw [moveBy_nth]
  refine (congrArg t.nth ?_).trans (h (j + d) r hr)
  ring

/-- The block contents determine the tape. -/
theorem Holds.unique {w : ℕ} (hw : 0 < w) {blk : ℤ → ℕ → Cell} {t₁ t₂ : Tape Cell}
    (h₁ : Holds w blk t₁) (h₂ : Holds w blk t₂) : t₁ = t₂ := by
  refine Tape.ext_nth fun i ↦ ?_
  have hw' : (0 : ℤ) < w := by exact_mod_cast hw
  have e : i = w * (i / w) + ((i % w).toNat : ℕ) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hw'.ne')]
    exact (Int.mul_ediv_add_emod i w).symm
  have hr : (i % w).toNat < w := by
    have := Int.emod_lt_of_pos i hw'
    omega
  rw [e, h₁ _ _ hr, h₂ _ _ hr]

end BF
