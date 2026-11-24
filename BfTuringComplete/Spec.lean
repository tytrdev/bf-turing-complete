import BfTuringComplete.Blocks

/-!
# Gadget specs over flag predicates

Every cell our compiled code touches is 0 or 1, so block contents are a predicate
`P : ℤ → ℕ → Prop` ("the flag at block `j`, offset `r` is set").
`Spec w p P Q`: from any tape whose blocks are `P`, program `p` runs to a tape whose blocks are `Q`.
-/

namespace BF

open Turing Classical

/-- 0/1 block contents of a flag predicate. -/
noncomputable def toBlk (P : ℤ → ℕ → Prop) : ℤ → ℕ → Cell := fun j r ↦ if P j r then 1 else 0

def Spec (w : ℕ) (p : Program) (P Q : ℤ → ℕ → Prop) : Prop :=
  ∀ t, Holds w (toBlk P) t → ∃ t', Holds w (toBlk Q) t' ∧ Runs p t t'

variable {w : ℕ} {p q : Program} {P Q R : ℤ → ℕ → Prop}

/-- Two predicates agreeing on in-block offsets describe the same tapes. -/
theorem Holds.congr {P Q : ℤ → ℕ → Prop} {t : Tape Cell} (h : Holds w (toBlk P) t)
    (e : ∀ j r, r < w → (P j r ↔ Q j r)) : Holds w (toBlk Q) t := by
  intro j r hr
  rw [h j r hr]
  simp [toBlk, e j r hr]

theorem Spec.nil : Spec w [] P P := fun t h ↦ ⟨t, h, Runs.nil t⟩

theorem Spec.append (h₁ : Spec w p P Q) (h₂ : Spec w q Q R) : Spec w (p ++ q) P R := by
  intro t h
  obtain ⟨t₁, h₁', r₁⟩ := h₁ t h
  obtain ⟨t₂, h₂', r₂⟩ := h₂ t₁ h₁'
  exact ⟨t₂, h₂', r₁.append r₂⟩

theorem Spec.conseq {Q' : ℤ → ℕ → Prop} (h : Spec w p P Q) (e : ∀ j r, r < w → (Q j r ↔ Q' j r)) :
    Spec w p P Q' := by
  intro t ht
  obtain ⟨t', h', r⟩ := h t ht
  exact ⟨t', h'.congr e, r⟩

theorem Spec.pre {P' : ℤ → ℕ → Prop} (h : Spec w p P Q) (e : ∀ j r, r < w → (P' j r ↔ P j r)) :
    Spec w p P' Q :=
  fun t ht ↦ h t (ht.congr e)

theorem Holds.nth0 {P : ℤ → ℕ → Prop} {t : Tape Cell} (h : Holds w (toBlk P) t) {o : ℕ}
    (ho : o < w) : t.nth o = if P 0 o then 1 else 0 := by
  simpa [toBlk] using h 0 o ho

/-- Set a clear flag in block `d`. -/
theorem holds_inc {t : Tape Cell} (ht : Holds w (toBlk P) t) (d : ℤ) {o : ℕ} (ho : o < w)
    (h0 : ¬P d o) (e : ∀ j r, r < w → (Q j r ↔ (j = d ∧ r = o) ∨ P j r)) :
    Holds w (toBlk Q) (modAt (w * d + o) (· + 1) t) := by
  intro j r hr
  rw [modAt_nth]
  split_ifs with hj
  · obtain ⟨rfl, rfl⟩ := (block_eq_iff' hr ho).1 hj
    rw [ht j r hr]
    simp [toBlk, h0, (e j r hr).2 (Or.inl ⟨rfl, rfl⟩)]
  · rw [ht j r hr]
    have : ¬(j = d ∧ r = o) := fun ⟨h1, h2⟩ ↦ hj (by subst h1 h2; rfl)
    simp [toBlk, e j r hr, this]

theorem spec_incAt (d : ℤ) {o : ℕ} (ho : o < w) (h0 : ¬P d o)
    (e : ∀ j r, r < w → (Q j r ↔ (j = d ∧ r = o) ∨ P j r)) :
    Spec w (incAt (w * d + o)) P Q :=
  fun t ht ↦ ⟨_, holds_inc ht d ho h0 e, runs_incAt _ t⟩

theorem spec_incAt0 {o : ℕ} (ho : o < w) (h0 : ¬P 0 o)
    (e : ∀ j r, r < w → (Q j r ↔ (j = 0 ∧ r = o) ∨ P j r)) :
    Spec w (incAt o) P Q := by
  simpa using spec_incAt (w := w) 0 ho h0 e

/-- Clear a set flag in block 0. -/
theorem holds_dec {t : Tape Cell} (ht : Holds w (toBlk P) t) {o : ℕ} (ho : o < w) (h1 : P 0 o)
    (e : ∀ j r, r < w → (Q j r ↔ ¬(j = 0 ∧ r = o) ∧ P j r)) :
    Holds w (toBlk Q) (modAt o (· - 1) t) := by
  intro j r hr
  rw [modAt_nth]
  split_ifs with hj
  · obtain ⟨rfl, rfl⟩ := (block_eq_iff hr ho).1 hj
    rw [ht.nth0 ho]
    simp [toBlk, h1, e 0 r hr]
  · rw [ht j r hr]
    have : ¬(j = 0 ∧ r = o) := fun ⟨h1, h2⟩ ↦ hj (by subst h1 h2; simp)
    simp [toBlk, e j r hr, this]

theorem spec_decAt {o : ℕ} (ho : o < w) (h1 : P 0 o)
    (e : ∀ j r, r < w → (Q j r ↔ ¬(j = 0 ∧ r = o) ∧ P j r)) :
    Spec w (decAt o) P Q :=
  fun t ht ↦ ⟨_, holds_dec ht ho h1 e, runs_decAt _ t⟩

/-- `ifAt` on a clear flag is a no-op. -/
theorem spec_ifAt_clear {o : ℕ} (ho : o < w) (h0 : ¬P 0 o) (body : Program) :
    Spec w (ifAt o body) P P := by
  intro t ht
  exact ⟨t, ht, runs_ifAt_zero (by rw [ht.nth0 ho]; simp [h0])⟩

/-- `ifAt` on a set flag: clear it, run the body, and the body must leave it clear. -/
theorem spec_ifAt_set {o : ℕ} (ho : o < w) {body : Program} (P' : ℤ → ℕ → Prop) (h1 : P 0 o)
    (e : ∀ j r, r < w → (P' j r ↔ ¬(j = 0 ∧ r = o) ∧ P j r))
    (hb : Spec w body P' Q) (hQ : ¬Q 0 o) : Spec w (ifAt o body) P Q := by
  intro t ht
  obtain ⟨t₂, ht₂, r₂⟩ := hb _ (holds_dec ht ho h1 e)
  exact ⟨t₂, ht₂, runs_ifAt_one (by rw [ht.nth0 ho]; simp [h1]) r₂
    (by rw [ht₂.nth0 ho]; simp [hQ])⟩

/-- Moving by `d` whole blocks relabels block contents. -/
theorem spec_mv (d : ℤ) (e : ∀ j r, r < w → (Q j r ↔ P (j + d) r)) :
    Spec w (mv (w * d)) P Q := by
  intro t ht
  refine ⟨_, ?_, runs_mv _ t⟩
  exact Holds.congr (ht.shift d) fun j r hr ↦ (e j r hr).symm

/-! ## The normal form `Base ∨ (j = 0 ∧ s r)`

Most states are a tape part `Base` plus head-block scratch flags `s`. -/

theorem Spec.conseq_s {Base : ℤ → ℕ → Prop} {s s' : ℕ → Prop}
    (h : Spec w p P (fun j r ↦ Base j r ∨ (j = 0 ∧ s r))) (e : ∀ r, r < w → (s r ↔ s' r)) :
    Spec w p P (fun j r ↦ Base j r ∨ (j = 0 ∧ s' r)) :=
  h.conseq fun j r hr ↦ by rw [e r hr]

/-- Set a clear scratch flag in the head block. -/
theorem spec_inc_s {Base : ℤ → ℕ → Prop} {s : ℕ → Prop} {o : ℕ} (ho : o < w)
    (h0 : ¬Base 0 o) (hs : ¬s o) :
    Spec w (incAt o) (fun j r ↦ Base j r ∨ (j = 0 ∧ s r))
      (fun j r ↦ Base j r ∨ (j = 0 ∧ (r = o ∨ s r))) :=
  spec_incAt0 ho (by simp [h0, hs]) fun j r _ ↦ by
    by_cases hj : j = 0 <;> simp [hj] <;> tauto

/-! ## Lists of gadgets -/

theorem spec_flatMap_noop {α} (L : List α) (f : α → Program) (h : ∀ x ∈ L, Spec w (f x) P P) :
    Spec w (L.flatMap f) P P := by
  induction L with
  | nil => exact Spec.nil
  | cons x L ih =>
    simp only [List.flatMap_cons]
    exact (h x (by simp)).append (ih fun y hy ↦ h y (by simp [hy]))

/-- Exactly one gadget in the list (`a`) does something; the rest are no-ops before and after. -/
theorem spec_flatMap_single {α} [DecidableEq α] (L : List α) (hL : L.Nodup) (f : α → Program)
    (a : α) (ha : a ∈ L) (hA : Spec w (f a) P Q)
    (hP : ∀ x ∈ L, x ≠ a → Spec w (f x) P P) (hQ : ∀ x ∈ L, x ≠ a → Spec w (f x) Q Q) :
    Spec w (L.flatMap f) P Q := by
  induction L with
  | nil => simp at ha
  | cons x L ih =>
    simp only [List.flatMap_cons]
    obtain ⟨hx, hL⟩ := List.nodup_cons.1 hL
    by_cases hxa : x = a
    · subst hxa
      exact hA.append (spec_flatMap_noop L f fun y hy ↦
        hQ y (by simp [hy]) (fun h ↦ hx (h ▸ hy)))
    · have ha' : a ∈ L := by simpa [Ne.symm hxa] using ha
      exact (hP x (by simp) hxa).append
        (ih hL ha' (fun y hy ↦ hP y (by simp [hy])) (fun y hy ↦ hQ y (by simp [hy])))

end BF
