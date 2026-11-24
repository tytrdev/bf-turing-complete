import BfTuringComplete.Core.Statement
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
set_option maxHeartbeats 1000000
namespace BF.Elegant
open Turing StateTransition Relation Classical Fintype

def Runs (p : Program) (t u : Tape Cell) := ∀ k, Reaches step ⟨p ++ k, t⟩ ⟨k, u⟩

theorem Runs.seq {p q : Program} {t u v : Tape Cell} (h : Runs p t u) (g : Runs q u v) :
    Runs (p ++ q) t v := fun k ↦ by rw [List.append_assoc]; exact (h _).trans (g k)

theorem replicate_runs (c : Stmt) (F : Tape Cell → Tape Cell) (s : ℤ)
    (hc : ∀ k t, step ⟨c :: k, t⟩ = some ⟨k, F t⟩) (hF : ∀ t i, (F t).nth i = t.nth (i + s)) :
    ∀ (n : ℕ) (t : Tape Cell), ∃ u, Runs (.replicate n c) t u ∧ ∀ i, u.nth i = t.nth (i + n * s)
  | 0, t => ⟨t, fun _ ↦ .refl, by simp⟩
  | n + 1, t => by
    obtain ⟨u, h, e⟩ := replicate_runs c F s hc hF n (F t)
    exact ⟨u, fun k ↦ .head (hc _ t) (h k), fun i ↦ by rw [e, hF]; congr 1; push_cast; ring⟩

def shift (x : ℤ) : Program :=
  if 0 ≤ x then .replicate x.toNat .right else .replicate (-x).toNat .left

theorem shift_runs (x : ℤ) (t : Tape Cell) : ∃ u, Runs (shift x) t u ∧ ∀ i, u.nth i = t.nth (i + x) := by
  unfold shift; split_ifs
  · obtain ⟨u, r, e⟩ := replicate_runs .right (·.move .right) 1 (fun _ _ ↦ rfl) (by simp) x.toNat t
    exact ⟨u, r, fun i ↦ by rw [e]; congr 1; omega⟩
  · obtain ⟨u, r, e⟩ := replicate_runs .left (·.move .left) (-1) (fun _ _ ↦ rfl)
      (by simp [sub_eq_add_neg]) (-x).toNat t
    exact ⟨u, r, fun i ↦ by rw [e]; congr 1; omega⟩

/-- Tape `t` holds flags `P` in blocks of width `w`, viewed from base offset `b`. -/
def Holds (w : ℕ) (b : ℤ) (P : ℤ → ℕ → Prop) (t : Tape Cell) : Prop :=
  ∀ j (r : ℕ), r < w → t.nth (w * j + r - b) = if P j r then 1 else 0

def Spec (w : ℕ) (p : Program) (b : ℤ) (P : ℤ → ℕ → Prop) (c : ℤ) (Q : ℤ → ℕ → Prop) : Prop :=
  ∀ t, Holds w b P t → ∃ u, Holds w c Q u ∧ Runs p t u

variable {w o : ℕ} {p q B : Program} {b c d x : ℤ} {P Q R : ℤ → ℕ → Prop}

theorem Spec.seq (h : Spec w p b P c Q) (g : Spec w q c Q d R) : Spec w (p ++ q) b P d R := fun t ht ↦ by
  obtain ⟨u, hu, r⟩ := h t ht
  obtain ⟨v, hv, r'⟩ := g u hu
  exact ⟨v, hv, r.seq r'⟩

theorem Spec.nil : Spec w [] b P b P := fun t h ↦ ⟨t, h, fun _ ↦ .refl⟩

theorem Spec.congr {P' Q' : ℤ → ℕ → Prop} (h : Spec w p b P c Q) (e₁ : ∀ j r, r < w → (P' j r ↔ P j r))
    (e₂ : ∀ j r, r < w → (Q j r ↔ Q' j r)) : Spec w p b P' c Q' := fun t ht ↦ by
  obtain ⟨u, hu, r⟩ := h t fun j r hr ↦ by rw [ht j r hr]; simp [e₁ j r hr]
  exact ⟨u, fun j r hr ↦ by rw [hu j r hr]; simp [e₂ j r hr], r⟩

theorem Spec.post {Q' : ℤ → ℕ → Prop} (h : Spec w p b P c Q) (e : ∀ j r, r < w → (Q j r ↔ Q' j r)) :
    Spec w p b P c Q' := h.congr (fun _ _ _ ↦ .rfl) e

theorem Spec.pre {P' : ℤ → ℕ → Prop} (h : Spec w p b P c Q) (e : ∀ j r, r < w → (P' j r ↔ P j r)) :
    Spec w p b P' c Q := h.congr e fun _ _ _ ↦ .rfl

theorem Holds.congr {t : Tape Cell} (h : Holds w b P t) (e : ∀ j r, r < w → (P j r ↔ Q j r)) : Holds w b Q t :=
  fun j r hr ↦ by rw [h j r hr]; simp [e j r hr]

theorem Spec.shift_by (h : c = b + x) : Spec w (shift x) b P c P := fun t ht ↦ by
  obtain ⟨u, r, e⟩ := shift_runs x t
  exact ⟨u, fun j k hk ↦ by rw [e, ← ht j k hk, h]; congr 1; ring, r⟩

theorem block_eq {j : ℤ} {r : ℕ} (hr : r < w) (ho : o < w) :
    w * j + r - (w * d + o) = 0 ↔ j = d ∧ r = o := by
  constructor
  · intro h
    rcases lt_trichotomy j d with hj | rfl | hj
    · have : (w : ℤ) * j + w ≤ w * d := by nlinarith
      omega
    · simp at h; omega
    · have : (w : ℤ) * d + w ≤ w * j := by nlinarith
      omega
  · rintro ⟨rfl, rfl⟩; ring

theorem head_eq {t : Tape Cell} (ht : Holds w b P t) (hb : b = w * d + o) (ho : o < w) :
    t.head = if P d o then 1 else 0 := by
  rw [← ht d o ho, hb]; simp

theorem Spec.write (commit : Stmt) (g : Cell → Cell)
    (hc : ∀ k t, step ⟨commit :: k, t⟩ = some ⟨k, t.write (g t.head)⟩)
    (hb : b = w * d + o) (ho : o < w) (hg : g (if P d o then 1 else 0) = if Q d o then 1 else 0)
    (hQ : ∀ j r, ¬(j = d ∧ r = o) → (Q j r ↔ P j r)) : Spec w [commit] b P b Q := fun t ht ↦
  ⟨_, fun j r hr ↦ by
    rw [Tape.write_nth]
    by_cases h : (w : ℤ) * j + r - b = 0
    · obtain ⟨rfl, rfl⟩ := (block_eq hr ho).1 (hb ▸ h)
      rw [if_pos h, head_eq ht hb ho, hg]
    · rw [if_neg h, ht j r hr]
      simp [hQ j r fun ⟨h1, h2⟩ ↦ h (by rw [h1, h2, hb]; ring)], fun _ ↦ .single (hc _ _)⟩

theorem Spec.inc (hb : b = w * d + o) (ho : o < w) (h0 : ¬P d o) :
    Spec w [.inc] b P b fun j r ↦ j = d ∧ r = o ∨ P j r :=
  Spec.write _ (· + 1) (fun _ _ ↦ rfl) hb ho (by simp [h0]) fun j r h ↦ by simp [h]

theorem Spec.dec (hb : b = w * d + o) (ho : o < w) (h1 : P d o) :
    Spec w [.dec] b P b fun j r ↦ ¬(j = d ∧ r = o) ∧ P j r :=
  Spec.write _ (· - 1) (fun _ _ ↦ rfl) hb ho (by simp [h1]) fun j r h ↦ by simp [h]

theorem Spec.skip (hb : b = w * d + o) (ho : o < w) (h0 : ¬P d o) : Spec w [.loop B] b P b P :=
  fun t ht ↦ ⟨t, ht, fun _ ↦ .single (by simp [step, head_eq ht hb ho, h0])⟩

theorem Spec.iter (hb : b = w * d + o) (ho : o < w) (h1 : P d o) (hB : Spec w B b P b Q)
    (hl : Spec w [.loop B] b Q b R) : Spec w [.loop B] b P b R := fun t ht ↦ by
  obtain ⟨u, hu, r⟩ := hB t ht
  obtain ⟨v, hv, r'⟩ := hl u hu
  exact ⟨v, hv, fun k ↦ .head (by simp [step, head_eq ht hb ho, h1]) ((r _).trans (r' k))⟩

set_option hygiene false in
macro "arith" : tactic => `(tactic|
  (simp (config := { failIfUnchanged := false }) only [symFlag, written, moved, actFlags, pendFlags, width, runOff, off, pendOff, stateOff, ne_eq,
    false_and, and_false, false_or, or_false, iff_def, false_implies, imp_false, true_and,
    and_true, not_true_eq_false, not_false_eq_true, true_or, or_true, true_implies,
    implies_true, and_self, or_self, eq_self_iff_true, Fin.val_mk, iff_self] at * <;> omega))

set_option hygiene false in
macro "arith_flags" : tactic => `(tactic| (intro j r hr; by_cases hj : j = 0 <;> (try subst hj) <;> arith))

def ifFlag (o : ℕ) (B : Program) : Program :=
  shift o ++ [.loop (.dec :: shift (-o) ++ B ++ shift o)] ++ shift (-o)
def incAt (x : ℤ) : Program := shift x ++ .inc :: shift (-x)
def decAt (x : ℤ) : Program := shift x ++ .dec :: shift (-x)

theorem Spec.inc_at (hx : x = w * d + o) (ho : o < w) (h0 : ¬P d o) :
    Spec w (incAt x) 0 P 0 fun j r ↦ j = d ∧ r = o ∨ P j r :=
  (Spec.shift_by (c := x) (by simp)).seq ((Spec.inc hx ho h0).seq (Spec.shift_by (by simp)))

theorem Spec.dec_at (ho : o < w) (h1 : P 0 o) :
    Spec w (decAt o) 0 P 0 fun j r ↦ ¬(j = 0 ∧ r = o) ∧ P j r :=
  (Spec.shift_by (c := o) (by simp)).seq ((Spec.dec (d := 0) (by simp) ho h1).seq (Spec.shift_by (by simp)))

theorem Spec.ifOff (ho : o < w := by arith) (h0 : ¬P 0 o := by arith) : Spec w (ifFlag o B) 0 P 0 P :=
  ((Spec.shift_by (c := o) (by simp)).seq (Spec.skip (d := 0) (by simp) ho h0)).seq (Spec.shift_by (by simp))

theorem Spec.ifOn (hB : Spec w B 0 (fun j r ↦ ¬(j = 0 ∧ r = o) ∧ P j r) 0 Q)
    (ho : o < w := by arith) (h1 : P 0 o := by arith) (hQ : ¬Q 0 o := by arith) :
    Spec w (ifFlag o B) 0 P 0 Q :=
  ((Spec.shift_by (c := o) (by simp)).seq (Spec.iter (d := 0) (by simp) ho h1
    ((((Spec.dec (d := 0) (by simp) ho h1).seq (Spec.shift_by (c := 0) (by simp))).seq hB).seq
      (Spec.shift_by (by simp))) (Spec.skip (d := 0) (by simp) ho hQ))).seq (Spec.shift_by (by simp))

theorem Spec.shiftBlocks (d : ℤ) : Spec w (shift (↑w * d)) 0 P 0 fun j r ↦ P (j + d) r := fun t ht ↦ by
  obtain ⟨u, hu, r⟩ := Spec.shift_by (c := ↑w * d) (x := ↑w * d) (by simp) t ht
  exact ⟨u, fun j k hk ↦ by rw [← hu (j + d) k hk]; congr 1; ring, r⟩

theorem Spec.flatMap_id {α} (L : List α) (g : α → Program) (h : ∀ x ∈ L, Spec w (g x) 0 P 0 P) :
    Spec w (L.flatMap g) 0 P 0 P := by
  induction L with
  | nil => exact Spec.nil
  | cons x L ih =>
    rw [List.flatMap_cons]
    exact (h x (by simp)).seq (ih fun y hy ↦ h y (by simp [hy]))

theorem Spec.flatMap_one {α} [DecidableEq α] (L : List α) (hL : L.Nodup) (g : α → Program) (a : α)
    (ha : a ∈ L) (hA : Spec w (g a) 0 P 0 Q) (hP : ∀ x ∈ L, x ≠ a → Spec w (g x) 0 P 0 P)
    (hQ : ∀ x ∈ L, x ≠ a → Spec w (g x) 0 Q 0 Q) : Spec w (L.flatMap g) 0 P 0 Q := by
  induction L with
  | nil => simp at ha
  | cons x L ih =>
    rw [List.flatMap_cons]
    obtain ⟨hx, hL⟩ := List.nodup_cons.1 hL
    by_cases hxa : x = a
    · subst hxa
      exact hA.seq (Spec.flatMap_id L g fun y hy ↦ hQ y (by simp [hy]) fun h ↦ hx (h ▸ hy))
    · exact (hP x (by simp) hxa).seq (ih hL (by simpa [Ne.symm hxa] using ha)
        (fun y hy ↦ hP y (by simp [hy])) fun y hy ↦ hQ y (by simp [hy]))

theorem Spec.incIf {C : Prop} [Decidable C] {x : ℕ} (hx : x < w) (h0 : C → ¬P 0 x) :
    Spec w (if C then incAt x else []) 0 P 0 fun j r ↦ j = 0 ∧ r = x ∧ C ∨ P j r := by
  split_ifs with h
  · exact (Spec.inc_at (d := 0) (by simp) hx (h0 h)).post fun j r _ ↦ by simp [h]
  · exact Spec.nil.post fun j r _ ↦ by simp [h]

/-! ## The machine -/

def idx (α) [Fintype α] [Inhabited α] : α ≃ Fin (card α - 1 + 1) :=
  let e := (equivFin α).trans (finCongr (by have : 0 < card α := card_pos; omega))
  e.trans (Equiv.swap (e default) 0)

theorem idx_default (α) [Fintype α] [Inhabited α] : idx α default = 0 := by simp [idx]

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Fintype Γ] [Fintype Λ] (M : TM0.Machine Γ Λ)

def width (M : TM0.Machine Γ Λ) := 2 * (card Γ - 1) + 2 * (card Λ - 1) + 6
def runOff (M : TM0.Machine Γ Λ) := 2 * (card Γ - 1) + 2 * (card Λ - 1) + 5
def off (M : TM0.Machine Γ Λ) (k : ℕ) : ℕ := 2 * (card Γ - 1) + 2 * (card Λ - 1) + k
def pendOff (M : TM0.Machine Γ Λ) (i : ℕ) : ℕ := 2 * (card Γ - 1) + (card Λ - 1) + 1 + i
def stateOff (M : TM0.Machine Γ Λ) (i : ℕ) : ℕ := 2 * (card Γ - 1) + i

/-- What a transition does: (new symbol, next state, continues?, moves left?, moves right?). -/
def tr (q : Λ) (a : Γ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  match M q a with
  | none => (idx Γ a, 0, 0, 0, 0)
  | some (q', .move .left) => (idx Γ a, idx Λ q', 1, 1, 0)
  | some (q', .move .right) => (idx Γ a, idx Λ q', 1, 0, 1)
  | some (q', .write b) => (idx Γ b, idx Λ q', 1, 0, 0)

theorem tr_bounds (q : Λ) (a : Γ) : (tr M q a).1 < (card Γ - 1) + 1 ∧ (tr M q a).2.1 < (card Λ - 1) + 1 ∧
    (tr M q a).2.2.1 ≤ 1 ∧ (tr M q a).2.2.2.1 + (tr M q a).2.2.2.2 ≤ (tr M q a).2.2.1 ∧
    ((tr M q a).2.2.1 = 0 ∨ (tr M q a).2.2.2.1 + (tr M q a).2.2.2.2 = 1 → (tr M q a).1 = idx Γ a) := by
  unfold tr; rcases M q a with _ | ⟨q', d | b⟩ <;> (try cases d) <;> simp

def actProg (q : Λ) (a : Γ) : Program :=
  (if (tr M q a).1 ≠ 0 then incAt ((card Γ - 1) + (tr M q a).1 - 1 : ℕ) else []) ++
  (if (tr M q a).2.2.2.1 = 1 then incAt (off M 3 : ℕ) else []) ++
  (if (tr M q a).2.2.2.2 = 1 then incAt (off M 4 : ℕ) else []) ++
  (if (tr M q a).2.2.1 = 1 then incAt (pendOff M (tr M q a).2.1 : ℕ) else []) ++
  (if (tr M q a).2.2.1 = 1 then incAt (off M 5 : ℕ) else [])

def dispatchSym (q : Λ) : Program :=
  incAt (off M 2 : ℕ) ++ (List.finRange ((card Γ - 1))).flatMap (fun i : Fin _ ↦
    ifFlag i (decAt (off M 2 : ℕ) ++ actProg M q ((idx Γ).symm i.succ))) ++
  ifFlag (off M 2) (actProg M q default)

def dispatch : Program := (List.finRange ((card Λ - 1) + 1)).flatMap fun i : Fin _ ↦ ifFlag (stateOff M i) (dispatchSym M ((idx Λ).symm i))
def flush (_ : TM0.Machine Γ Λ) : Program := (List.finRange ((card Γ - 1))).flatMap fun i : Fin _ ↦ ifFlag ((card Γ - 1) + i) (incAt (i : ℕ))
def carry (d : ℤ) : Program :=
  (List.finRange ((card Λ - 1) + 1)).flatMap (fun i : Fin _ ↦
    ifFlag (pendOff M i) (incAt (↑(pendOff M i : ℕ) + ↑(width M) * d))) ++
  ifFlag (off M 5) (incAt (↑(off M 5 : ℕ) + ↑(width M) * d)) ++ shift (↑(width M) * d)
def commit : Program :=
  (List.finRange ((card Λ - 1) + 1)).flatMap fun i : Fin _ ↦ ifFlag (pendOff M i) (incAt (stateOff M i : ℕ))
def body : Program :=
  dispatch M ++ flush M ++ (ifFlag (off M 3) (carry M (-1)) ++ ifFlag (off M 4) (carry M 1)) ++
    commit M
def program : Program :=
  incAt (stateOff M (idx Λ default) : ℕ) ++ incAt (off M 5 : ℕ) ++ ifFlag (off M 5) (body M)

/-! ## Flag predicates -/

def symFlag (T : Tape Γ) (j : ℤ) (r : ℕ) : Prop := r + 1 = idx Γ (T.nth j)

def pendFlags (q : Λ) (a : Γ) (r : ℕ) : Prop :=
  (tr M q a).2.2.2.1 = 1 ∧ r = off M 3 ∨ (tr M q a).2.2.2.2 = 1 ∧ r = off M 4 ∨
  (tr M q a).2.2.1 = 1 ∧ r = pendOff M (tr M q a).2.1 ∨
  (tr M q a).2.2.1 = 1 ∧ r = off M 5

def actFlags (q : Λ) (a : Γ) (r : ℕ) : Prop :=
  (tr M q a).1 ≠ 0 ∧ r = (card Γ - 1) + (tr M q a).1 - 1 ∨ pendFlags M q a r

def written (q : Λ) (T : Tape Γ) (j : ℤ) (r : ℕ) : Prop :=
  j ≠ 0 ∧ symFlag T j r ∨ j = 0 ∧ r + 1 = (tr M q (T.nth 0)).1

def moved (q : Λ) (T : Tape Γ) (j : ℤ) (r : ℕ) : Prop :=
  (tr M q (T.nth 0)).2.2.2.1 = 1 ∧ written M q T (j + -1) r ∨
  (tr M q (T.nth 0)).2.2.2.2 = 1 ∧ written M q T (j + 1) r ∨
  (tr M q (T.nth 0)).2.2.2.1 = 0 ∧ (tr M q (T.nth 0)).2.2.2.2 = 0 ∧ written M q T j r


/-! ## Phases -/

theorem actProg_spec (T : Tape Γ) (q : Λ) (a : Γ) :
    Spec (width M) (actProg M q a) 0 (fun j r ↦ j ≠ 0 ∧ symFlag T j r) 0
      fun j r ↦ j ≠ 0 ∧ symFlag T j r ∨ j = 0 ∧ actFlags M q a r := by
  have := tr_bounds M q a
  unfold actProg
  refine (((((Spec.incIf ?_ ?_).seq (Spec.incIf ?_ ?_)).seq (Spec.incIf ?_ ?_)).seq (Spec.incIf ?_ ?_)).seq
    (Spec.incIf ?_ ?_)).post ?_
  all_goals first | arith | arith_flags

theorem dispatchSym_spec (T : Tape Γ) (q : Λ) :
    Spec (width M) (dispatchSym M q) 0 (symFlag T) 0 fun j r ↦ j ≠ 0 ∧ symFlag T j r ∨ j = 0 ∧ actFlags M q (T.nth 0) r := by
  have := tr_bounds M q (T.nth 0)
  have I := Spec.inc_at (w := width M) (P := symFlag T) (d := 0) (o := off M 2)
    (x := (off M 2 : ℕ)) (by simp)
    (by arith) (by arith)
  unfold dispatchSym
  by_cases ha : (idx Γ (T.nth 0) : ℕ) = 0
  · have e : T.nth 0 = default := (idx Γ).injective (Fin.ext (by rw [ha, idx_default]; rfl))
    refine (I.seq (Spec.flatMap_id _ _ fun i _ ↦ Spec.ifOff)).seq ?_
    rw [e] at this ⊢
    exact Spec.ifOn ((actProg_spec M T q default).pre (by arith_flags))
  · obtain ⟨i₀, hi⟩ : ∃ i₀ : Fin ((card Γ - 1)), i₀.val + 1 = idx Γ (T.nth 0) :=
      ⟨⟨(idx Γ (T.nth 0) : ℕ) - 1, by have := (idx Γ (T.nth 0)).isLt; omega⟩,
        by simp only; omega⟩
    have hs : (idx Γ).symm i₀.succ = T.nth 0 :=
      (idx Γ).symm_apply_eq.2 (Fin.ext (by simp only [Fin.val_succ]; omega))
    refine (I.seq (Spec.flatMap_one _ (List.nodup_finRange _) _ i₀ (List.mem_finRange _) ?_ ?_ ?_)).seq
      (Spec.ifOff)
    · simp only [hs]
      exact Spec.ifOn (((Spec.dec_at (by arith) (by arith)).post (by arith_flags)).seq
        (actProg_spec M T q _))
    · intro i _ h; have := Fin.val_ne_of_ne h; exact Spec.ifOff
    · intro i _ _; exact Spec.ifOff

theorem dispatch_spec (T : Tape Γ) (q : Λ) :
    Spec (width M) (dispatch M) 0 (fun j r ↦ symFlag T j r ∨ j = 0 ∧ r = stateOff M (idx Λ q)) 0
      fun j r ↦ j ≠ 0 ∧ symFlag T j r ∨ j = 0 ∧ actFlags M q (T.nth 0) r := by
  have := tr_bounds M q (T.nth 0)
  refine Spec.flatMap_one _ (List.nodup_finRange _) _ (idx Λ q) (List.mem_finRange _) ?_ ?_ ?_
  · simp only [Equiv.symm_apply_apply]
    exact Spec.ifOn ((dispatchSym_spec M T q).pre (by arith_flags))
  · intro i _ h; have := Fin.val_ne_of_ne h; exact Spec.ifOff
  · intro i _ _; exact Spec.ifOff

theorem flush_spec (T : Tape Γ) (q : Λ) :
    Spec (width M) (flush M) 0 (fun j r ↦ j ≠ 0 ∧ symFlag T j r ∨ j = 0 ∧ actFlags M q (T.nth 0) r) 0
      fun j r ↦ written M q T j r ∨ j = 0 ∧ pendFlags M q (T.nth 0) r := by
  have := tr_bounds M q (T.nth 0)
  unfold flush
  by_cases h0 : (tr M q (T.nth 0)).1 = 0
  · exact (Spec.flatMap_id _ _ fun i _ ↦ Spec.ifOff).post (by arith_flags)
  · obtain ⟨i₀, hi⟩ : ∃ i₀ : Fin ((card Γ - 1)), i₀.val + 1 = (tr M q (T.nth 0)).1 :=
      ⟨⟨(tr M q (T.nth 0)).1 - 1, by omega⟩, by simp only; omega⟩
    refine Spec.flatMap_one _ (List.nodup_finRange _) _ i₀ (List.mem_finRange _) ?_ ?_ ?_
    · exact Spec.ifOn ((Spec.inc_at (d := 0) (o := i₀) (by simp) (by arith) (by arith)).post (by arith_flags))
    · intro i _ h; have := Fin.val_ne_of_ne h; exact Spec.ifOff
    · intro i _ h; have := Fin.val_ne_of_ne h; exact Spec.ifOff

theorem carry_spec (T : Tape Γ) (q : Λ) (d : ℤ) (hd : d = 1 ∨ d = -1) (k : ℕ) (hk : k < (card Λ - 1) + 1) :
    Spec (width M) (carry M d) 0 (fun j r ↦ written M q T j r ∨ j = 0 ∧
        (r = pendOff M k ∨ r = off M 5)) 0
      fun j r ↦ written M q T (j + d) r ∨ j = 0 ∧
        (r = pendOff M k ∨ r = off M 5) := by
  have := tr_bounds M q (T.nth 0)
  refine (((Spec.flatMap_one (Q := fun j r ↦ j = d ∧ r = pendOff M k ∨ written M q T j r ∨
      j = 0 ∧ r = off M 5) _ (List.nodup_finRange _) _ ⟨k, hk⟩
      (List.mem_finRange _) ?_ ?_ ?_).seq (Spec.ifOn
        (Spec.inc_at (d := d) (o := off M 5) (by ring) (by arith) (by arith)))).seq
      (Spec.shiftBlocks d)).post (by arith_flags)
  · exact Spec.ifOn ((Spec.inc_at (d := d) (o := pendOff M k) (by simp; ring)
      (by arith) (by arith)).post (by arith_flags))
  · intro i _ h; have := Fin.val_ne_of_ne h; exact Spec.ifOff
  · intro i _ h; have := Fin.val_ne_of_ne h; exact Spec.ifOff

theorem move_spec (T : Tape Γ) (q : Λ) :
    Spec (width M) (ifFlag (off M 3) (carry M (-1)) ++ ifFlag (off M 4) (carry M 1)) 0
      (fun j r ↦ written M q T j r ∨ j = 0 ∧ pendFlags M q (T.nth 0) r) 0
      fun j r ↦ moved M q T j r ∨ j = 0 ∧ (tr M q (T.nth 0)).2.2.1 = 1 ∧
        (r = pendOff M (tr M q (T.nth 0)).2.1 ∨ r = off M 5) := by
  have := tr_bounds M q (T.nth 0)
  by_cases hL : (tr M q (T.nth 0)).2.2.2.1 = 1
  · exact ((Spec.ifOn ((carry_spec M T q (-1) (by simp) _ this.2.1).pre (by arith_flags))).seq (Spec.ifOff)).post (by arith_flags)
  · by_cases hR : (tr M q (T.nth 0)).2.2.2.2 = 1
    · exact ((Spec.ifOff).seq (Spec.ifOn ((carry_spec M T q 1 (by simp) _
        this.2.1).pre (by arith_flags)))).post (by arith_flags)
    · exact ((Spec.ifOff).seq (Spec.ifOff)).post (by arith_flags)

theorem commit_spec (T : Tape Γ) (q : Λ) :
    Spec (width M) (commit M) 0 (fun j r ↦ moved M q T j r ∨ j = 0 ∧ (tr M q (T.nth 0)).2.2.1 = 1 ∧
        (r = pendOff M (tr M q (T.nth 0)).2.1 ∨ r = off M 5)) 0
      fun j r ↦ moved M q T j r ∨ j = 0 ∧ (tr M q (T.nth 0)).2.2.1 = 1 ∧
        (r = stateOff M ((tr M q (T.nth 0)).2.1) ∨ r = off M 5) := by
  have := tr_bounds M q (T.nth 0)
  unfold commit
  by_cases hc : (tr M q (T.nth 0)).2.2.1 = 1
  · refine Spec.flatMap_one _ (List.nodup_finRange _) _ ⟨_, this.2.1⟩ (List.mem_finRange _) ?_ ?_ ?_
    · exact Spec.ifOn ((Spec.inc_at (d := 0) (o := stateOff M ((tr M q (T.nth 0)).2.1))
        (by simp) (by arith) (by arith)).post (by arith_flags))
    · intro i _ h; have := Fin.val_ne_of_ne h; exact Spec.ifOff
    · intro i _ _; exact Spec.ifOff
  · exact (Spec.flatMap_id _ _ fun i _ ↦ Spec.ifOff).post fun _ _ _ ↦ by simp only [hc, false_and, and_false, or_false]

theorem body_spec (T : Tape Γ) (q : Λ) :
    Spec (width M) (body M) 0 (fun j r ↦ symFlag T j r ∨ j = 0 ∧ r = stateOff M (idx Λ q)) 0
      fun j r ↦ moved M q T j r ∨ j = 0 ∧ (tr M q (T.nth 0)).2.2.1 = 1 ∧
        (r = stateOff M ((tr M q (T.nth 0)).2.1) ∨ r = off M 5) := by
  rw [body]; exact (((dispatch_spec M T q).seq (flush_spec M T q)).seq (move_spec M T q)).seq (commit_spec M T q)

/-! ## TM steps, the loop, and the claim -/

theorem tm_step (q : Λ) (T : Tape Γ) :
    (TM0.step M ⟨q, T⟩ = none ∧ (tr M q (T.nth 0)).2.2.1 = 0) ∨
    ∃ c', TM0.step M ⟨q, T⟩ = some c' ∧ (tr M q (T.nth 0)).2.2.1 = 1 ∧
      (idx Λ c'.q : ℕ) = (tr M q (T.nth 0)).2.1 ∧ ∀ j r, symFlag c'.Tape j r ↔ moved M q T j r := by
  rcases h : M q T.head with _ | ⟨q', d | b⟩
  · left; simp [TM0.step, tr, h]
  · right; cases d
    · refine ⟨⟨q', T.move .left⟩, by simp [TM0.step, h], by simp [tr, h], by simp [tr, h],
        fun j r ↦ ?_⟩
      rcases eq_or_ne j 1 with rfl | h1 <;>
        simp [symFlag, moved, written, tr, h, Tape.move_left_nth, sub_eq_add_neg] <;> omega
    · refine ⟨⟨q', T.move .right⟩, by simp [TM0.step, h], by simp [tr, h], by simp [tr, h],
        fun j r ↦ ?_⟩
      rcases eq_or_ne j (-1) with rfl | h1 <;>
        simp [symFlag, moved, written, tr, h, Tape.move_right_nth] <;> omega
  · right
    refine ⟨⟨q', T.write b⟩, by simp [TM0.step, h], by simp [tr, h], by simp [tr, h],
      fun j r ↦ ?_⟩
    have hw : (T.write b).head = b := rfl
    rcases eq_or_ne j 0 with rfl | h1 <;> simp [symFlag, moved, written, tr, h, hw, Tape.write_nth, *]

def loopBody : Program := .dec :: shift (-↑(runOff M)) ++ body M ++ shift ↑(runOff M)

def cfgFlags (c : TM0.Cfg Γ Λ) (j : ℤ) (r : ℕ) : Prop :=
  symFlag c.Tape j r ∨ j = 0 ∧ (r = stateOff M (idx Λ c.q) ∨ r = runOff M)

theorem iterate (q : Λ) (T : Tape Γ) (t : Tape Cell) (ht : Holds (width M) (runOff M) (cfgFlags M ⟨q, T⟩) t) :
    ∃ u, Holds (width M) (runOff M) (fun j r ↦ moved M q T j r ∨ j = 0 ∧ (tr M q (T.nth 0)).2.2.1 = 1 ∧
        (r = stateOff M ((tr M q (T.nth 0)).2.1) ∨ r = off M 5)) u ∧
      Reaches₁ step ⟨.loop (loopBody M) :: shift (-↑(runOff M)), t⟩ ⟨.loop (loopBody M) :: shift (-↑(runOff M)), u⟩ := by
  have h1 : cfgFlags M ⟨q, T⟩ 0 (runOff M) := Or.inr ⟨rfl, Or.inr rfl⟩
  obtain ⟨u, hu, r⟩ := ((((Spec.dec (d := 0) (o := runOff M) (by simp) (by simp [width, runOff]) h1).seq
    (Spec.shift_by (c := 0) (x := -↑(runOff M)) (by simp))).seq ((body_spec M T q).pre (by simp only [cfgFlags]; arith_flags))).seq (Spec.shift_by (c := ↑(runOff M)) (x := ↑(runOff M)) (by simp))) t ht
  exact ⟨u, hu, .head' (by simp [step, loopBody, head_eq ht (d := 0) (o := runOff M) (by simp) (by simp [width, runOff]),
    h1]) (r _)⟩

theorem exit (P : ℤ → ℕ → Prop) (t : Tape Cell) (ht : Holds (width M) (runOff M) P t) (h0 : ¬P 0 (runOff M)) :
    ∃ u, Holds (width M) 0 P u ∧ Reaches step ⟨.loop (loopBody M) :: shift (-↑(runOff M)), t⟩ ⟨[], u⟩ := by
  obtain ⟨u, hu, r⟩ := ((Spec.skip (B := loopBody M) (d := 0) (o := runOff M) (by simp) (by simp [width, runOff]) h0).seq
    (Spec.shift_by (c := 0) (x := -↑(runOff M)) (by simp))) t ht
  exact ⟨u, hu, by simpa using r []⟩

def Tr (c₁ : TM0.Cfg Γ Λ) (c₂ : Cfg) : Prop :=
  TM0.step M c₁ = none ∧ (∃ t, Holds (width M) 0 (symFlag c₁.Tape) t ∧ c₂ = ⟨[], t⟩) ∨
  (TM0.step M c₁).isSome ∧ ∃ t, Holds (width M) (runOff M) (cfgFlags M c₁) t ∧
    c₂ = ⟨.loop (loopBody M) :: shift (-↑(runOff M)), t⟩

theorem loop_spec (c : TM0.Cfg Γ Λ) (t : Tape Cell) (ht : Holds (width M) (runOff M) (cfgFlags M c) t) :
    ∃ c₂, Tr M c c₂ ∧ Reaches step ⟨.loop (loopBody M) :: shift (-↑(runOff M)), t⟩ c₂ := by
  obtain ⟨q, T⟩ := c
  rcases tm_step M q T with ⟨hs, hc⟩ | ⟨c', hs, -⟩
  · have := tr_bounds M q (T.nth 0)
    obtain ⟨u, hu, r⟩ := iterate M q T t ht
    obtain ⟨v, hv, r'⟩ := exit M _ u hu (by arith)
    exact ⟨⟨[], v⟩, .inl ⟨hs, v, hv.congr (by arith_flags), rfl⟩, r.to_reflTransGen.trans r'⟩
  · exact ⟨_, .inr ⟨by simp [hs], t, ht, rfl⟩, .refl⟩

theorem respects : Respects (TM0.step M) step (Tr M) := by
  rintro ⟨q, T⟩ c₂ h
  rcases tm_step M q T with ⟨hs, -⟩ | ⟨c', hs, hc, hq, hT⟩ <;> simp only [hs]
  · rcases h with ⟨-, t, -, rfl⟩ | ⟨h, -⟩
    · rfl
    · simp [hs] at h
  · rcases h with ⟨h, -⟩ | ⟨-, t, ht, rfl⟩
    · simp [hs] at h
    obtain ⟨u, hu, r⟩ := iterate M q T t ht
    obtain ⟨c₂, h, r'⟩ := loop_spec M c' u (hu.congr fun j r _ ↦ by simp only [cfgFlags, hT, hq, hc, runOff, off, true_and])
    exact ⟨c₂, h, r.trans_left r'⟩

def enc (a : Γ) : List Cell := (List.range (width M)).map fun i ↦ if i + 1 = (idx Γ a : ℕ) then 1 else 0

theorem getI_flatMap {α β : Type*} [Inhabited α] [Inhabited β] (f : α → List β) (w : ℕ) (hw : 0 < w)
    (hl : ∀ a, (f a).length = w) (hd : f default = List.replicate w default) (l : List α) (i : ℕ) :
    (l.flatMap f).getI i = (f (l.getI (i / w))).getI (i % w) := by
  induction l generalizing i with
  | nil =>
    rw [List.flatMap_nil, List.getI_nil, List.getI_nil, hd,
      List.getI_eq_getElem _ (by simpa using Nat.mod_lt _ hw)]
    simp
  | cons a l ih =>
    rw [List.flatMap_cons]
    by_cases hi : i < w
    · rw [List.getI_append _ _ _ (by rw [hl]; exact hi), Nat.div_eq_of_lt hi,
        Nat.mod_eq_of_lt hi, List.getI_cons_zero]
    · rw [List.getI_append_right _ _ _ (by rw [hl]; omega), hl, ih,
        Nat.div_eq_sub_div hw (by omega : w ≤ i), Nat.mod_eq_sub_mod (by omega : w ≤ i),
        List.getI_cons_succ]

theorem enc_getI (a : Γ) {r : ℕ} (hr : r < width M) :
    (enc M a).getI r = if r + 1 = (idx Γ a : ℕ) then 1 else 0 := by
  rw [enc, List.getI_eq_getElem _ (by simpa using hr)]; simp

theorem enc_default : enc M default = List.replicate (width M) default := by
  simp [enc, idx_default, List.map_const', default]

theorem width_pos : 0 < width M := by simp [width]

theorem enc_injective : Function.Injective (enc M) := by
  intro a b h
  apply (idx Γ).injective
  ext
  have := (idx Γ a).isLt
  have := (idx Γ b).isLt
  have k : (enc M a).getI (max (idx Γ a : ℕ) (idx Γ b) - 1) =
      (enc M b).getI (max (idx Γ a : ℕ) (idx Γ b) - 1) := by rw [h]
  rw [enc_getI _ _ (by simp [width]; omega), enc_getI _ _ (by simp [width]; omega)] at k
  by_contra hne
  split_ifs at k <;> first | omega | simp at k

theorem mk₁_nth {α} [Inhabited α] (l : List α) (k : ℕ) : (Tape.mk₁ l).nth k = l.getI k := by
  simp [Tape.mk₁, Tape.mk₂, ListBlank.nth_mk]

theorem mk₁_nth_neg {α} [Inhabited α] (l : List α) (i : ℤ) (hi : i < 0) : (Tape.mk₁ l).nth i = default := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = Int.negSucc k := ⟨(-i - 1).toNat, by rw [Int.negSucc_eq]; omega⟩
  rfl

theorem init_holds (l : List Γ) : Holds (width M) 0 (symFlag (Tape.mk₁ l)) (Tape.mk₁ (l.flatMap (enc M))) := by
  intro j r hr
  rw [sub_zero]
  rcases lt_or_ge j 0 with hj | hj
  · have : (width M : ℤ) * j ≤ -(width M) := by nlinarith
    rw [mk₁_nth_neg _ _ (by omega), symFlag, mk₁_nth_neg _ _ hj]
    simp [idx_default]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    rw [show (width M : ℤ) * k + r = ((width M * k + r : ℕ) : ℤ) by push_cast; ring, mk₁_nth,
      getI_flatMap _ _ (width_pos M) (fun _ ↦ by simp [enc]) (enc_default M), Nat.mul_add_div (width_pos M), Nat.div_eq_of_lt hr,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hr, enc_getI _ _ hr, symFlag, mk₁_nth, add_zero]
    by_cases hc : r + 1 = (idx Γ (l.getI k) : ℕ) <;> simp [hc]

theorem right₀_eq (T : Tape Γ) (t : Tape Cell) (h : Holds (width M) 0 (symFlag T) t) :
    t.right₀ = T.right₀.flatMap (enc M) ⟨width M, enc_default M⟩ := by
  apply ListBlank.ext
  intro i
  have key : ∀ L : ListBlank Γ, (L.flatMap (enc M) ⟨width M, enc_default M⟩).nth i =
      (enc M (L.nth (i / width M))).getI (i % width M) := fun L ↦ L.induction_on fun l ↦ by
    simp only [ListBlank.flatMap_mk, ListBlank.nth_mk]
    exact getI_flatMap _ _ (width_pos M) (fun _ ↦ by simp [enc]) (enc_default M) l i
  have hr : i % width M < width M := Nat.mod_lt _ (width_pos M)
  rw [Tape.right₀_nth, key, Tape.right₀_nth, enc_getI _ _ hr]
  have := h (i / width M : ℕ) (i % width M) hr
  rw [sub_zero, show ((width M : ℤ) * ((i / width M : ℕ) : ℤ) + ((i % width M : ℕ) : ℤ)) = (i : ℤ) by
    exact_mod_cast Nat.div_add_mod i (width M)] at this
  rw [this, symFlag]
  by_cases hc : i % width M + 1 = (idx Γ (T.nth ↑(i / width M)) : ℕ) <;> simp [hc]

theorem eval_eq (l : List Γ) : eval (program M) (l.flatMap (enc M)) =
    (TM0.eval M l).map fun L ↦ L.flatMap (enc M) ⟨width M, enc_default M⟩ := by
  obtain ⟨t1, ht1, hr1⟩ := ((Spec.inc_at (d := 0) (o := stateOff M (idx Λ default))
    (x := (stateOff M (idx Λ default) : ℕ)) (by simp) (by arith) (by arith)).seq
    ((Spec.inc_at (d := 0) (o := runOff M) (x := (runOff M : ℕ)) (by simp) (by arith) (by arith)).seq
      (Spec.shift_by (c := ↑(runOff M)) (x := ↑(runOff M)) (by simp)))) _ (init_holds M l)
  obtain ⟨c₂, htr, hr⟩ := loop_spec M (TM0.init l) t1 (ht1.congr (by simp only [cfgFlags, TM0.init]; arith_flags))
  have h0 : Reaches step (init (program M) (l.flatMap (enc M))) ⟨.loop (loopBody M) :: shift (-↑(runOff M)), t1⟩ := by
    have := hr1 ([.loop (loopBody M)] ++ shift (-↑(runOff M)))
    simpa [init, program, ifFlag, loopBody, runOff, off, List.append_assoc] using this
  have e1 := reaches_eval (h0.trans hr)
  unfold eval TM0.eval
  rw [e1]
  ext x
  simp only [Part.map_map, Part.mem_map_iff, Function.comp]
  constructor
  · rintro ⟨b₂, hb₂, rfl⟩
    obtain ⟨c₁, htr', hc₁⟩ := tr_eval_rev (respects M) htr hb₂
    have hs : TM0.step M c₁ = none := (mem_eval.1 hc₁).2
    rcases htr' with ⟨_, t, ht, rfl⟩ | ⟨h, _⟩
    · exact ⟨c₁, hc₁, (right₀_eq M c₁.Tape t ht).symm⟩
    · simp [hs] at h
  · rintro ⟨c₁, hc₁, rfl⟩
    obtain ⟨b₂, htr', hb₂⟩ := tr_eval (respects M) htr hc₁
    have hs : TM0.step M c₁ = none := (mem_eval.1 hc₁).2
    rcases htr' with ⟨_, t, ht, rfl⟩ | ⟨h, _⟩
    · exact ⟨_, hb₂, right₀_eq M c₁.Tape t ht⟩
    · simp [hs] at h

theorem claim : Claim := fun M ↦ ⟨⟨width M, enc M, fun _ ↦ by simp [enc], enc_default M, enc_injective M⟩, program M, eval_eq M⟩

end BF.Elegant
