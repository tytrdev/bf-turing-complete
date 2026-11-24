import BfTuringComplete.Core.Statement
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
set_option maxHeartbeats 1000000
namespace BF.G
open Turing StateTransition Relation Classical Fintype

def Rn (p : Program) (t u : Tape Cell) := ∀ k, Reaches step ⟨p ++ k, t⟩ ⟨k, u⟩

theorem Rn.ap {p q : Program} {t u v : Tape Cell} (h : Rn p t u) (g : Rn q u v) :
    Rn (p ++ q) t v := fun k ↦ by rw [List.append_assoc]; exact (h _).trans (g k)

theorem rep (c : Stmt) (F : Tape Cell → Tape Cell) (s : ℤ)
    (hc : ∀ k t, step ⟨c :: k, t⟩ = some ⟨k, F t⟩) (hF : ∀ t i, (F t).nth i = t.nth (i + s)) :
    ∀ (n : ℕ) (t : Tape Cell), ∃ u, Rn (.replicate n c) t u ∧ ∀ i, u.nth i = t.nth (i + n * s)
  | 0, t => ⟨t, fun _ ↦ .refl, by simp⟩
  | n + 1, t => by
    obtain ⟨u, h, e⟩ := rep c F s hc hF n (F t)
    exact ⟨u, fun k ↦ .head (hc _ t) (h k), fun i ↦ by rw [e, hF]; congr 1; push_cast; ring⟩

def mv (x : ℤ) : Program :=
  if 0 ≤ x then .replicate x.toNat .right else .replicate (-x).toNat .left

theorem rmv (x : ℤ) (t : Tape Cell) : ∃ u, Rn (mv x) t u ∧ ∀ i, u.nth i = t.nth (i + x) := by
  unfold mv; split_ifs
  · obtain ⟨u, r, e⟩ := rep .right (·.move .right) 1 (fun _ _ ↦ rfl) (by simp) x.toNat t
    exact ⟨u, r, fun i ↦ by rw [e]; congr 1; omega⟩
  · obtain ⟨u, r, e⟩ := rep .left (·.move .left) (-1) (fun _ _ ↦ rfl)
      (by simp [sub_eq_add_neg]) (-x).toNat t
    exact ⟨u, r, fun i ↦ by rw [e]; congr 1; omega⟩

/-- Tape `t` holds flags `P` in blocks of width `w`, viewed from base offset `b`. -/
def H (w : ℕ) (b : ℤ) (P : ℤ → ℕ → Prop) (t : Tape Cell) : Prop :=
  ∀ j (r : ℕ), r < w → t.nth (w * j + r - b) = if P j r then 1 else 0

def S (w : ℕ) (p : Program) (b : ℤ) (P : ℤ → ℕ → Prop) (c : ℤ) (Q : ℤ → ℕ → Prop) : Prop :=
  ∀ t, H w b P t → ∃ u, H w c Q u ∧ Rn p t u

variable {w o : ℕ} {p q B : Program} {b c d x : ℤ} {P Q R : ℤ → ℕ → Prop}

theorem S.ap (h : S w p b P c Q) (g : S w q c Q d R) : S w (p ++ q) b P d R := fun t ht ↦ by
  obtain ⟨u, hu, r⟩ := h t ht
  obtain ⟨v, hv, r'⟩ := g u hu
  exact ⟨v, hv, r.ap r'⟩

theorem S.nil : S w [] b P b P := fun t h ↦ ⟨t, h, fun _ ↦ .refl⟩

theorem S.cq {P' Q' : ℤ → ℕ → Prop} (h : S w p b P c Q) (e₁ : ∀ j r, r < w → (P' j r ↔ P j r))
    (e₂ : ∀ j r, r < w → (Q j r ↔ Q' j r)) : S w p b P' c Q' := fun t ht ↦ by
  obtain ⟨u, hu, r⟩ := h t fun j r hr ↦ by rw [ht j r hr]; simp [e₁ j r hr]
  exact ⟨u, fun j r hr ↦ by rw [hu j r hr]; simp [e₂ j r hr], r⟩

theorem S.cr {Q' : ℤ → ℕ → Prop} (h : S w p b P c Q) (e : ∀ j r, r < w → (Q j r ↔ Q' j r)) :
    S w p b P c Q' := h.cq (fun _ _ _ ↦ .rfl) e

theorem S.cl {P' : ℤ → ℕ → Prop} (h : S w p b P c Q) (e : ∀ j r, r < w → (P' j r ↔ P j r)) :
    S w p b P' c Q := h.cq e fun _ _ _ ↦ .rfl

theorem H.cq {t : Tape Cell} (h : H w b P t) (e : ∀ j r, r < w → (P j r ↔ Q j r)) : H w b Q t :=
  fun j r hr ↦ by rw [h j r hr]; simp [e j r hr]

theorem S.mo (h : c = b + x) : S w (mv x) b P c P := fun t ht ↦ by
  obtain ⟨u, r, e⟩ := rmv x t
  exact ⟨u, fun j k hk ↦ by rw [e, ← ht j k hk, h]; congr 1; ring, r⟩

theorem bk {j : ℤ} {r : ℕ} (hr : r < w) (ho : o < w) :
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

theorem hd {t : Tape Cell} (ht : H w b P t) (hb : b = w * d + o) (ho : o < w) :
    t.head = if P d o then 1 else 0 := by
  rw [← ht d o ho, hb]; simp

theorem S.tg (cm : Stmt) (g : Cell → Cell)
    (hc : ∀ k t, step ⟨cm :: k, t⟩ = some ⟨k, t.write (g t.head)⟩)
    (hb : b = w * d + o) (ho : o < w) (hg : g (if P d o then 1 else 0) = if Q d o then 1 else 0)
    (hQ : ∀ j r, ¬(j = d ∧ r = o) → (Q j r ↔ P j r)) : S w [cm] b P b Q := fun t ht ↦
  ⟨_, fun j r hr ↦ by
    rw [Tape.write_nth]
    by_cases h : (w : ℤ) * j + r - b = 0
    · obtain ⟨rfl, rfl⟩ := (bk hr ho).1 (hb ▸ h)
      rw [if_pos h, hd ht hb ho, hg]
    · rw [if_neg h, ht j r hr]
      simp [hQ j r fun ⟨h1, h2⟩ ↦ h (by rw [h1, h2, hb]; ring)], fun _ ↦ .single (hc _ _)⟩

theorem S.inc (hb : b = w * d + o) (ho : o < w) (h0 : ¬P d o) :
    S w [.inc] b P b fun j r ↦ j = d ∧ r = o ∨ P j r :=
  S.tg _ (· + 1) (fun _ _ ↦ rfl) hb ho (by simp [h0]) fun j r h ↦ by simp [h]

theorem S.dec (hb : b = w * d + o) (ho : o < w) (h1 : P d o) :
    S w [.dec] b P b fun j r ↦ ¬(j = d ∧ r = o) ∧ P j r :=
  S.tg _ (· - 1) (fun _ _ ↦ rfl) hb ho (by simp [h1]) fun j r h ↦ by simp [h]

theorem S.l0 (hb : b = w * d + o) (ho : o < w) (h0 : ¬P d o) : S w [.loop B] b P b P :=
  fun t ht ↦ ⟨t, ht, fun _ ↦ .single (by simp [step, hd ht hb ho, h0])⟩

theorem S.l1 (hb : b = w * d + o) (ho : o < w) (h1 : P d o) (hB : S w B b P b Q)
    (hl : S w [.loop B] b Q b R) : S w [.loop B] b P b R := fun t ht ↦ by
  obtain ⟨u, hu, r⟩ := hB t ht
  obtain ⟨v, hv, r'⟩ := hl u hu
  exact ⟨v, hv, fun k ↦ .head (by simp [step, hd ht hb ho, h1]) ((r _).trans (r' k))⟩

set_option hygiene false in
macro "om" : tactic => `(tactic|
  (simp (config := { failIfUnchanged := false }) only [sy, S0, NX, AP, RP, W, Rf, ne_eq,
    false_and, and_false, false_or, or_false, iff_def, false_implies, imp_false, true_and,
    and_true, not_true_eq_false, not_false_eq_true, true_or, or_true, true_implies,
    implies_true, and_self, or_self, eq_self_iff_true, Fin.val_mk, iff_self] at * <;> omega))

set_option hygiene false in
macro "oi" : tactic => `(tactic| (intro j r hr; by_cases hj : j = 0 <;> (try subst hj) <;> om))

def IF (o : ℕ) (B : Program) : Program :=
  mv o ++ [.loop (.dec :: mv (-o) ++ B ++ mv o)] ++ mv (-o)
def ia (x : ℤ) : Program := mv x ++ .inc :: mv (-x)
def da (x : ℤ) : Program := mv x ++ .dec :: mv (-x)

theorem S.si (hx : x = w * d + o) (ho : o < w) (h0 : ¬P d o) :
    S w (ia x) 0 P 0 fun j r ↦ j = d ∧ r = o ∨ P j r :=
  (S.mo (c := x) (by simp)).ap ((S.inc hx ho h0).ap (S.mo (by simp)))

theorem S.sd (ho : o < w) (h1 : P 0 o) :
    S w (da o) 0 P 0 fun j r ↦ ¬(j = 0 ∧ r = o) ∧ P j r :=
  (S.mo (c := o) (by simp)).ap ((S.dec (d := 0) (by simp) ho h1).ap (S.mo (by simp)))

theorem S.i0 (ho : o < w := by om) (h0 : ¬P 0 o := by om) : S w (IF o B) 0 P 0 P :=
  ((S.mo (c := o) (by simp)).ap (S.l0 (d := 0) (by simp) ho h0)).ap (S.mo (by simp))

theorem S.i1 (hB : S w B 0 (fun j r ↦ ¬(j = 0 ∧ r = o) ∧ P j r) 0 Q)
    (ho : o < w := by om) (h1 : P 0 o := by om) (hQ : ¬Q 0 o := by om) :
    S w (IF o B) 0 P 0 Q :=
  ((S.mo (c := o) (by simp)).ap (S.l1 (d := 0) (by simp) ho h1
    ((((S.dec (d := 0) (by simp) ho h1).ap (S.mo (c := 0) (by simp))).ap hB).ap
      (S.mo (by simp))) (S.l0 (d := 0) (by simp) ho hQ))).ap (S.mo (by simp))

theorem S.bm (d : ℤ) : S w (mv (↑w * d)) 0 P 0 fun j r ↦ P (j + d) r := fun t ht ↦ by
  obtain ⟨u, hu, r⟩ := S.mo (c := ↑w * d) (x := ↑w * d) (by simp) t ht
  exact ⟨u, fun j k hk ↦ by rw [← hu (j + d) k hk]; congr 1; ring, r⟩

theorem S.fN {α} (L : List α) (g : α → Program) (h : ∀ x ∈ L, S w (g x) 0 P 0 P) :
    S w (L.flatMap g) 0 P 0 P := by
  induction L with
  | nil => exact S.nil
  | cons x L ih =>
    rw [List.flatMap_cons]
    exact (h x (by simp)).ap (ih fun y hy ↦ h y (by simp [hy]))

theorem S.f1 {α} [DecidableEq α] (L : List α) (hL : L.Nodup) (g : α → Program) (a : α)
    (ha : a ∈ L) (hA : S w (g a) 0 P 0 Q) (hP : ∀ x ∈ L, x ≠ a → S w (g x) 0 P 0 P)
    (hQ : ∀ x ∈ L, x ≠ a → S w (g x) 0 Q 0 Q) : S w (L.flatMap g) 0 P 0 Q := by
  induction L with
  | nil => simp at ha
  | cons x L ih =>
    rw [List.flatMap_cons]
    obtain ⟨hx, hL⟩ := List.nodup_cons.1 hL
    by_cases hxa : x = a
    · subst hxa
      exact hA.ap (S.fN L g fun y hy ↦ hQ y (by simp [hy]) fun h ↦ hx (h ▸ hy))
    · exact (hP x (by simp) hxa).ap (ih hL (by simpa [Ne.symm hxa] using ha)
        (fun y hy ↦ hP y (by simp [hy])) fun y hy ↦ hQ y (by simp [hy]))

theorem S.oi {C : Prop} [Decidable C] {x : ℕ} (hx : x < w) (h0 : C → ¬P 0 x) :
    S w (if C then ia x else []) 0 P 0 fun j r ↦ j = 0 ∧ r = x ∧ C ∨ P j r := by
  split_ifs with h
  · exact (S.si (d := 0) (by simp) hx (h0 h)).cr fun j r _ ↦ by simp [h]
  · exact S.nil.cr fun j r _ ↦ by simp [h]

/-! ## The machine -/

def E (α) [Fintype α] [Inhabited α] : α ≃ Fin (card α - 1 + 1) :=
  let e := (equivFin α).trans (finCongr (by have : 0 < card α := card_pos; omega))
  e.trans (Equiv.swap (e default) 0)

theorem E0 (α) [Fintype α] [Inhabited α] : E α default = 0 := by simp [E]

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Fintype Γ] [Fintype Λ] (M : TM0.Machine Γ Λ)

def W (M : TM0.Machine Γ Λ) := 2 * (card Γ - 1) + 2 * (card Λ - 1) + 6
def Rf (M : TM0.Machine Γ Λ) := 2 * (card Γ - 1) + 2 * (card Λ - 1) + 5

/-- What a transition does: (new symbol, next state, continues?, moves left?, moves right?). -/
def D (q : Λ) (a : Γ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  match M q a with
  | none => (E Γ a, 0, 0, 0, 0)
  | some (q', .move .left) => (E Γ a, E Λ q', 1, 1, 0)
  | some (q', .move .right) => (E Γ a, E Λ q', 1, 0, 1)
  | some (q', .write b) => (E Γ b, E Λ q', 1, 0, 0)

theorem DB (q : Λ) (a : Γ) : (D M q a).1 < (card Γ - 1) + 1 ∧ (D M q a).2.1 < (card Λ - 1) + 1 ∧
    (D M q a).2.2.1 ≤ 1 ∧ (D M q a).2.2.2.1 + (D M q a).2.2.2.2 ≤ (D M q a).2.2.1 ∧
    ((D M q a).2.2.1 = 0 ∨ (D M q a).2.2.2.1 + (D M q a).2.2.2.2 = 1 → (D M q a).1 = E Γ a) := by
  unfold D; rcases M q a with _ | ⟨q', d | b⟩ <;> (try cases d) <;> simp

def act (q : Λ) (a : Γ) : Program :=
  (if (D M q a).1 ≠ 0 then ia ((card Γ - 1) + (D M q a).1 - 1 : ℕ) else []) ++
  (if (D M q a).2.2.2.1 = 1 then ia (2 * (card Γ - 1) + 2 * (card Λ - 1) + 3 : ℕ) else []) ++
  (if (D M q a).2.2.2.2 = 1 then ia (2 * (card Γ - 1) + 2 * (card Λ - 1) + 4 : ℕ) else []) ++
  (if (D M q a).2.2.1 = 1 then ia (2 * (card Γ - 1) + (card Λ - 1) + 1 + (D M q a).2.1 : ℕ) else []) ++
  (if (D M q a).2.2.1 = 1 then ia (2 * (card Γ - 1) + 2 * (card Λ - 1) + 5 : ℕ) else [])

def ds (q : Λ) : Program :=
  ia (2 * (card Γ - 1) + 2 * (card Λ - 1) + 2 : ℕ) ++ (List.finRange ((card Γ - 1))).flatMap (fun i : Fin _ ↦
    IF i (da (2 * (card Γ - 1) + 2 * (card Λ - 1) + 2 : ℕ) ++ act M q ((E Γ).symm i.succ))) ++
  IF (2 * (card Γ - 1) + 2 * (card Λ - 1) + 2) (act M q default)

def dp : Program := (List.finRange ((card Λ - 1) + 1)).flatMap fun i : Fin _ ↦ IF (2 * (card Γ - 1) + i) (ds M ((E Λ).symm i))
def fl (_ : TM0.Machine Γ Λ) : Program := (List.finRange ((card Γ - 1))).flatMap fun i : Fin _ ↦ IF ((card Γ - 1) + i) (ia (i : ℕ))
def cb (d : ℤ) : Program :=
  (List.finRange ((card Λ - 1) + 1)).flatMap (fun i : Fin _ ↦
    IF (2 * (card Γ - 1) + (card Λ - 1) + 1 + i) (ia (↑(2 * (card Γ - 1) + (card Λ - 1) + 1 + i : ℕ) + ↑(W M) * d))) ++
  IF (2 * (card Γ - 1) + 2 * (card Λ - 1) + 5) (ia (↑(2 * (card Γ - 1) + 2 * (card Λ - 1) + 5 : ℕ) + ↑(W M) * d)) ++ mv (↑(W M) * d)
def cm (_ : TM0.Machine Γ Λ) : Program :=
  (List.finRange ((card Λ - 1) + 1)).flatMap fun i : Fin _ ↦ IF (2 * (card Γ - 1) + (card Λ - 1) + 1 + i) (ia (2 * (card Γ - 1) + i : ℕ))
def bd : Program :=
  dp M ++ fl M ++ (IF (2 * (card Γ - 1) + 2 * (card Λ - 1) + 3) (cb M (-1)) ++ IF (2 * (card Γ - 1) + 2 * (card Λ - 1) + 4) (cb M 1)) ++
    cm M
def pg : Program :=
  ia (2 * (card Γ - 1) + E Λ default : ℕ) ++ ia (2 * (card Γ - 1) + 2 * (card Λ - 1) + 5 : ℕ) ++ IF (2 * (card Γ - 1) + 2 * (card Λ - 1) + 5) (bd M)

/-! ## Flag predicates -/

def sy (T : Tape Γ) (j : ℤ) (r : ℕ) : Prop := r + 1 = E Γ (T.nth j)

def RP (q : Λ) (a : Γ) (r : ℕ) : Prop :=
  (D M q a).2.2.2.1 = 1 ∧ r = 2 * (card Γ - 1) + 2 * (card Λ - 1) + 3 ∨ (D M q a).2.2.2.2 = 1 ∧ r = 2 * (card Γ - 1) + 2 * (card Λ - 1) + 4 ∨
  (D M q a).2.2.1 = 1 ∧ r = 2 * (card Γ - 1) + (card Λ - 1) + 1 + (D M q a).2.1 ∨
  (D M q a).2.2.1 = 1 ∧ r = 2 * (card Γ - 1) + 2 * (card Λ - 1) + 5

def AP (q : Λ) (a : Γ) (r : ℕ) : Prop :=
  (D M q a).1 ≠ 0 ∧ r = (card Γ - 1) + (D M q a).1 - 1 ∨ RP M q a r

def S0 (q : Λ) (T : Tape Γ) (j : ℤ) (r : ℕ) : Prop :=
  j ≠ 0 ∧ sy T j r ∨ j = 0 ∧ r + 1 = (D M q (T.nth 0)).1

def NX (q : Λ) (T : Tape Γ) (j : ℤ) (r : ℕ) : Prop :=
  (D M q (T.nth 0)).2.2.2.1 = 1 ∧ S0 M q T (j + -1) r ∨
  (D M q (T.nth 0)).2.2.2.2 = 1 ∧ S0 M q T (j + 1) r ∨
  (D M q (T.nth 0)).2.2.2.1 = 0 ∧ (D M q (T.nth 0)).2.2.2.2 = 0 ∧ S0 M q T j r


/-! ## Phases -/

theorem sAct (T : Tape Γ) (q : Λ) (a : Γ) :
    S (W M) (act M q a) 0 (fun j r ↦ j ≠ 0 ∧ sy T j r) 0
      fun j r ↦ j ≠ 0 ∧ sy T j r ∨ j = 0 ∧ AP M q a r := by
  have := DB M q a
  unfold act
  refine (((((S.oi ?_ ?_).ap (S.oi ?_ ?_)).ap (S.oi ?_ ?_)).ap (S.oi ?_ ?_)).ap
    (S.oi ?_ ?_)).cr ?_
  all_goals first | om | oi

theorem dsS (T : Tape Γ) (q : Λ) :
    S (W M) (ds M q) 0 (sy T) 0 fun j r ↦ j ≠ 0 ∧ sy T j r ∨ j = 0 ∧ AP M q (T.nth 0) r := by
  have := DB M q (T.nth 0)
  have I := S.si (w := W M) (P := sy T) (d := 0) (o := 2 * (card Γ - 1) + 2 * (card Λ - 1) + 2)
    (x := (2 * (card Γ - 1) + 2 * (card Λ - 1) + 2 : ℕ)) (by simp)
    (by om) (by om)
  unfold ds
  by_cases ha : (E Γ (T.nth 0) : ℕ) = 0
  · have e : T.nth 0 = default := (E Γ).injective (Fin.ext (by rw [ha, E0]; rfl))
    refine (I.ap (S.fN _ _ fun i _ ↦ S.i0)).ap ?_
    rw [e] at this ⊢
    exact S.i1 ((sAct M T q default).cl (by oi))
  · obtain ⟨i₀, hi⟩ : ∃ i₀ : Fin ((card Γ - 1)), i₀.val + 1 = E Γ (T.nth 0) :=
      ⟨⟨(E Γ (T.nth 0) : ℕ) - 1, by have := (E Γ (T.nth 0)).isLt; omega⟩,
        by simp only; omega⟩
    have hs : (E Γ).symm i₀.succ = T.nth 0 :=
      (E Γ).symm_apply_eq.2 (Fin.ext (by simp only [Fin.val_succ]; omega))
    refine (I.ap (S.f1 _ (List.nodup_finRange _) _ i₀ (List.mem_finRange _) ?_ ?_ ?_)).ap
      (S.i0)
    · simp only [hs]
      exact S.i1 (((S.sd (by om) (by om)).cr (by oi)).ap
        (sAct M T q _))
    · intro i _ h; have := Fin.val_ne_of_ne h; exact S.i0
    · intro i _ _; exact S.i0

theorem dpS (T : Tape Γ) (q : Λ) :
    S (W M) (dp M) 0 (fun j r ↦ sy T j r ∨ j = 0 ∧ r = 2 * (card Γ - 1) + E Λ q) 0
      fun j r ↦ j ≠ 0 ∧ sy T j r ∨ j = 0 ∧ AP M q (T.nth 0) r := by
  have := DB M q (T.nth 0)
  refine S.f1 _ (List.nodup_finRange _) _ (E Λ q) (List.mem_finRange _) ?_ ?_ ?_
  · simp only [Equiv.symm_apply_apply]
    exact S.i1 ((dsS M T q).cl (by oi))
  · intro i _ h; have := Fin.val_ne_of_ne h; exact S.i0
  · intro i _ _; exact S.i0

theorem flS (T : Tape Γ) (q : Λ) :
    S (W M) (fl M) 0 (fun j r ↦ j ≠ 0 ∧ sy T j r ∨ j = 0 ∧ AP M q (T.nth 0) r) 0
      fun j r ↦ S0 M q T j r ∨ j = 0 ∧ RP M q (T.nth 0) r := by
  have := DB M q (T.nth 0)
  unfold fl
  by_cases h0 : (D M q (T.nth 0)).1 = 0
  · exact (S.fN _ _ fun i _ ↦ S.i0).cr (by oi)
  · obtain ⟨i₀, hi⟩ : ∃ i₀ : Fin ((card Γ - 1)), i₀.val + 1 = (D M q (T.nth 0)).1 :=
      ⟨⟨(D M q (T.nth 0)).1 - 1, by omega⟩, by simp only; omega⟩
    refine S.f1 _ (List.nodup_finRange _) _ i₀ (List.mem_finRange _) ?_ ?_ ?_
    · exact S.i1 ((S.si (d := 0) (o := i₀) (by simp) (by om) (by om)).cr (by oi))
    · intro i _ h; have := Fin.val_ne_of_ne h; exact S.i0
    · intro i _ h; have := Fin.val_ne_of_ne h; exact S.i0

theorem caS (T : Tape Γ) (q : Λ) (d : ℤ) (hd : d = 1 ∨ d = -1) (k : ℕ) (hk : k < (card Λ - 1) + 1) :
    S (W M) (cb M d) 0 (fun j r ↦ S0 M q T j r ∨ j = 0 ∧
        (r = 2 * (card Γ - 1) + (card Λ - 1) + 1 + k ∨ r = 2 * (card Γ - 1) + 2 * (card Λ - 1) + 5)) 0
      fun j r ↦ S0 M q T (j + d) r ∨ j = 0 ∧
        (r = 2 * (card Γ - 1) + (card Λ - 1) + 1 + k ∨ r = 2 * (card Γ - 1) + 2 * (card Λ - 1) + 5) := by
  have := DB M q (T.nth 0)
  refine (((S.f1 (Q := fun j r ↦ j = d ∧ r = 2 * (card Γ - 1) + (card Λ - 1) + 1 + k ∨ S0 M q T j r ∨
      j = 0 ∧ r = 2 * (card Γ - 1) + 2 * (card Λ - 1) + 5) _ (List.nodup_finRange _) _ ⟨k, hk⟩
      (List.mem_finRange _) ?_ ?_ ?_).ap (S.i1
        (S.si (d := d) (o := 2 * (card Γ - 1) + 2 * (card Λ - 1) + 5) (by ring) (by om) (by om)))).ap
      (S.bm d)).cr (by oi)
  · exact S.i1 ((S.si (d := d) (o := 2 * (card Γ - 1) + (card Λ - 1) + 1 + k) (by simp; ring)
      (by om) (by om)).cr (by oi))
  · intro i _ h; have := Fin.val_ne_of_ne h; exact S.i0
  · intro i _ h; have := Fin.val_ne_of_ne h; exact S.i0

theorem mvS (T : Tape Γ) (q : Λ) :
    S (W M) (IF (2 * (card Γ - 1) + 2 * (card Λ - 1) + 3) (cb M (-1)) ++ IF (2 * (card Γ - 1) + 2 * (card Λ - 1) + 4) (cb M 1)) 0
      (fun j r ↦ S0 M q T j r ∨ j = 0 ∧ RP M q (T.nth 0) r) 0
      fun j r ↦ NX M q T j r ∨ j = 0 ∧ (D M q (T.nth 0)).2.2.1 = 1 ∧
        (r = 2 * (card Γ - 1) + (card Λ - 1) + 1 + (D M q (T.nth 0)).2.1 ∨ r = 2 * (card Γ - 1) + 2 * (card Λ - 1) + 5) := by
  have := DB M q (T.nth 0)
  by_cases hL : (D M q (T.nth 0)).2.2.2.1 = 1
  · exact ((S.i1 ((caS M T q (-1) (by simp) _ this.2.1).cl (by oi))).ap (S.i0)).cr (by oi)
  · by_cases hR : (D M q (T.nth 0)).2.2.2.2 = 1
    · exact ((S.i0).ap (S.i1 ((caS M T q 1 (by simp) _
        this.2.1).cl (by oi)))).cr (by oi)
    · exact ((S.i0).ap (S.i0)).cr (by oi)

theorem cmS (T : Tape Γ) (q : Λ) :
    S (W M) (cm M) 0 (fun j r ↦ NX M q T j r ∨ j = 0 ∧ (D M q (T.nth 0)).2.2.1 = 1 ∧
        (r = 2 * (card Γ - 1) + (card Λ - 1) + 1 + (D M q (T.nth 0)).2.1 ∨ r = 2 * (card Γ - 1) + 2 * (card Λ - 1) + 5)) 0
      fun j r ↦ NX M q T j r ∨ j = 0 ∧ (D M q (T.nth 0)).2.2.1 = 1 ∧
        (r = 2 * (card Γ - 1) + (D M q (T.nth 0)).2.1 ∨ r = 2 * (card Γ - 1) + 2 * (card Λ - 1) + 5) := by
  have := DB M q (T.nth 0)
  unfold cm
  by_cases hc : (D M q (T.nth 0)).2.2.1 = 1
  · refine S.f1 _ (List.nodup_finRange _) _ ⟨_, this.2.1⟩ (List.mem_finRange _) ?_ ?_ ?_
    · exact S.i1 ((S.si (d := 0) (o := 2 * (card Γ - 1) + (D M q (T.nth 0)).2.1)
        (by simp) (by om) (by om)).cr (by oi))
    · intro i _ h; have := Fin.val_ne_of_ne h; exact S.i0
    · intro i _ _; exact S.i0
  · exact (S.fN _ _ fun i _ ↦ S.i0).cr fun _ _ _ ↦ by simp only [hc, false_and, and_false, or_false]

theorem bdS (T : Tape Γ) (q : Λ) :
    S (W M) (bd M) 0 (fun j r ↦ sy T j r ∨ j = 0 ∧ r = 2 * (card Γ - 1) + E Λ q) 0
      fun j r ↦ NX M q T j r ∨ j = 0 ∧ (D M q (T.nth 0)).2.2.1 = 1 ∧
        (r = 2 * (card Γ - 1) + (D M q (T.nth 0)).2.1 ∨ r = 2 * (card Γ - 1) + 2 * (card Λ - 1) + 5) := by
  rw [bd]; exact (((dpS M T q).ap (flS M T q)).ap (mvS M T q)).ap (cmS M T q)

/-! ## TM steps, the loop, and the claim -/

theorem tmS (q : Λ) (T : Tape Γ) :
    (TM0.step M ⟨q, T⟩ = none ∧ (D M q (T.nth 0)).2.2.1 = 0) ∨
    ∃ c', TM0.step M ⟨q, T⟩ = some c' ∧ (D M q (T.nth 0)).2.2.1 = 1 ∧
      (E Λ c'.q : ℕ) = (D M q (T.nth 0)).2.1 ∧ ∀ j r, sy c'.Tape j r ↔ NX M q T j r := by
  rcases h : M q T.head with _ | ⟨q', d | b⟩
  · left; simp [TM0.step, D, h]
  · right; cases d
    · refine ⟨⟨q', T.move .left⟩, by simp [TM0.step, h], by simp [D, h], by simp [D, h],
        fun j r ↦ ?_⟩
      rcases eq_or_ne j 1 with rfl | h1 <;>
        simp [sy, NX, S0, D, h, Tape.move_left_nth, sub_eq_add_neg] <;> omega
    · refine ⟨⟨q', T.move .right⟩, by simp [TM0.step, h], by simp [D, h], by simp [D, h],
        fun j r ↦ ?_⟩
      rcases eq_or_ne j (-1) with rfl | h1 <;>
        simp [sy, NX, S0, D, h, Tape.move_right_nth] <;> omega
  · right
    refine ⟨⟨q', T.write b⟩, by simp [TM0.step, h], by simp [D, h], by simp [D, h],
      fun j r ↦ ?_⟩
    have hw : (T.write b).head = b := rfl
    rcases eq_or_ne j 0 with rfl | h1 <;> simp [sy, NX, S0, D, h, hw, Tape.write_nth, *]

def LB : Program := .dec :: mv (-↑(Rf M)) ++ bd M ++ mv ↑(Rf M)

def tp (c : TM0.Cfg Γ Λ) (j : ℤ) (r : ℕ) : Prop :=
  sy c.Tape j r ∨ j = 0 ∧ (r = 2 * (card Γ - 1) + E Λ c.q ∨ r = Rf M)

theorem it (q : Λ) (T : Tape Γ) (t : Tape Cell) (ht : H (W M) (Rf M) (tp M ⟨q, T⟩) t) :
    ∃ u, H (W M) (Rf M) (fun j r ↦ NX M q T j r ∨ j = 0 ∧ (D M q (T.nth 0)).2.2.1 = 1 ∧
        (r = 2 * (card Γ - 1) + (D M q (T.nth 0)).2.1 ∨ r = 2 * (card Γ - 1) + 2 * (card Λ - 1) + 5)) u ∧
      Reaches₁ step ⟨.loop (LB M) :: mv (-↑(Rf M)), t⟩ ⟨.loop (LB M) :: mv (-↑(Rf M)), u⟩ := by
  have h1 : tp M ⟨q, T⟩ 0 (Rf M) := Or.inr ⟨rfl, Or.inr rfl⟩
  obtain ⟨u, hu, r⟩ := ((((S.dec (d := 0) (o := Rf M) (by simp) (by simp [W, Rf]) h1).ap
    (S.mo (c := 0) (x := -↑(Rf M)) (by simp))).ap ((bdS M T q).cl (by simp only [tp]; oi))).ap (S.mo (c := ↑(Rf M)) (x := ↑(Rf M)) (by simp))) t ht
  exact ⟨u, hu, .head' (by simp [step, LB, hd ht (d := 0) (o := Rf M) (by simp) (by simp [W, Rf]),
    h1]) (r _)⟩

theorem ex (P : ℤ → ℕ → Prop) (t : Tape Cell) (ht : H (W M) (Rf M) P t) (h0 : ¬P 0 (Rf M)) :
    ∃ u, H (W M) 0 P u ∧ Reaches step ⟨.loop (LB M) :: mv (-↑(Rf M)), t⟩ ⟨[], u⟩ := by
  obtain ⟨u, hu, r⟩ := ((S.l0 (B := LB M) (d := 0) (o := Rf M) (by simp) (by simp [W, Rf]) h0).ap
    (S.mo (c := 0) (x := -↑(Rf M)) (by simp))) t ht
  exact ⟨u, hu, by simpa using r []⟩

def TR (c₁ : TM0.Cfg Γ Λ) (c₂ : Cfg) : Prop :=
  TM0.step M c₁ = none ∧ (∃ t, H (W M) 0 (sy c₁.Tape) t ∧ c₂ = ⟨[], t⟩) ∨
  (TM0.step M c₁).isSome ∧ ∃ t, H (W M) (Rf M) (tp M c₁) t ∧
    c₂ = ⟨.loop (LB M) :: mv (-↑(Rf M)), t⟩

theorem lt (c : TM0.Cfg Γ Λ) (t : Tape Cell) (ht : H (W M) (Rf M) (tp M c) t) :
    ∃ c₂, TR M c c₂ ∧ Reaches step ⟨.loop (LB M) :: mv (-↑(Rf M)), t⟩ c₂ := by
  obtain ⟨q, T⟩ := c
  rcases tmS M q T with ⟨hs, hc⟩ | ⟨c', hs, -⟩
  · have := DB M q (T.nth 0)
    obtain ⟨u, hu, r⟩ := it M q T t ht
    obtain ⟨v, hv, r'⟩ := ex M _ u hu (by om)
    exact ⟨⟨[], v⟩, .inl ⟨hs, v, hv.cq (by oi), rfl⟩, r.to_reflTransGen.trans r'⟩
  · exact ⟨_, .inr ⟨by simp [hs], t, ht, rfl⟩, .refl⟩

theorem rs : Respects (TM0.step M) step (TR M) := by
  rintro ⟨q, T⟩ c₂ h
  rcases tmS M q T with ⟨hs, -⟩ | ⟨c', hs, hc, hq, hT⟩ <;> simp only [hs]
  · rcases h with ⟨-, t, -, rfl⟩ | ⟨h, -⟩
    · rfl
    · simp [hs] at h
  · rcases h with ⟨h, -⟩ | ⟨-, t, ht, rfl⟩
    · simp [hs] at h
    obtain ⟨u, hu, r⟩ := it M q T t ht
    obtain ⟨c₂, h, r'⟩ := lt M c' u (hu.cq fun j r _ ↦ by simp only [tp, hT, hq, hc, Rf, true_and])
    exact ⟨c₂, h, r.trans_left r'⟩

def en (a : Γ) : List Cell := (List.range (W M)).map fun i ↦ if i + 1 = (E Γ a : ℕ) then 1 else 0

theorem fg {α β : Type*} [Inhabited α] [Inhabited β] (f : α → List β) (w : ℕ) (hw : 0 < w)
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

theorem eg (a : Γ) {r : ℕ} (hr : r < W M) :
    (en M a).getI r = if r + 1 = (E Γ a : ℕ) then 1 else 0 := by
  rw [en, List.getI_eq_getElem _ (by simpa using hr)]; simp

theorem ed : en M default = List.replicate (W M) default := by
  simp [en, E0, List.map_const', default]

theorem wp : 0 < W M := by simp [W]

theorem ei : Function.Injective (en M) := by
  intro a b h
  apply (E Γ).injective
  ext
  have := (E Γ a).isLt
  have := (E Γ b).isLt
  have k : (en M a).getI (max (E Γ a : ℕ) (E Γ b) - 1) =
      (en M b).getI (max (E Γ a : ℕ) (E Γ b) - 1) := by rw [h]
  rw [eg _ _ (by simp [W]; omega), eg _ _ (by simp [W]; omega)] at k
  by_contra hne
  split_ifs at k <;> first | omega | simp at k

theorem mn {α} [Inhabited α] (l : List α) (k : ℕ) : (Tape.mk₁ l).nth k = l.getI k := by
  simp [Tape.mk₁, Tape.mk₂, ListBlank.nth_mk]

theorem mg' {α} [Inhabited α] (l : List α) (i : ℤ) (hi : i < 0) : (Tape.mk₁ l).nth i = default := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = Int.negSucc k := ⟨(-i - 1).toNat, by rw [Int.negSucc_eq]; omega⟩
  rfl

theorem ih (l : List Γ) : H (W M) 0 (sy (Tape.mk₁ l)) (Tape.mk₁ (l.flatMap (en M))) := by
  intro j r hr
  rw [sub_zero]
  rcases lt_or_ge j 0 with hj | hj
  · have : (W M : ℤ) * j ≤ -(W M) := by nlinarith
    rw [mg' _ _ (by omega), sy, mg' _ _ hj]
    simp [E0]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    rw [show (W M : ℤ) * k + r = ((W M * k + r : ℕ) : ℤ) by push_cast; ring, mn,
      fg _ _ (wp M) (fun _ ↦ by simp [en]) (ed M), Nat.mul_add_div (wp M), Nat.div_eq_of_lt hr,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hr, eg _ _ hr, sy, mn, add_zero]
    by_cases hc : r + 1 = (E Γ (l.getI k) : ℕ) <;> simp [hc]

theorem r0 (T : Tape Γ) (t : Tape Cell) (h : H (W M) 0 (sy T) t) :
    t.right₀ = T.right₀.flatMap (en M) ⟨W M, ed M⟩ := by
  apply ListBlank.ext
  intro i
  have key : ∀ L : ListBlank Γ, (L.flatMap (en M) ⟨W M, ed M⟩).nth i =
      (en M (L.nth (i / W M))).getI (i % W M) := fun L ↦ L.induction_on fun l ↦ by
    simp only [ListBlank.flatMap_mk, ListBlank.nth_mk]
    exact fg _ _ (wp M) (fun _ ↦ by simp [en]) (ed M) l i
  have hr : i % W M < W M := Nat.mod_lt _ (wp M)
  rw [Tape.right₀_nth, key, Tape.right₀_nth, eg _ _ hr]
  have := h (i / W M : ℕ) (i % W M) hr
  rw [sub_zero, show ((W M : ℤ) * ((i / W M : ℕ) : ℤ) + ((i % W M : ℕ) : ℤ)) = (i : ℤ) by
    exact_mod_cast Nat.div_add_mod i (W M)] at this
  rw [this, sy]
  by_cases hc : i % W M + 1 = (E Γ (T.nth ↑(i / W M)) : ℕ) <;> simp [hc]

theorem ev (l : List Γ) : eval (pg M) (l.flatMap (en M)) =
    (TM0.eval M l).map fun L ↦ L.flatMap (en M) ⟨W M, ed M⟩ := by
  obtain ⟨t1, ht1, hr1⟩ := ((S.si (d := 0) (o := 2 * (card Γ - 1) + E Λ default)
    (x := (2 * (card Γ - 1) + E Λ default : ℕ)) (by simp) (by om) (by om)).ap
    ((S.si (d := 0) (o := Rf M) (x := (Rf M : ℕ)) (by simp) (by om) (by om)).ap
      (S.mo (c := ↑(Rf M)) (x := ↑(Rf M)) (by simp)))) _ (ih M l)
  obtain ⟨c₂, htr, hr⟩ := lt M (TM0.init l) t1 (ht1.cq (by simp only [tp, TM0.init]; oi))
  have h0 : Reaches step (init (pg M) (l.flatMap (en M))) ⟨.loop (LB M) :: mv (-↑(Rf M)), t1⟩ := by
    have := hr1 ([.loop (LB M)] ++ mv (-↑(Rf M)))
    simpa [init, pg, IF, LB, Rf, List.append_assoc] using this
  have e1 := reaches_eval (h0.trans hr)
  unfold eval TM0.eval
  rw [e1]
  ext x
  simp only [Part.map_map, Part.mem_map_iff, Function.comp]
  constructor
  · rintro ⟨b₂, hb₂, rfl⟩
    obtain ⟨c₁, htr', hc₁⟩ := tr_eval_rev (rs M) htr hb₂
    have hs : TM0.step M c₁ = none := (mem_eval.1 hc₁).2
    rcases htr' with ⟨_, t, ht, rfl⟩ | ⟨h, _⟩
    · exact ⟨c₁, hc₁, (r0 M c₁.Tape t ht).symm⟩
    · simp [hs] at h
  · rintro ⟨c₁, hc₁, rfl⟩
    obtain ⟨b₂, htr', hb₂⟩ := tr_eval (rs M) htr hc₁
    have hs : TM0.step M c₁ = none := (mem_eval.1 hc₁).2
    rcases htr' with ⟨_, t, ht, rfl⟩ | ⟨h, _⟩
    · exact ⟨_, hb₂, r0 M c₁.Tape t ht⟩
    · simp [hs] at h

theorem claim : Claim := fun M ↦ ⟨⟨W M, en M, fun _ ↦ by simp [en], ed M, ei M⟩, pg M, ev M⟩

end BF.G
