import BfTuringComplete.Spec

/-!
# Correctness of the compiled step

All block contents are flag predicates built from
* `symAt Tp j r`: the one-hot symbol flags of TM tape `Tp`, and
* arithmetic conditions on `j`, `r` and a few numbers describing the transition
  (`newSym`, `nst`, `cont`, `mvL`, `mvR`),
so every side condition is linear arithmetic, closed by `bf_omega`.
-/

namespace BF

open Turing Layout

variable {n m : ℕ} (M : TM0.Machine (Fin (n + 1)) (Fin (m + 1)))

/-- One-hot symbol flags of a TM tape: offset `r` of block `j` is set iff cell `j` holds `r + 1`. -/
def symAt (Tp : Tape (Fin (n + 1))) (j : ℤ) (r : ℕ) : Prop := r < n ∧ r + 1 = (Tp.nth j).val

/-! ## A transition, as numbers -/

def newSym (q : Fin (m + 1)) (a : Fin (n + 1)) : Fin (n + 1) :=
  match M q a with
  | some (_, .write b) => b
  | _ => a

def nst (q : Fin (m + 1)) (a : Fin (n + 1)) : ℕ :=
  match M q a with
  | some (q', _) => q'.val
  | none => 0

def cont (q : Fin (m + 1)) (a : Fin (n + 1)) : ℕ :=
  match M q a with
  | some _ => 1
  | none => 0

def mvL (q : Fin (m + 1)) (a : Fin (n + 1)) : ℕ :=
  match M q a with
  | some (_, .move .left) => 1
  | _ => 0

def mvR (q : Fin (m + 1)) (a : Fin (n + 1)) : ℕ :=
  match M q a with
  | some (_, .move .right) => 1
  | _ => 0

theorem ctl_bounds (q : Fin (m + 1)) (a : Fin (n + 1)) :
    nst M q a < m + 1 ∧ cont M q a ≤ 1 ∧ mvL M q a + mvR M q a ≤ cont M q a ∧
      (cont M q a = 0 → newSym M q a = a) ∧
      (mvL M q a + mvR M q a = 1 → newSym M q a = a) := by
  unfold nst cont mvL mvR newSym
  rcases h : M q a with _ | ⟨q', s⟩
  · simp
  · cases s with
    | move d => cases d <;> simp [q'.isLt]
    | write b => simp [q'.isLt]

/-- Pending flags `act` leaves in the head block, besides the pending symbol. -/
def restP (q : Fin (m + 1)) (a : Fin (n + 1)) (r : ℕ) : Prop :=
  (mvL M q a = 1 ∧ r = ML n m) ∨ (mvR M q a = 1 ∧ r = MR n m) ∨
    (cont M q a = 1 ∧ r = pend n m (nst M q a)) ∨ (cont M q a = 1 ∧ r = R n m)

/-- All pending flags `act` sets. -/
def actP (q : Fin (m + 1)) (a : Fin (n + 1)) (r : ℕ) : Prop :=
  ((newSym M q a).val ≠ 0 ∧ r = xsym n (newSym M q a).val) ∨ restP M q a r

/-- Unfold layout and flag definitions, then `omega`. -/
macro "bf_omega" : tactic => `(tactic|
  (simp (config := { failIfUnchanged := false }) only [symAt, actP, restP, Layout.sym,
    Layout.xsym, Layout.st, Layout.pend, Layout.T, Layout.ML, Layout.MR, Layout.R,
    Layout.width, ne_eq, false_and, and_false, false_or, or_false, iff_def, false_implies,
    imp_false, true_and, and_true, not_true_eq_false, not_false_eq_true, true_or, or_true,
    true_implies, implies_true, and_self, or_self, eq_self_iff_true] at * <;> omega))

/-- Side goal `∀ j r, r < w → (_ ↔ _)`: split on the head block, then `bf_omega`. -/
macro "bf_iff" : tactic => `(tactic|
  (intro j r hr; by_cases hj : j = 0 <;> (try subst hj) <;> bf_omega))

local notation "W" => width n m

/-! ## `act` -/

theorem spec_act (Tp : Tape (Fin (n + 1))) (q : Fin (m + 1)) (a : Fin (n + 1)) :
    Spec W (act n m M q a) (fun j r ↦ j ≠ 0 ∧ symAt Tp j r)
      (fun j r ↦ (j ≠ 0 ∧ symAt Tp j r) ∨ (j = 0 ∧ actP M q a r)) := by
  have hb := ctl_bounds M q a
  have ha := a.isLt
  suffices H : Spec W (act n m M q a) (fun j r ↦ (j ≠ 0 ∧ symAt Tp j r) ∨ (j = 0 ∧ False))
      (fun j r ↦ (j ≠ 0 ∧ symAt Tp j r) ∨ (j = 0 ∧ actP M q a r)) from
    H.pre (by intro j r _; simp)
  have h0 : ∀ o, ¬((0 : ℤ) ≠ 0 ∧ symAt Tp 0 o) := by simp
  unfold act setSym
  rcases h : M q a with _ | ⟨q', s⟩
  · simp only [actP, restP, newSym, nst, cont, mvL, mvR, h] at hb ⊢
    split_ifs with hz
    · exact Spec.nil.conseq_s (by intro r _; bf_omega)
    · exact (spec_inc_s (by bf_omega) (h0 _) (by simp)).conseq_s (by intro r _; bf_omega)
  · have hq := q'.isLt
    cases s with
    | move d =>
      cases d <;> simp only [actP, restP, newSym, nst, cont, mvL, mvR, h] at hb ⊢ <;>
        split_ifs with hz
      · exact (((Spec.nil.append (spec_inc_s (by bf_omega) (h0 _) (by simp))).append
          (spec_inc_s (by bf_omega) (h0 _) (by bf_omega))).append
          (spec_inc_s (by bf_omega) (h0 _) (by bf_omega))).conseq_s (by intro r _; bf_omega)
      · exact ((((spec_inc_s (by bf_omega) (h0 _) (by simp))).append
          (spec_inc_s (by bf_omega) (h0 _) (by bf_omega))).append
          (spec_inc_s (by bf_omega) (h0 _) (by bf_omega))).append
          (spec_inc_s (by bf_omega) (h0 _) (by bf_omega)) |>.conseq_s (by intro r _; bf_omega)
      · exact (((Spec.nil.append (spec_inc_s (by bf_omega) (h0 _) (by simp))).append
          (spec_inc_s (by bf_omega) (h0 _) (by bf_omega))).append
          (spec_inc_s (by bf_omega) (h0 _) (by bf_omega))).conseq_s (by intro r _; bf_omega)
      · exact ((((spec_inc_s (by bf_omega) (h0 _) (by simp))).append
          (spec_inc_s (by bf_omega) (h0 _) (by bf_omega))).append
          (spec_inc_s (by bf_omega) (h0 _) (by bf_omega))).append
          (spec_inc_s (by bf_omega) (h0 _) (by bf_omega)) |>.conseq_s (by intro r _; bf_omega)
    | write b =>
      have := b.isLt
      simp only [actP, restP, newSym, nst, cont, mvL, mvR, h] at hb ⊢
      split_ifs with hz
      · exact ((Spec.nil.append (spec_inc_s (by bf_omega) (h0 _) (by simp))).append
          (spec_inc_s (by bf_omega) (h0 _) (by bf_omega))).conseq_s (by intro r _; bf_omega)
      · exact (((spec_inc_s (by bf_omega) (h0 _) (by simp)).append
          (spec_inc_s (by bf_omega) (h0 _) (by bf_omega))).append
          (spec_inc_s (by bf_omega) (h0 _) (by bf_omega))).conseq_s (by intro r _; bf_omega)

/-! ## Dispatch -/

theorem spec_dispatchSym (Tp : Tape (Fin (n + 1))) (q : Fin (m + 1)) :
    Spec W (dispatchSym n m M q) (fun j r ↦ symAt Tp j r ∨ (j = 0 ∧ False))
      (fun j r ↦ (j ≠ 0 ∧ symAt Tp j r) ∨ (j = 0 ∧ actP M q (Tp.nth 0) r)) := by
  have hb := ctl_bounds M q (Tp.nth 0)
  have I1 := spec_inc_s (w := W) (Base := symAt Tp) (s := fun _ ↦ False) (o := Layout.T n m)
    (by bf_omega) (by bf_omega) (by simp)
  unfold dispatchSym
  by_cases ha : (Tp.nth 0).val = 0
  · have e0 : Tp.nth 0 = 0 := Fin.ext ha
    refine (I1.append (spec_flatMap_noop _ _ fun i _ ↦
      spec_ifAt_clear (by bf_omega) (by bf_omega) _)).append ?_
    rw [e0] at hb ⊢
    exact spec_ifAt_set (by bf_omega) (fun j r ↦ j ≠ 0 ∧ symAt Tp j r) (Or.inr ⟨rfl, Or.inl rfl⟩)
      (by bf_iff) (spec_act M Tp q 0) (by bf_omega)
  · obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin n, i₀.val + 1 = (Tp.nth 0).val :=
      ⟨⟨(Tp.nth 0).val - 1, by have := (Tp.nth 0).isLt; omega⟩, by simp only [Fin.val_mk]; omega⟩
    have hsucc : i₀.succ = Tp.nth 0 := Fin.ext (by simp only [Fin.val_succ]; omega)
    refine (I1.append (spec_flatMap_single _ (List.nodup_finRange n) _ i₀ (List.mem_finRange _)
      ?_ ?_ ?_)).append (spec_ifAt_clear (by bf_omega) (by bf_omega) _)
    · show Spec W (ifAt (sym (i₀.val + 1)) (decAt (Layout.T n m) ++ act n m M q i₀.succ)) _ _
      rw [hsucc]
      exact spec_ifAt_set (by bf_omega)
        (fun j r ↦ (j ≠ 0 ∧ symAt Tp j r) ∨ (j = 0 ∧ (r = Layout.T n m ∨ False)))
        (Or.inl (by bf_omega)) (by bf_iff)
        ((spec_decAt (Q := fun j r ↦ j ≠ 0 ∧ symAt Tp j r) (by bf_omega) (Or.inr ⟨rfl, Or.inl rfl⟩)
          (by bf_iff)).append (spec_act M Tp q _)) (by bf_omega)
    · intro i _ hi
      have := Fin.val_ne_of_ne hi
      exact spec_ifAt_clear (by bf_omega) (by bf_omega) _
    · intro i _ hi
      exact spec_ifAt_clear (by bf_omega) (by bf_omega) _

theorem spec_dispatch (Tp : Tape (Fin (n + 1))) (q : Fin (m + 1)) :
    Spec W (dispatch n m M) (fun j r ↦ symAt Tp j r ∨ (j = 0 ∧ r = st n q))
      (fun j r ↦ (j ≠ 0 ∧ symAt Tp j r) ∨ (j = 0 ∧ actP M q (Tp.nth 0) r)) := by
  have hb := ctl_bounds M q (Tp.nth 0)
  refine spec_flatMap_single _ (List.nodup_finRange _) _ q (List.mem_finRange _) ?_ ?_ ?_
  · exact spec_ifAt_set (by bf_omega) (fun j r ↦ symAt Tp j r ∨ (j = 0 ∧ False))
      (Or.inr ⟨rfl, rfl⟩) (by bf_iff) (spec_dispatchSym M Tp q) (by bf_omega)
  · intro q' _ hq
    have := Fin.val_ne_of_ne hq
    exact spec_ifAt_clear (by bf_omega) (by bf_omega) _
  · intro q' _ hq
    exact spec_ifAt_clear (by bf_omega) (by bf_omega) _

/-! ## Flush: pending symbol becomes the real symbol -/

set_option maxHeartbeats 2000000 in
theorem spec_flush (Tp : Tape (Fin (n + 1))) (q : Fin (m + 1)) :
    Spec W (flush n) (fun j r ↦ (j ≠ 0 ∧ symAt Tp j r) ∨ (j = 0 ∧ actP M q (Tp.nth 0) r))
      (fun j r ↦ ((j ≠ 0 ∧ symAt Tp j r) ∨
          (j = 0 ∧ r < n ∧ r + 1 = (newSym M q (Tp.nth 0)).val)) ∨
        (j = 0 ∧ restP M q (Tp.nth 0) r)) := by
  have hb := ctl_bounds M q (Tp.nth 0)
  have hB := (newSym M q (Tp.nth 0)).isLt
  unfold flush
  by_cases hb0 : (newSym M q (Tp.nth 0)).val = 0
  · exact (spec_flatMap_noop _ _ fun i _ ↦
      spec_ifAt_clear (by bf_omega) (by bf_omega) _).conseq (by bf_iff)
  · obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin n, i₀.val + 1 = (newSym M q (Tp.nth 0)).val :=
      ⟨⟨(newSym M q (Tp.nth 0)).val - 1, by omega⟩, by simp only [Fin.val_mk]; omega⟩
    refine spec_flatMap_single _ (List.nodup_finRange n) _ i₀ (List.mem_finRange _) ?_ ?_ ?_
    · exact spec_ifAt_set (by bf_omega)
        (fun j r ↦ (j ≠ 0 ∧ symAt Tp j r) ∨ (j = 0 ∧ restP M q (Tp.nth 0) r))
        (Or.inr ⟨rfl, by bf_omega⟩) (by bf_iff)
        (spec_incAt0 (by bf_omega) (by bf_omega) (by bf_iff)) (by bf_omega)
    · intro i _ hi
      have := Fin.val_ne_of_ne hi
      exact spec_ifAt_clear (by bf_omega) (by bf_omega) _
    · intro i _ hi
      exact spec_ifAt_clear (by bf_omega) (by bf_omega) _

/-! ## Moving: carry pending state and `R` into the neighbouring block -/

theorem symAt_write (Tp : Tape (Fin (n + 1))) (b : Fin (n + 1)) (j : ℤ) (r : ℕ) :
    symAt (Tp.write b) j r ↔ (j ≠ 0 ∧ symAt Tp j r) ∨ (j = 0 ∧ r < n ∧ r + 1 = b.val) := by
  unfold symAt
  rw [Tape.write_nth]
  by_cases hj : j = 0 <;> simp [hj]

theorem symAt_moveL (U : Tape (Fin (n + 1))) (j : ℤ) (r : ℕ) :
    symAt (U.move .left) j r ↔ symAt U (j + -1) r := by
  simp [symAt, Tape.move_left_nth, sub_eq_add_neg]

theorem symAt_moveR (U : Tape (Fin (n + 1))) (j : ℤ) (r : ℕ) :
    symAt (U.move .right) j r ↔ symAt U (j + 1) r := by
  simp [symAt, Tape.move_right_nth]

theorem incAt_neg (o : ℕ) : incAt ((o : ℤ) + -(W : ℤ)) = incAt (W * (-1) + o) := by
  congr 1; ring

theorem incAt_pos (o : ℕ) : incAt ((o : ℤ) + (W : ℤ)) = incAt (W * 1 + o) := by
  congr 1; ring

theorem mv_neg : mv (-(W : ℤ)) = mv (W * (-1)) := by congr 1; ring

theorem mv_pos : mv (W : ℤ) = mv (W * 1) := by congr 1; ring

/-- Shared body of both move gadgets, moving by `d = ±1` blocks. -/
theorem spec_carry (U : Tape (Fin (n + 1))) (k : Fin (m + 1)) (d : ℤ) (hd : d = 1 ∨ d = -1) :
    Spec W (((List.finRange (m + 1)).flatMap fun q ↦
        ifAt (pend n m q.val) (incAt ((pend n m q.val : ℤ) + d * W)))
      ++ ifAt (R n m) (incAt ((R n m : ℤ) + d * W)) ++ mv (d * W))
      (fun j r ↦ symAt U j r ∨ (j = 0 ∧ (r = pend n m k ∨ r = R n m)))
      (fun j r ↦ symAt U (j + d) r ∨ (j = 0 ∧ (r = pend n m k ∨ r = R n m))) := by
  have hk := k.isLt
  have e1 : ∀ o : ℕ, incAt ((o : ℤ) + d * W) = incAt (W * d + o) := fun o ↦ by congr 1; ring
  have e2 : mv (d * W) = mv (W * d) := by congr 1; ring
  simp only [e1, e2]
  refine ((spec_flatMap_single (Q := fun j r ↦ (j = d ∧ r = pend n m k) ∨
      (symAt U j r ∨ (j = 0 ∧ r = R n m))) _ (List.nodup_finRange _) _ k (List.mem_finRange _)
      ?_ ?_ ?_).append
    (spec_ifAt_set (by bf_omega) (fun j r ↦ (j = d ∧ r = pend n m k) ∨ symAt U j r)
      (by bf_omega) (by bf_iff) (spec_incAt d (by bf_omega) (by bf_omega) (fun _ _ _ ↦ Iff.rfl))
      (by rcases hd with rfl | rfl <;> bf_omega))).append
    (spec_mv (Q := fun j r ↦ symAt U (j + d) r ∨ (j = 0 ∧ (r = pend n m k ∨ r = R n m))) d ?_)
  · exact spec_ifAt_set (by bf_omega) (fun j r ↦ symAt U j r ∨ (j = 0 ∧ r = R n m))
      (by bf_omega) (by bf_iff) (spec_incAt d (by bf_omega) (by rcases hd with rfl | rfl <;> bf_omega)
        (fun _ _ _ ↦ Iff.rfl)) (by rcases hd with rfl | rfl <;> bf_omega)
  · intro q' _ hq
    have := Fin.val_ne_of_ne hq
    exact spec_ifAt_clear (by bf_omega) (by bf_omega) _
  · intro q' _ hq
    have := Fin.val_ne_of_ne hq
    exact spec_ifAt_clear (by bf_omega) (by rcases hd with rfl | rfl <;> bf_omega) _
  · intro j r hr
    rcases hd with rfl | rfl <;> by_cases hj : j = 0 <;> (try subst hj) <;> bf_omega

/-- The tape after one TM step (write, then move). -/
def nextTape (Tp : Tape (Fin (n + 1))) (q : Fin (m + 1)) : Tape (Fin (n + 1)) :=
  let U := Tp.write (newSym M q (Tp.nth 0))
  if mvL M q (Tp.nth 0) = 1 then U.move .left
  else if mvR M q (Tp.nth 0) = 1 then U.move .right else U

theorem spec_moves (Tp : Tape (Fin (n + 1))) (q : Fin (m + 1)) :
    Spec W (moveGadget n m (ML n m) (-(W : ℤ)) ++ moveGadget n m (MR n m) W)
      (fun j r ↦ symAt (Tp.write (newSym M q (Tp.nth 0))) j r ∨ (j = 0 ∧ restP M q (Tp.nth 0) r))
      (fun j r ↦ symAt (nextTape M Tp q) j r ∨
        (j = 0 ∧ cont M q (Tp.nth 0) = 1 ∧
          (r = pend n m (nst M q (Tp.nth 0)) ∨ r = R n m))) := by
  have hb := ctl_bounds M q (Tp.nth 0)
  set U := Tp.write (newSym M q (Tp.nth 0))
  let k : Fin (m + 1) := ⟨nst M q (Tp.nth 0), hb.1⟩
  have hk : (k : ℕ) = nst M q (Tp.nth 0) := rfl
  unfold moveGadget
  by_cases hL : mvL M q (Tp.nth 0) = 1
  · have hnt : nextTape M Tp q = U.move .left := by simp only [nextTape, U, hL, ↓reduceIte]
    rw [hnt]
    refine (spec_ifAt_set (Q := fun j r ↦ symAt U (j + -1) r ∨
        (j = 0 ∧ (r = pend n m k ∨ r = R n m))) (by bf_omega)
      (fun j r ↦ symAt U j r ∨ (j = 0 ∧ (r = pend n m k ∨ r = R n m)))
      (by bf_omega) (by bf_iff) ?_ (by bf_omega)).append (spec_ifAt_clear (by bf_omega)
        (by bf_omega) _) |>.conseq ?_
    · have := spec_carry U k (-1) (Or.inr rfl)
      simp only [neg_one_mul] at this
      exact this
    · intro j r _
      rw [symAt_moveL]
      bf_omega
  · by_cases hR : mvR M q (Tp.nth 0) = 1
    · have hnt : nextTape M Tp q = U.move .right := by
        simp only [nextTape, U, hL, hR, ↓reduceIte]
      rw [hnt]
      refine (spec_ifAt_clear (by bf_omega) (by bf_omega) _).append (spec_ifAt_set
        (Q := fun j r ↦ symAt U (j + 1) r ∨ (j = 0 ∧ (r = pend n m k ∨ r = R n m))) (by bf_omega)
        (fun j r ↦ symAt U j r ∨ (j = 0 ∧ (r = pend n m k ∨ r = R n m)))
        (by bf_omega) (by bf_iff) ?_ (by bf_omega)) |>.conseq ?_
      · have := spec_carry U k 1 (Or.inl rfl)
        simp only [one_mul] at this
        exact this
      · intro j r _
        rw [symAt_moveR]
        bf_omega
    · have hnt : nextTape M Tp q = U := by simp only [nextTape, U, hL, hR, ↓reduceIte]
      rw [hnt]
      exact ((spec_ifAt_clear (by bf_omega) (by bf_omega) _).append
        (spec_ifAt_clear (by bf_omega) (by bf_omega) _)).conseq (by bf_iff)

/-! ## Commit: pending state becomes the real state -/

theorem spec_commit (V : Tape (Fin (n + 1))) (c k : ℕ) (hk : k < m + 1) (hc : c ≤ 1) :
    Spec W (commit n m)
      (fun j r ↦ symAt V j r ∨ (j = 0 ∧ c = 1 ∧ (r = pend n m k ∨ r = R n m)))
      (fun j r ↦ symAt V j r ∨ (j = 0 ∧ c = 1 ∧ (r = st n k ∨ r = R n m))) := by
  unfold commit
  by_cases h1 : c = 1
  · refine spec_flatMap_single _ (List.nodup_finRange _) _ ⟨k, hk⟩ (List.mem_finRange _) ?_ ?_ ?_
    · exact spec_ifAt_set (by bf_omega) (fun j r ↦ symAt V j r ∨ (j = 0 ∧ r = R n m))
        (by bf_omega) (by bf_iff) (spec_incAt0 (by bf_omega) (by bf_omega) (by bf_iff))
        (by bf_omega)
    · intro q' _ hq
      have := Fin.val_ne_of_ne hq
      exact spec_ifAt_clear (by bf_omega) (by simp at this; bf_omega) _
    · intro q' _ hq
      exact spec_ifAt_clear (by bf_omega) (by bf_omega) _
  · exact (spec_flatMap_noop _ _ fun q _ ↦
      spec_ifAt_clear (by bf_omega) (by bf_omega) _).conseq (by bf_iff)

/-! ## One whole step -/

theorem spec_stepBody (Tp : Tape (Fin (n + 1))) (q : Fin (m + 1)) :
    Spec W (stepBody n m M) (fun j r ↦ symAt Tp j r ∨ (j = 0 ∧ r = st n q))
      (fun j r ↦ symAt (nextTape M Tp q) j r ∨
        (j = 0 ∧ cont M q (Tp.nth 0) = 1 ∧ (r = st n (nst M q (Tp.nth 0)) ∨ r = R n m))) := by
  have hb := ctl_bounds M q (Tp.nth 0)
  have e : stepBody n m M = dispatch n m M ++ flush n ++
      (moveGadget n m (ML n m) (-(W : ℤ)) ++ moveGadget n m (MR n m) W) ++ commit n m := by
    simp [stepBody, List.append_assoc]
  rw [e]
  exact ((((spec_dispatch M Tp q).append (spec_flush M Tp q)).conseq
    (fun j r _ ↦ by rw [symAt_write])).append (spec_moves M Tp q)).append
    (spec_commit _ _ _ hb.1 hb.2.1)

/-- `TM0.step` in terms of our transition numbers. -/
theorem tm_step_cases (q : Fin (m + 1)) (Tp : Tape (Fin (n + 1))) :
    (TM0.step M ⟨q, Tp⟩ = none ∧ cont M q (Tp.nth 0) = 0) ∨
    (∃ c', TM0.step M ⟨q, Tp⟩ = some c' ∧ cont M q (Tp.nth 0) = 1 ∧
      c'.q.val = nst M q (Tp.nth 0) ∧ c'.Tape = nextTape M Tp q) := by
  rcases h : M q Tp.head with _ | ⟨q', s⟩
  · left; simp [nextTape, cont, nst, newSym, mvL, mvR, Tape.nth_zero, TM0.step, h]
  · right
    cases s with
    | move d => cases d <;> simp [nextTape, cont, nst, newSym, mvL, mvR, Tape.nth_zero, TM0.step, h]
    | write b => simp [nextTape, cont, nst, newSym, mvL, mvR, Tape.nth_zero, TM0.step, h]

theorem nextTape_halt (q : Fin (m + 1)) (Tp : Tape (Fin (n + 1)))
    (h : cont M q (Tp.nth 0) = 0) : nextTape M Tp q = Tp := by
  have hb := ctl_bounds M q (Tp.nth 0)
  have hL : mvL M q (Tp.nth 0) = 0 := by omega
  have hR : mvR M q (Tp.nth 0) = 0 := by omega
  simp only [nextTape, hL, hR, hb.2.2.2.1 h, ↓reduceIte, zero_ne_one]
  exact Tape.write_self Tp

end BF
