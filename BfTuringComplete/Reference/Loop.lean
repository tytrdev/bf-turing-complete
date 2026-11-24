import BfTuringComplete.Reference.Sim

/-!
# The main loop, and the simulation theorem for `Fin`-indexed machines

One iteration of the BF main loop is one TM step. We package this as a
`StateTransition.Respects` refinement and let Mathlib's `tr_eval` / `tr_eval_rev`
do the "same result, or both diverge" bookkeeping.
-/

namespace BF

open Turing Layout StateTransition Relation

variable {n m : ℕ} (M : TM0.Machine (Fin (n + 1)) (Fin (m + 1)))

local notation "W" => width n m

/-! ## Encoding lemmas: input and output tapes -/

theorem flatMap_getI {α β : Type*} [Inhabited α] [Inhabited β] (f : α → List β) (w : ℕ)
    (hw : 0 < w) (hlen : ∀ a, (f a).length = w) (hdef : f default = List.replicate w default)
    (l : List α) (i : ℕ) : (l.flatMap f).getI i = (f (l.getI (i / w))).getI (i % w) := by
  induction l generalizing i with
  | nil =>
    rw [List.flatMap_nil, List.getI_nil, List.getI_nil, hdef,
      List.getI_eq_getElem _ (by simpa using Nat.mod_lt _ hw)]
    simp
  | cons a l ih =>
    rw [List.flatMap_cons]
    by_cases hi : i < w
    · rw [List.getI_append _ _ _ (by rw [hlen]; exact hi), Nat.div_eq_of_lt hi,
        Nat.mod_eq_of_lt hi, List.getI_cons_zero]
    · have h1 : i / w = (i - w) / w + 1 := Nat.div_eq_sub_div hw (by omega)
      have h2 : i % w = (i - w) % w := Nat.mod_eq_sub_mod (by omega)
      rw [List.getI_append_right _ _ _ (by rw [hlen]; omega), hlen, ih, h1, h2,
        List.getI_cons_succ]

theorem encSym_length (a : Fin (n + 1)) : (encSym n m a).length = W := by simp [encSym]

theorem encSym_getI (a : Fin (n + 1)) {r : ℕ} (hr : r < W) :
    (encSym n m a).getI r = if r < n ∧ r + 1 = a.val then 1 else 0 := by
  unfold encSym
  rw [List.getI_eq_getElem _ (by simpa using hr)]
  have := a.isLt
  simp only [List.getElem_map, List.getElem_range]
  congr 1
  apply propext
  omega

theorem width_pos : 0 < W := by simp [Layout.width]

theorem mk₁_nth_nat {Γ} [Inhabited Γ] (l : List Γ) (k : ℕ) : (Tape.mk₁ l).nth k = l.getI k := by
  simp [Tape.mk₁, Tape.mk₂, ListBlank.nth_mk]

theorem mk₁_nth_neg {Γ} [Inhabited Γ] (l : List Γ) (i : ℤ) (hi : i < 0) :
    (Tape.mk₁ l).nth i = default := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = Int.negSucc k := ⟨(-i - 1).toNat, by rw [Int.negSucc_eq]; omega⟩
  rfl

theorem init_holds (l : List (Fin (n + 1))) :
    Holds W (toBlk (symAt (Tape.mk₁ l))) (Tape.mk₁ (l.flatMap (encSym n m))) := by
  intro j r hr
  simp only [toBlk]
  rcases lt_or_ge j 0 with hj | hj
  · have hW := width_pos (n := n) (m := m)
    have : (W : ℤ) * j ≤ -W := by nlinarith
    rw [mk₁_nth_neg _ _ (by omega), symAt, mk₁_nth_neg _ _ hj]
    simp
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    rw [show (W : ℤ) * k + r = ((W * k + r : ℕ) : ℤ) by push_cast; ring, mk₁_nth_nat,
      flatMap_getI _ W width_pos (encSym_length (m := m)) (encSym_default n m),
      Nat.mul_add_div width_pos, Nat.div_eq_of_lt hr, Nat.mul_add_mod, Nat.mod_eq_of_lt hr,
      encSym_getI _ hr, symAt, mk₁_nth_nat]
    simp

theorem right0_of_holds (Tp : Tape (Fin (n + 1))) (t : Tape Cell)
    (h : Holds W (toBlk (symAt Tp)) t) :
    t.right₀ = Tp.right₀.flatMap (encSym n m) ⟨W, encSym_default n m⟩ := by
  apply ListBlank.ext
  intro i
  have key : ∀ L : ListBlank (Fin (n + 1)),
      (L.flatMap (encSym n m) ⟨W, encSym_default n m⟩).nth i =
        (encSym n m (L.nth (i / W))).getI (i % W) := fun L ↦ L.induction_on fun l ↦ by
    simp only [ListBlank.flatMap_mk, ListBlank.nth_mk]
    exact flatMap_getI _ W width_pos (encSym_length (m := m)) (encSym_default n m) l i
  have hr : i % W < W := Nat.mod_lt _ width_pos
  rw [Tape.right₀_nth, key, Tape.right₀_nth, encSym_getI _ hr]
  have := h (i / W : ℕ) (i % W) hr
  rw [show ((W : ℤ) * ((i / W : ℕ) : ℤ) + ((i % W : ℕ) : ℤ)) = (i : ℤ) by
    exact_mod_cast Nat.div_add_mod i W] at this
  rw [this]
  classical
  exact if_congr Iff.rfl rfl rfl

/-! ## The main loop -/

/-- Body of the main BF loop (the `ifAt R stepBody` loop, unfolded). -/
def loopBody : Program := [.dec] ++ mv (-(R n m : ℤ)) ++ stepBody n m M ++ mv (R n m : ℤ)

/-- BF config at the top of the main loop; `t` is the tape viewed from home. -/
def top (t : Tape Cell) : Cfg := ⟨.loop (loopBody M) :: mv (-(R n m : ℤ)), moveBy (R n m) t⟩

/-- Head block at the top of the loop: symbol, state flag, running flag. -/
def topP (c : TM0.Cfg (Fin (n + 1)) (Fin (m + 1))) : ℤ → ℕ → Prop :=
  fun j r ↦ symAt c.Tape j r ∨ (j = 0 ∧ (r = st n c.q.val ∨ r = R n m))

theorem iterate (q : Fin (m + 1)) (Tp : Tape (Fin (n + 1))) (t : Tape Cell)
    (ht : Holds W (toBlk (topP ⟨q, Tp⟩)) t) :
    ∃ t', Holds W (toBlk fun j r ↦ symAt (nextTape M Tp q) j r ∨
        (j = 0 ∧ cont M q (Tp.nth 0) = 1 ∧ (r = st n (nst M q (Tp.nth 0)) ∨ r = R n m))) t' ∧
      Reaches₁ step (top M t) (top M t') := by
  have hR : R n m < W := by bf_omega
  have h1 : topP (n := n) (m := m) ⟨q, Tp⟩ 0 (R n m) := Or.inr ⟨rfl, Or.inr rfl⟩
  obtain ⟨t', ht', hr⟩ := spec_stepBody M Tp q _
    (holds_dec ht hR h1 (by simp only [topP]; bf_iff))
  refine ⟨t', ht', ?_⟩
  have hh : (moveBy (R n m) t).head ≠ 0 := by
    rw [show (moveBy (R n m) t).head = t.nth (R n m) by simpa using moveBy_nth (R n m) t 0,
      ht.nth0 hR]
    simp [h1]
  refine TransGen.head' (b := ⟨loopBody M ++ .loop (loopBody M) :: mv (-(R n m : ℤ)),
    moveBy (R n m) t⟩) (by simp [top, step, hh]) ?_
  have hL : Runs (loopBody M) (moveBy (R n m) t) (moveBy (R n m) t') :=
    (((Runs.dec _).append (runs_mv _ _)).append hr).append (runs_mv _ _)
  exact hL _

theorem exit_loop (t : Tape Cell) (P : ℤ → ℕ → Prop) (ht : Holds W (toBlk P) t)
    (h0 : ¬P 0 (R n m)) : Reaches step (top M t) ⟨[], t⟩ := by
  have hR : R n m < W := by bf_omega
  have hh : (moveBy (R n m) t).head = 0 := by
    rw [show (moveBy (R n m) t).head = t.nth (R n m) by simpa using moveBy_nth (R n m) t 0,
      ht.nth0 hR]
    simp [h0]
  have := ((Runs.loop_zero (b := loopBody M) hh).append (runs_mv (-(R n m : ℤ)) _)) []
  simpa [top] using this

/-- The refinement relation between TM0 configs and BF configs. -/
def TrRel (c₁ : TM0.Cfg (Fin (n + 1)) (Fin (m + 1))) (c₂ : Cfg) : Prop :=
  (TM0.step M c₁ = none ∧ ∃ t, Holds W (toBlk (symAt c₁.Tape)) t ∧ c₂ = ⟨[], t⟩) ∨
    ((TM0.step M c₁).isSome ∧ ∃ t, Holds W (toBlk (topP c₁)) t ∧ c₂ = top M t)

theorem loop_tr (c : TM0.Cfg (Fin (n + 1)) (Fin (m + 1))) (t : Tape Cell)
    (ht : Holds W (toBlk (topP c)) t) : ∃ c₂, TrRel M c c₂ ∧ Reaches step (top M t) c₂ := by
  obtain ⟨q, Tp⟩ := c
  rcases tm_step_cases M q Tp with ⟨hs, hc⟩ | ⟨c', hs, hc, -, -⟩
  · obtain ⟨t', ht', hr⟩ := iterate M q Tp t ht
    rw [nextTape_halt M q Tp hc] at ht'
    have ht'' : Holds W (toBlk (symAt Tp)) t' := ht'.congr (by intro j r _; simp only [hc]; simp)
    exact ⟨⟨[], t'⟩, Or.inl ⟨hs, t', ht'', rfl⟩,
      hr.to_reflTransGen.trans (exit_loop M t' _ ht'' (by bf_omega))⟩
  · exact ⟨top M t, Or.inr ⟨by simp [hs], t, ht, rfl⟩, ReflTransGen.refl⟩

theorem respects : Respects (TM0.step M) step (TrRel M) := by
  intro c₁ c₂ hrel
  obtain ⟨q, Tp⟩ := c₁
  rcases tm_step_cases M q Tp with ⟨hs, hc⟩ | ⟨c', hs, hc, hq, hT⟩
  · simp only [hs]
    rcases hrel with ⟨_, t, _, rfl⟩ | ⟨hsome, _⟩
    · rfl
    · simp [hs] at hsome
  · simp only [hs]
    rcases hrel with ⟨hnone, _⟩ | ⟨_, t, ht, rfl⟩
    · simp [hs] at hnone
    obtain ⟨t', ht', hr⟩ := iterate M q Tp t ht
    have ht'' : Holds W (toBlk (topP c')) t' :=
      ht'.congr (by intro j r _; simp only [topP, hT, hq, hc, true_and])
    obtain ⟨c₂, htr, hr2⟩ := loop_tr M c' t' ht''
    exact ⟨c₂, htr, hr.trans_left hr2⟩

/-! ## The simulation theorem for `Fin` machines -/

theorem compile_eval (l : List (Fin (n + 1))) :
    eval (compile n m M) (l.flatMap (encSym n m)) =
      (TM0.eval M l).map fun L ↦ L.flatMap (encSym n m) ⟨W, encSym_default n m⟩ := by
  have h0 := init_holds (m := m) l
  have hI : Spec W (incAt (st n 0) ++ incAt (R n m))
      (fun j r ↦ symAt (Tape.mk₁ l) j r ∨ (j = 0 ∧ False))
      (fun j r ↦ symAt (Tape.mk₁ l) j r ∨ (j = 0 ∧ (r = R n m ∨ (r = st n 0 ∨ False)))) :=
    (spec_inc_s (by bf_omega) (by bf_omega) (by simp)).append
      (spec_inc_s (by bf_omega) (by bf_omega) (by bf_omega))
  obtain ⟨t1, ht1, hr1⟩ := hI _ (h0.congr (by simp))
  have ht1' : Holds W (toBlk (topP (TM0.init l))) t1 :=
    ht1.congr (by intro j r _; simp only [topP, TM0.init]; simp; tauto)
  have hreach0 : Reaches step (init (compile n m M) (l.flatMap (encSym n m))) (top M t1) := by
    have := (hr1.append (runs_mv (R n m : ℤ) t1)) (.loop (loopBody M) :: mv (-(R n m : ℤ)))
    simpa [init, compile, ifAt, top, loopBody, List.append_assoc] using this
  obtain ⟨c₂, htr, hreach⟩ := loop_tr M (TM0.init l) t1 ht1'
  have e1 : StateTransition.eval step (init (compile n m M) (l.flatMap (encSym n m))) =
      StateTransition.eval step c₂ := reaches_eval (hreach0.trans hreach)
  unfold eval TM0.eval
  rw [e1]
  ext x
  simp only [Part.map_map, Part.mem_map_iff, Function.comp]
  constructor
  · rintro ⟨b₂, hb₂, rfl⟩
    obtain ⟨c₁, htr', hc₁⟩ := tr_eval_rev (respects M) htr hb₂
    refine ⟨c₁, hc₁, ?_⟩
    have hs : TM0.step M c₁ = none := (mem_eval.1 hc₁).2
    rcases htr' with ⟨_, t, ht, rfl⟩ | ⟨hsome, _⟩
    · exact (right0_of_holds c₁.Tape t ht).symm
    · simp [hs] at hsome
  · rintro ⟨c₁, hc₁, rfl⟩
    obtain ⟨b₂, htr', hb₂⟩ := tr_eval (respects M) htr hc₁
    have hs : TM0.step M c₁ = none := (mem_eval.1 hc₁).2
    rcases htr' with ⟨_, t, ht, rfl⟩ | ⟨hsome, _⟩
    · exact ⟨_, hb₂, right0_of_holds c₁.Tape t ht⟩
    · simp [hs] at hsome

end BF
