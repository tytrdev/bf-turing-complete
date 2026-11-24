import BfTuringComplete.Elegant.Machine

/-!
# Brainfuck simulates every TM0 machine

The program raises `state default` and `run`, then loops on `run`: each pass clears `run` and
performs one TM step (`step_den`), which raises `run` again unless the machine halted. The final
tape holds exactly the TM's final tape in the block code `enc`.
-/

noncomputable section
namespace BF.Elegant
open Turing StateTransition Relation Classical Fintype FProg

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Fintype Γ] [Fintype Λ] (M : TM0.Machine Γ Λ)

local notation "Fl" => Flag Γ Λ

/-- The main loop: while `run` is raised, perform a step. -/
def mainLoop : Stmt := loopCode (Flag.run : Fl) (stepProg M)

/-- The Brainfuck program simulating `M`. -/
def program : Program :=
  (FProg.set (Flag.state default : Fl) ⨾ .set .run).compile ++ atFlag (Flag.run : Fl) [mainLoop M]

/-- A running configuration: in the main loop, with `run` raised. -/
def Running (c : TM0.Cfg Γ Λ) (t : Tape Cell) : Prop :=
  Holds (pos (Flag.run : Fl)) (cfgSet c ∪ here [.run]) t

/-- How BF configurations track TM configurations: in the main loop while the machine runs,
and finished with the encoded tape once it halts. -/
def Tracks (c : TM0.Cfg Γ Λ) (b : Cfg) : Prop :=
  TM0.step M c = none ∧ (∃ t, Holds 0 (tapeSet c.Tape : Set (ℤ × Fl)) t ∧ b = ⟨[], t⟩) ∨
  (TM0.step M c).isSome ∧ ∃ t, Running c t ∧ b = ⟨mainLoop M :: mv (-pos (Flag.run : Fl)), t⟩

theorem cfgSet_run (c : TM0.Cfg Γ Λ) :
    (cfgSet c ∪ here [.run]) \ {(0, .run)} = (cfgSet c : Set (ℤ × Fl)) := by
  ext ⟨j, f⟩; cases f <;> simp [cfgSet, tapeSet, here]

/-- From a running configuration, the BF program reaches a configuration tracking it. -/
theorem settle (c : TM0.Cfg Γ Λ) (t : Tape Cell) (h : Running c t) :
    ∃ b, Tracks M c b ∧ Reaches step ⟨mainLoop M :: mv (-pos (Flag.run : Fl)), t⟩ b := by
  rcases e : TM0.step M c with _ | c'
  · obtain ⟨u, hu, r⟩ := loop_pass (stepProg M) (by simp [cfgSet, here]) (by
      rw [cfgSet_run, step_den, e]) h (mv (-pos (Flag.run : Fl)))
    obtain ⟨v, hv, r'⟩ := hu.mv (-pos (Flag.run : Fl))
    refine ⟨⟨[], v⟩, .inl ⟨e, v, by simpa using hv, rfl⟩, r.to_reflTransGen.trans
      ((loop_exit _ (by simp [tapeSet]) hu _).trans (by have := r' []; rwa [List.append_nil] at this))⟩
  · exact ⟨_, .inr ⟨by simp [e], t, h, rfl⟩, .refl⟩

theorem respects : Respects (TM0.step M) step (Tracks M) := by
  intro c b h
  rcases e : TM0.step M c with _ | c' <;> simp only
  · rcases h with ⟨-, t, -, rfl⟩ | ⟨h, -⟩
    · rfl
    · simp [e] at h
  · rcases h with ⟨h, -⟩ | ⟨-, t, ht, rfl⟩
    · simp [e] at h
    obtain ⟨u, hu, r⟩ := loop_pass (stepProg M) (by simp [cfgSet, here]) (by
      rw [cfgSet_run, step_den, e]) ht (mv (-pos (Flag.run : Fl)))
    obtain ⟨b', h', r'⟩ := settle M c' u (by
      unfold Running; convert hu using 2; ext ⟨j, f⟩; cases f <;> simp [cfgSet, here])
    exact ⟨b', h', r.trans_left r'⟩

/-! ## The block code -/

/-- Symbol `a` as a block: its `sym` flag raised, unless it is the blank. -/
def enc (a : Γ) : List Cell :=
  (List.finRange (card Fl)).map fun i ↦ if (equivFin Fl).symm i = .sym a ∧ a ≠ default then 1 else 0

theorem enc_length (a : Γ) : (enc (Λ := Λ) a).length = card Fl := by simp [enc]

theorem enc_getI (a : Γ) (f : Fl) :
    (enc (Λ := Λ) a).getI (pos f) = if f = .sym a ∧ a ≠ default then 1 else 0 := by
  rw [enc, List.getI_eq_getElem _ (by simpa using pos_lt f)]; simp [pos]

theorem enc_default : enc (Λ := Λ) (default : Γ) = List.replicate (card Fl) default := by
  simp [enc, List.map_const', default]

theorem enc_injective : Function.Injective (enc (Γ := Γ) (Λ := Λ)) := by
  intro a b h
  by_contra hab
  wlog ha : a ≠ default generalizing a b
  · exact this h.symm (Ne.symm hab) (by rintro rfl; exact ha (by simp_all))
  have := congrArg (·.getI (pos (Flag.sym a : Fl))) h
  simp [enc_getI, ha, hab] at this

/-- The block code of symbols. -/
def code : BlockCode Γ := ⟨card Fl, enc (Λ := Λ), enc_length, enc_default, enc_injective⟩

theorem card_pos : 0 < card Fl := Fintype.card_pos_iff.2 ⟨.run⟩

theorem getI_flatMap {α β : Type*} [Inhabited α] [Inhabited β] (f : α → List β) (w : ℕ)
    (hw : 0 < w) (hl : ∀ a, (f a).length = w) (hd : f default = List.replicate w default)
    (l : List α) (i : ℕ) : (l.flatMap f).getI i = (f (l.getI (i / w))).getI (i % w) := by
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

/-- Every cell index splits into a block and a flag. -/
theorem split (i : ℕ) : ∃ (j : ℕ) (f : Fl), i = card Fl * j + pos f :=
  ⟨i / card Fl, (equivFin Fl).symm ⟨i % card Fl, Nat.mod_lt _ card_pos⟩,
    by simp [pos, Nat.div_add_mod]⟩

theorem div_split (j : ℕ) (f : Fl) : (card Fl * j + pos f) / card Fl = j ∧
    (card Fl * j + pos f) % card Fl = pos f := by
  have := pos_lt f
  constructor
  · rw [Nat.mul_add_div card_pos, Nat.div_eq_of_lt this, add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt this]

theorem flatMap_enc_getI (l : List Γ) (j : ℕ) (f : Fl) :
    (l.flatMap (enc (Λ := Λ))).getI (card Fl * j + pos f) =
      if f = .sym (l.getI j) ∧ l.getI j ≠ default then 1 else 0 := by
  rw [getI_flatMap _ _ card_pos enc_length enc_default, (div_split j f).1, (div_split j f).2,
    enc_getI]

theorem mem_tapeSet {T : Tape Γ} {j : ℤ} {f : Fl} :
    (j, f) ∈ tapeSet T ↔ f = .sym (T.nth j) ∧ T.nth j ≠ default := by
  simp only [tapeSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, rfl, h, rfl⟩; exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact ⟨_, rfl, h, rfl⟩

theorem mk₁_nth {α : Type*} [Inhabited α] (l : List α) (k : ℕ) : (Tape.mk₁ l).nth k = l.getI k := by
  simp [Tape.mk₁, Tape.mk₂, ListBlank.nth_mk]

theorem mk₁_nth_neg {α : Type*} [Inhabited α] (l : List α) {i : ℤ} (hi : i < 0) :
    (Tape.mk₁ l).nth i = default := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = Int.negSucc k := ⟨(-i - 1).toNat, by rw [Int.negSucc_eq]; omega⟩
  rfl

theorem holds_init (l : List Γ) :
    Holds 0 (tapeSet (Tape.mk₁ l) : Set (ℤ × Fl)) (Tape.mk₁ (l.flatMap (enc (Λ := Λ)))) := by
  intro j f
  rw [sub_zero, mem_tapeSet]
  rcases lt_or_ge j 0 with hj | hj
  · have : (card Fl : ℤ) * j + pos f < 0 := by
      have := pos_lt f
      nlinarith [mul_le_mul_of_nonneg_left (show j ≤ -1 by omega) (Nat.cast_nonneg (α := ℤ) (card Fl))]
    simp [mk₁_nth_neg _ this, mk₁_nth_neg _ hj]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    rw [show (card Fl : ℤ) * k + pos f = ((card Fl * k + pos f : ℕ) : ℤ) by push_cast; ring,
      mk₁_nth, flatMap_enc_getI, mk₁_nth]
    congr

theorem right₀_eq (T : Tape Γ) (t : Tape Cell) (h : Holds 0 (tapeSet T : Set (ℤ × Fl)) t) :
    t.right₀ = (code (Λ := Λ)).encTape T.right₀ := by
  apply ListBlank.ext
  intro i
  obtain ⟨j, f, rfl⟩ := split (Γ := Γ) (Λ := Λ) i
  have key : ∀ L : ListBlank Γ, (L.flatMap (enc (Λ := Λ)) ⟨card Fl, enc_default⟩).nth
      (card Fl * j + pos f) = if f = .sym (L.nth j) ∧ L.nth j ≠ default then 1 else 0 :=
    fun L ↦ L.induction_on fun l ↦ by
      simp only [ListBlank.flatMap_mk, ListBlank.nth_mk, flatMap_enc_getI]; congr
  rw [Tape.right₀_nth, BlockCode.encTape, code, key, Tape.right₀_nth]
  have := h j f
  rw [sub_zero, show ((card Fl : ℤ) * (j : ℤ) + (pos f : ℤ)) = ((card Fl * j + pos f : ℕ) : ℤ) by
    push_cast; ring, mem_tapeSet] at this
  convert this using 2

/-! ## The claim -/

theorem eval_eq (l : List Γ) :
    eval (program M) (l.flatMap (code (Λ := Λ)).enc) = (TM0.eval M l).map (code (Λ := Λ)).encTape := by
  obtain ⟨t₁, h₁, r₁⟩ := compile_spec (FProg.set (Flag.state default : Fl) ⨾ .set .run)
    (P := tapeSet (Tape.mk₁ l)) rfl (holds_init l)
  obtain ⟨t₂, h₂, r₂⟩ := h₁.mv (pos (Flag.run : Fl))
  obtain ⟨b, hb, rb⟩ := settle M (TM0.init l) t₂ (by
    rw [zero_add] at h₂
    unfold Running; convert h₂ using 2
    ext ⟨j, f⟩; cases f <;> simp [cfgSet, tapeSet, here, TM0.init])
  have h0 : Reaches step (init (program M) (l.flatMap (code (Λ := Λ)).enc))
      ⟨mainLoop M :: mv (-pos (Flag.run : Fl)), t₂⟩ := by
    have := (r₁.seq r₂) (mainLoop M :: mv (-pos (Flag.run : Fl)))
    simpa [init, program, atFlag, code, List.append_assoc] using this
  unfold eval TM0.eval
  rw [reaches_eval (h0.trans rb)]
  ext x
  simp only [Part.map_map, Part.mem_map_iff, Function.comp]
  constructor
  · rintro ⟨b₂, hb₂, rfl⟩
    obtain ⟨c, hc, hc₂⟩ := tr_eval_rev (respects M) hb hb₂
    rcases hc with ⟨_, t, ht, rfl⟩ | ⟨h, _⟩
    · exact ⟨c, hc₂, (right₀_eq c.Tape t ht).symm⟩
    · simp [(mem_eval.1 hc₂).2] at h
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨b₂, hb₂, hc₂⟩ := tr_eval (respects M) hb hc
    rcases hb₂ with ⟨_, t, ht, rfl⟩ | ⟨h, _⟩
    · exact ⟨_, hc₂, right₀_eq c.Tape t ht⟩
    · simp [(mem_eval.1 hc).2] at h

/-- **Brainfuck simulates every finite TM0 machine.** -/
theorem claim : Claim := fun M ↦ ⟨code, program M, eval_eq M⟩

end BF.Elegant
