import BfTuringComplete.Exposition.Machine

/-!
# Brainfuck simulates every TM0 machine

The program raises `state default` and `run`, then loops on `run`: each pass clears `run` and
performs one TM step (`step_den`), which raises `run` again unless the machine halted. The final
tape holds exactly the TM's final tape in the block code `enc`.
-/

namespace BF.Exposition
open Turing StateTransition Relation FinEnum FProg

variable {Γ Λ : Type*} [Inhabited Γ]

local notation "Fl" => Flag Γ Λ

/-! ## The block code -/

theorem symFlags_default (f : Fl) : ¬symFlags (default : Γ) f := by simp [symFlags]

/-- Symbol `a` as a block: its `sym` flag raised, unless it is the blank. -/
abbrev enc [FinEnum Γ] [FinEnum Λ] : Γ → List Cell := fun a ↦ block (symFlags (Λ := Λ) a)

theorem enc_injective [FinEnum Γ] [FinEnum Λ] : Function.Injective (enc (Γ := Γ) (Λ := Λ)) := by
  intro a b h
  by_contra hab
  wlog ha : a ≠ default generalizing a b
  · exact this h.symm (Ne.symm hab) (by rintro rfl; exact ha (by simp_all))
  have := congrArg (·.getI (pos (Flag.sym a : Fl))) h
  simp [enc, block_getI, symFlags, ha, hab] at this

/-- The block code of symbols. -/
def code [FinEnum Γ] [FinEnum Λ] : BlockCode Γ where
  width := card Fl
  enc := enc (Λ := Λ)
  length_enc _ := block_length _
  enc_default := by simp [enc, block, symFlags, List.map_const', default]
  injective := enc_injective

theorem cfgSet_run (c : TM0.Cfg Γ Λ) :
    (cfgSet c ∪ here [.run]) \ {(0, .run)} = (cfgSet c : Set (ℤ × Fl)) := by
  ext ⟨j, f⟩; cases f <;> simp [cfgSet, tapeSet, symFlags, here]

/-! ## The main loop -/

variable [Inhabited Λ] [FinEnum Γ] [FinEnum Λ] (M : TM0.Machine Γ Λ)


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

/-- From a running configuration, the BF program reaches a configuration tracking it. -/
theorem settle (c : TM0.Cfg Γ Λ) (t : Tape Cell) (h : Running c t) :
    ∃ b, Tracks M c b ∧ Reaches step ⟨mainLoop M :: mv (-pos (Flag.run : Fl)), t⟩ b := by
  rcases e : TM0.step M c with _ | c'
  · obtain ⟨u, hu, r⟩ := loop_pass (stepProg M) (by simp [cfgSet, here]) (by
      rw [cfgSet_run, step_den, e]) h (mv (-pos (Flag.run : Fl)))
    obtain ⟨v, hv, r'⟩ := hu.mv (-pos (Flag.run : Fl))
    refine ⟨⟨[], v⟩, .inl ⟨e, v, by simpa using hv, rfl⟩, r.to_reflTransGen.trans
      ((loop_exit _ (by simp [tapeSet, symFlags]) hu _).trans
        (by have := r' []; rwa [List.append_nil] at this))⟩
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

/-! ## The claim -/

theorem eval_eq (l : List Γ) :
    eval (program M) (l.flatMap (code (Λ := Λ)).enc) =
      (TM0.eval M l).map (code (Λ := Λ)).encTape := by
  obtain ⟨t₁, h₁, r₁⟩ := compile_spec (FProg.set (Flag.state default : Fl) ⨾ .set .run)
    (P := tapeSet (Tape.mk₁ l)) rfl (holds_mk₁ _ symFlags_default l)
  obtain ⟨t₂, h₂, r₂⟩ := h₁.mv (pos (Flag.run : Fl))
  obtain ⟨b, hb, rb⟩ := settle M (TM0.init l) t₂ (by
    rw [zero_add] at h₂
    unfold Running; convert h₂ using 2
    ext ⟨j, f⟩; cases f <;> simp [cfgSet, tapeSet, symFlags, here, TM0.init])
  have h0 : Reaches step (init (program M) (l.flatMap (code (Λ := Λ)).enc))
      ⟨mainLoop M :: mv (-pos (Flag.run : Fl)), t₂⟩ := by
    have := (r₁.seq r₂) (mainLoop M :: mv (-pos (Flag.run : Fl)))
    simpa [init, program, atFlag, code, enc, List.append_assoc] using this
  unfold eval TM0.eval
  rw [reaches_eval (h0.trans rb)]
  ext x
  simp only [Part.map_map, Part.mem_map_iff, Function.comp]
  constructor
  · rintro ⟨b₂, hb₂, rfl⟩
    obtain ⟨c, hc, hc₂⟩ := tr_eval_rev (respects M) hb hb₂
    rcases hc with ⟨_, t, ht, rfl⟩ | ⟨h, _⟩
    · exact ⟨c, hc₂, (right₀_eq _ symFlags_default c.Tape t ht).symm⟩
    · simp [(mem_eval.1 hc₂).2] at h
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨b₂, hb₂, hc₂⟩ := tr_eval (respects M) hb hc
    rcases hb₂ with ⟨_, t, ht, rfl⟩ | ⟨h, _⟩
    · exact ⟨_, hc₂, right₀_eq _ symFlags_default c.Tape t ht⟩
    · simp [(mem_eval.1 hc).2] at h

/-- **Brainfuck simulates every finite TM0 machine.** -/
theorem claim : Claim := by
  intro Γ Λ _ _ _ _ M
  classical
  let _ : FinEnum Γ := .ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
  let _ : FinEnum Λ := .ofEquiv (Fin (Fintype.card Λ)) (Fintype.equivFin Λ)
  exact ⟨code, program M, eval_eq M⟩

end BF.Exposition
