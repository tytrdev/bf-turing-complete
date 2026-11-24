import BfTuringComplete.Statement
import BfTuringComplete.Loop
import Mathlib.Data.Fintype.EquivFin

/-!
# Main theorem: BF simulates every finite TM0 machine

We relabel an arbitrary finite machine to one over `Fin (n+1)` symbols and
`Fin (m+1)` states (blank and the start state both ↦ 0), then apply `compile_eval`.
-/

namespace BF

open Turing StateTransition Relation

/-- Any finite inhabited type is `Fin (k+1)`, with `default ↦ 0`. -/
theorem exists_equiv_fin (α : Type*) [Fintype α] [Inhabited α] :
    ∃ (k : ℕ) (e : α ≃ Fin (k + 1)), e default = 0 := by
  have hpos : 0 < Fintype.card α := Fintype.card_pos
  let e1 : α ≃ Fin (Fintype.card α - 1 + 1) := (Fintype.equivFin α).trans (finCongr (by omega))
  exact ⟨_, e1.trans (Equiv.swap (e1 default) 0), by simp⟩

section Relabel

variable {Γ Λ Γ' Λ' : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Γ'] [Inhabited Λ']
  (eΓ : Γ ≃ Γ') (eΛ : Λ ≃ Λ') (hΓ : eΓ default = default) (hΛ : eΛ default = default)

def stmtMap : TM0.Stmt Γ → TM0.Stmt Γ'
  | .move d => .move d
  | .write a => .write (eΓ a)

/-- The machine `M` with symbols and states renamed. -/
def conj (M : TM0.Machine Γ Λ) : TM0.Machine Γ' Λ' :=
  fun q a ↦ (M (eΛ.symm q) (eΓ.symm a)).map fun p ↦ (eΛ p.1, stmtMap eΓ p.2)

def pmap : PointedMap Γ Γ' := ⟨eΓ, hΓ⟩

def trCfg (c : TM0.Cfg Γ Λ) : TM0.Cfg Γ' Λ' := ⟨eΛ c.q, c.Tape.map (pmap eΓ hΓ)⟩

theorem conj_step (M : TM0.Machine Γ Λ) (c : TM0.Cfg Γ Λ) :
    TM0.step (conj eΓ eΛ M) (trCfg eΓ eΛ hΓ c) = (TM0.step M c).map (trCfg eΓ eΛ hΓ) := by
  obtain ⟨q, T⟩ := c
  simp only [TM0.step, trCfg, conj, Tape.map_fst, pmap, Equiv.symm_apply_apply]
  rcases M q T.1 with _ | ⟨q', s⟩
  · rfl
  · cases s <;> simp [stmtMap, Tape.map_move, Tape.map_write, pmap, trCfg]

theorem right₀_map (T : Tape Γ) : (T.map (pmap eΓ hΓ)).right₀ = T.right₀.map (pmap eΓ hΓ) := by
  obtain ⟨a, L, R⟩ := T
  simp [Tape.map, Tape.right₀, ListBlank.map_cons]

include hΛ in
theorem conj_eval (M : TM0.Machine Γ Λ) (l : List Γ) :
    TM0.eval (conj eΓ eΛ M) (l.map eΓ) = (TM0.eval M l).map (ListBlank.map (pmap eΓ hΓ)) := by
  have H : Respects (TM0.step M) (TM0.step (conj eΓ eΛ M))
      fun a b ↦ trCfg eΓ eΛ hΓ a = b := by
    rw [fun_respects]
    intro c
    rcases h : TM0.step M c with _ | b
    · simp [FRespects, conj_step, h]
    · exact TransGen.single (by simp [conj_step, h])
  have hinit : trCfg eΓ eΛ hΓ (TM0.init l) = TM0.init (l.map eΓ) := by
    simp only [trCfg, TM0.init, hΛ, Tape.map_mk₁]
    rfl
  unfold TM0.eval
  rw [← hinit]
  ext x
  simp only [Part.map_map, Part.mem_map_iff, Function.comp]
  constructor
  · rintro ⟨b₂, hb₂, rfl⟩
    obtain ⟨b₁, hb, hb₁⟩ := tr_eval_rev H rfl hb₂
    subst hb
    exact ⟨b₁, hb₁, (right₀_map eΓ hΓ b₁.Tape).symm⟩
  · rintro ⟨b₁, hb₁, rfl⟩
    obtain ⟨b₂, hb, hb₂⟩ := tr_eval H rfl hb₁
    subst hb
    exact ⟨_, hb₂, right₀_map eΓ hΓ b₁.Tape⟩

end Relabel

theorem encSym_injective (n m : ℕ) : Function.Injective (encSym n m) := by
  intro a b h
  have hw : n < Layout.width n m := by simp [Layout.width]; omega
  have key : ∀ r, r < n → (encSym n m a).getI r = (encSym n m b).getI r := fun r _ ↦ by rw [h]
  apply Fin.ext
  by_contra hne
  have ha := a.isLt
  have hb := b.isLt
  rcases Nat.eq_zero_or_pos a.val with h0 | h0
  · have := key (b.val - 1) (by omega)
    rw [encSym_getI _ (by omega), encSym_getI _ (by omega)] at this
    simp only [show ¬(b.val - 1 < n ∧ b.val - 1 + 1 = a.val) by omega,
      show (b.val - 1 < n ∧ b.val - 1 + 1 = b.val) by omega] at this
    simp at this
    omega
  · have := key (a.val - 1) (by omega)
    rw [encSym_getI _ (by omega), encSym_getI _ (by omega)] at this
    simp only [show (a.val - 1 < n ∧ a.val - 1 + 1 = a.val) by omega,
      show ¬(a.val - 1 < n ∧ a.val - 1 + 1 = b.val) by omega] at this
    simp at this
    omega

theorem flatMap_map_enc {Γ : Type*} (n m : ℕ) (e : Γ → Fin (n + 1)) (l : List Γ) :
    (l.map e).flatMap (encSym n m) = l.flatMap (fun a ↦ encSym n m (e a)) := by
  induction l <;> simp_all

/-- **Main theorem.** BF (8-bit wrapping cells, unbounded tape) simulates every finite TM0
machine: an injective, fixed-width, blank-to-zero block code `c` and a BF program `p` such
that running `p` on the encoded input gives exactly the encoded TM output, and runs
forever exactly when the TM does. -/
theorem simulates_TM0 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Fintype Γ] [Fintype Λ]
    (M : TM0.Machine Γ Λ) :
    ∃ (c : BlockCode Γ) (p : Program),
      ∀ l : List Γ, eval p (l.flatMap c.enc) = (TM0.eval M l).map c.encTape := by
  obtain ⟨n, eΓ, hΓ⟩ := exists_equiv_fin Γ
  obtain ⟨m, eΛ, hΛ⟩ := exists_equiv_fin Λ
  refine ⟨⟨Layout.width n m, fun a ↦ encSym n m (eΓ a), fun a ↦ encSym_length _,
    by rw [hΓ]; exact encSym_default n m, (encSym_injective n m).comp eΓ.injective⟩,
    compile n m (conj eΓ eΛ M), fun l ↦ ?_⟩
  rw [← flatMap_map_enc, compile_eval, conj_eval eΓ eΛ hΓ hΛ, Part.map_map]
  congr 1
  funext L
  simp only [Function.comp, BlockCode.encTape]
  induction L using ListBlank.induction_on with
  | _ l =>
    rw [ListBlank.map_mk, ListBlank.flatMap_mk, ListBlank.flatMap_mk]
    exact congrArg ListBlank.mk (flatMap_map_enc n m eΓ l)

end BF
