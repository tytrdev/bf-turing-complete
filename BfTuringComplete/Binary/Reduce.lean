import BfTuringComplete.Core.Statement
import Mathlib

/-!
# Reducing the claim to binary machines

If Brainfuck simulates every finite TM0 machine over `Bool`, it simulates every finite TM0 machine.
Mathlib supplies the reductions: `TM0to1` (TM0 → TM1), `TM1to1` (any finite alphabet → `Bool`,
each symbol a fixed-width block of bits), `TM1to0` (TM1 → TM0). The machines in between have
infinite state types, so we restrict to the finitely many reachable states (`TM0.Machine.map`).
A symbol is then encoded as its bits, each bit encoded by the binary block code.
-/

noncomputable section
namespace BF.Binary
open Turing StateTransition
attribute [local instance] Classical.propDecidable

/-- BF simulates every finite TM0 machine over `Bool`. -/
def BinaryClaim.{v} : Prop :=
  ∀ {Λ : Type v} [Inhabited Λ] [Fintype Λ] (M : TM0.Machine Bool Λ),
    ∃ (c : BlockCode Bool) (p : Program),
      ∀ l : List Bool, eval p (l.flatMap c.enc) = (TM0.eval M l).map c.encTape

/-! ## Evaluation along a simulation -/

/-- Readouts agree along a simulation: `tr_eval` and `tr_eval_rev`, packaged, for any universes. -/
theorem eval_map {σ₁ σ₂ α : Type*} {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂}
    {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) (g : σ₁ → α) (h : σ₂ → α)
    (hgh : ∀ a b, tr a b → g a = h b) {a₁ : σ₁} {a₂ : σ₂} (ha : tr a₁ a₂) :
    (StateTransition.eval f₂ a₂).map h = (StateTransition.eval f₁ a₁).map g := by
  ext x
  simp only [Part.mem_map_iff]
  constructor
  · rintro ⟨b₂, hb₂, rfl⟩
    obtain ⟨b₁, hb, hb₁⟩ := tr_eval_rev H ha hb₂
    exact ⟨b₁, hb₁, hgh _ _ hb⟩
  · rintro ⟨b₁, hb₁, rfl⟩
    obtain ⟨b₂, hb, hb₂⟩ := tr_eval H ha hb₁
    exact ⟨b₂, hb₂, (hgh _ _ hb).symm⟩

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-! ## TM0 → TM1 -/

instance [Finite Γ] [Finite Λ] : Finite (TM0to1.Λ' Γ Λ) := by
  refine Finite.of_injective (β := Λ ⊕ ((Bool ⊕ Γ) × Λ)) (fun
    | .normal q => .inl q
    | .act (.move d) q => .inr (.inl (d == .left), q)
    | .act (.write a) q => .inr (.inr a, q)) ?_
  rintro (_ | ⟨_ | _, _⟩) (_ | ⟨_ | _, _⟩) h <;> simp_all <;>
    cases ‹Dir› <;> cases ‹Dir› <;> simp_all

omit [Inhabited Γ] [Inhabited Λ] in
theorem supportsStmt_univ {σ : Type*} [Fintype Λ] (q : TM1.Stmt Γ Λ σ) :
    TM1.SupportsStmt Finset.univ q := by
  induction q <;> simp_all [TM1.SupportsStmt]

theorem tm0to1_eval (M : TM0.Machine Γ Λ) (l : List Γ) :
    TM1.eval (TM0to1.tr M) l = TM0.eval M l := by
  have hr : Reaches (TM1.step (TM0to1.tr M)) (TM1.init l) (TM0to1.trCfg M (TM0.init l)) := by
    cases e : M default (Tape.mk₁ l).head
    · refine Relation.ReflTransGen.single ?_
      simp [TM1.step, TM1.init, TM0to1.trCfg, TM0.init, TM1.stepAux, e,
        show (default : TM0to1.Λ' Γ Λ) = .normal default from rfl, TM0to1.tr]
    · simp only [TM0to1.trCfg, TM0.init, e, Option.isSome_some, Bool.cond_true]
      exact Relation.ReflTransGen.refl
  unfold TM1.eval TM0.eval
  rw [reaches_eval hr]
  exact eval_map (TM0to1.tr_respects M) (fun c => c.Tape.right₀) (fun c => c.Tape.right₀)
    (by rintro ⟨q, T⟩ _ rfl; rfl) rfl

/-! ## Any finite alphabet → `Bool` -/

section bits
variable {n : ℕ} {enc : Γ → List.Vector Bool n}

theorem bits_default (enc0 : enc default = List.Vector.replicate n false) :
    ∃ k, (fun x => (enc x).toList) default = List.replicate k default :=
  ⟨n, by simp [enc0, List.Vector.replicate]⟩

theorem tm1to1_eval (enc0 : enc default = List.Vector.replicate n false) {σ : Type*}
    [Inhabited σ] (dec : List.Vector Bool n → Γ) (encdec : ∀ a, dec (enc a) = a)
    (M : Λ → TM1.Stmt Γ Λ σ) (l : List Γ) :
    TM1.eval (TM1to1.tr enc dec M) (l.flatMap fun x => (enc x).toList) =
      (TM1.eval M l).map (·.flatMap (fun x => (enc x).toList) (bits_default enc0)) := by
  unfold TM1.eval
  rw [Part.map_map]
  refine eval_map (TM1to1.tr_respects (enc0 := enc0) dec M encdec) _ _ ?_ ?_
  · rintro ⟨q, v, T⟩ _ rfl
    simp [TM1to1.trCfg, TM1to1.trTape, TM1to1.trTape']
  · simp only [TM1to1.trCfg, TM1.init, TM1to1.trTape, TM1to1.trTape', Tape.mk₁]
    congr 2
    simp [Tape.mk₂, ListBlank.flatMap_mk]
end bits

/-! ## Restricting to the reachable states -/

section restrict
variable {Λ₀ : Type*} [Inhabited Λ₀] (M : TM0.Machine Bool Λ₀) (S : Finset Λ₀)

/-- The reachable states (plus the start state), as a finite type. -/
abbrev Reach := {q // q ∈ insert default S}

instance : Inhabited (Reach S) := ⟨⟨default, Finset.mem_insert_self _ _⟩⟩

/-- Enter the finite state type (pointed: `default ↦ default`). -/
def enter : PointedMap Λ₀ (Reach S) :=
  ⟨fun q => if h : q ∈ insert default S then ⟨q, h⟩ else default, by simp; rfl⟩

theorem enter_f {q : Λ₀} (h : q ∈ insert default S) : (enter S).f q = ⟨q, h⟩ :=
  dite_eq_left_of_eq_true (eq_true h)

def idB : PointedMap Bool Bool := ⟨id, rfl⟩

theorem map_idB (T : Tape Bool) : T.map idB = T := by
  obtain ⟨L, R, rfl⟩ := T.exists_mk'
  induction L using ListBlank.induction_on
  induction R using ListBlank.induction_on
  simp [Tape.map_mk', ListBlank.map_mk, idB]

/-- The machine on the reachable states. -/
def restrict : TM0.Machine Bool (Reach S) := M.map idB idB (enter S) Subtype.val

theorem restrict_eval (hS : TM0.Supports M ↑S) (l : List Bool) :
    TM0.eval (restrict M S) l = TM0.eval M l := by
  have H := TM0.Machine.map_respects M idB idB (enter S) Subtype.val hS (fun _ => rfl)
    (fun q hq => by rw [enter_f S (Finset.mem_insert_of_mem (Finset.mem_coe.1 hq))])
  unfold TM0.eval
  refine eval_map H (fun c => c.Tape.right₀) (fun c => c.Tape.right₀) ?_ ⟨hS.1, ?_⟩
  · rintro ⟨q, T⟩ _ ⟨-, rfl⟩
    simp [TM0.Cfg.map, map_idB]
  · rw [TM0.map_init]; simp [idB]
end restrict

/-! ## Composing block codes -/

/-- Concatenating fixed-width, injective blocks is injective. -/
theorem flatMap_inj {α β : Type*} {f : α → List β} {w : ℕ} (hw : ∀ a, (f a).length = w)
    (hw0 : 0 < w) (hf : Function.Injective f) : Function.Injective (List.flatMap f) := by
  intro l₁ l₂ h
  induction l₁ generalizing l₂ with
  | nil => cases l₂ with
    | nil => rfl
    | cons b l₂ => have := congrArg List.length h; simp [hw] at this; omega
  | cons a l₁ ih => cases l₂ with
    | nil => have := congrArg List.length h; simp [hw] at this; omega
    | cons b l₂ =>
      simp only [List.flatMap_cons] at h
      obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [hw, hw])
      rw [hf h₁, ih h₂]

/-- A symbol as its bits, each bit as a binary block. -/
def compose {n : ℕ} (enc : Γ → List.Vector Bool n)
    (enc0 : enc default = List.Vector.replicate n false)
    (dec : List.Vector Bool n → Γ) (encdec : ∀ a, dec (enc a) = a) (c : BlockCode Bool) :
    BlockCode Γ where
  width := n * c.width
  enc a := (enc a).toList.flatMap c.enc
  length_enc a := by simp [List.length_flatMap, c.length_enc]
  enc_default := by
    simp [enc0, List.Vector.replicate, show c.enc false = _ from c.enc_default,
      List.flatMap_replicate]
  injective a b h := by
    rcases Nat.eq_zero_or_pos c.width with h0 | h0
    · have h1 := c.length_enc false
      have h2 := c.length_enc true
      rw [h0, List.length_eq_zero_iff] at h1 h2
      exact absurd (c.injective (h1.trans h2.symm)) Bool.false_ne_true
    · rw [← encdec a, ← encdec b, List.Vector.eq _ _ (flatMap_inj c.length_enc h0 c.injective h)]

theorem encTape_compose {n : ℕ} (enc : Γ → List.Vector Bool n)
    (enc0 : enc default = List.Vector.replicate n false) (dec : List.Vector Bool n → Γ)
    (encdec : ∀ a, dec (enc a) = a) (c : BlockCode Bool) (R : ListBlank Γ) :
    c.encTape (R.flatMap (fun x => (enc x).toList) (bits_default enc0)) =
      (compose enc enc0 dec encdec c).encTape R := by
  induction R using ListBlank.induction_on
  simp [BlockCode.encTape, ListBlank.flatMap_mk, compose, List.flatMap_assoc]

/-! ## The reduction -/

theorem claim_of_binary (h : BinaryClaim.{max u v}) : Claim.{u, v} := by
  intro Γ Λ _ _ _ _ M
  classical
  -- TM0 → TM1
  let M₁ := TM0to1.tr M
  let : Fintype (TM0to1.Λ' Γ Λ) := Fintype.ofFinite _
  have s₁ : TM1.Supports M₁ Finset.univ := ⟨Finset.mem_univ _, fun q _ => supportsStmt_univ _⟩
  -- any alphabet → Bool
  obtain ⟨n, enc, dec, enc0, encdec⟩ := TM1to1.exists_enc_dec (Γ := Γ)
  let M₂ := TM1to1.tr enc dec M₁
  -- TM1 → TM0, restricted to the reachable states
  let M₃ := TM1to0.tr M₂
  let S := TM1to0.trStmts M₂ (TM1to1.trSupp M₁ Finset.univ)
  have s₃ : TM0.Supports M₃ ↑S := TM1to0.tr_supports M₂ (TM1to1.tr_supports enc dec M₁ s₁)
  obtain ⟨c, p, hp⟩ := h (restrict M₃ S)
  refine ⟨compose enc enc0 dec encdec c, p, fun l => ?_⟩
  have e : l.flatMap (compose enc enc0 dec encdec c).enc =
      (l.flatMap fun x => (enc x).toList).flatMap c.enc := by
    simp [compose, List.flatMap_assoc]
  rw [e, hp, restrict_eval M₃ S s₃, TM1to0.tr_eval, tm1to1_eval enc0 dec encdec, tm0to1_eval,
    Part.map_map]
  congr 1
  funext R
  exact encTape_compose enc enc0 dec encdec c R

end BF.Binary
