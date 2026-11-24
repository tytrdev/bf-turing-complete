import BfTuringComplete.Basic
import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# The target theorem

The definitions for the main theorem (proved in `Main.lean`): every finite TM0 machine
is simulated by a BF program, where each TM symbol is
stored as a fixed-width block of BF cells. The block code must be injective
(no hiding information) and send blank to all-zero cells (so the infinite blank
parts of the tapes line up). The final BF tape must be *exactly* the encoded
final TM tape: scratch cleaned up, head back in place.
-/

namespace BF

open Turing

example : (default : Cell) = 0 := rfl

/-- A fixed-width, injective, blank-preserving encoding of symbols as BF cells. -/
structure BlockCode (Γ : Type*) [Inhabited Γ] where
  width : ℕ
  enc : Γ → List Cell
  length_enc : ∀ a, (enc a).length = width
  enc_default : enc default = List.replicate width default
  injective : Function.Injective enc

/-- Encode a whole (blank-extended) tape half, symbol by symbol. -/
def BlockCode.encTape {Γ : Type*} [Inhabited Γ] (c : BlockCode Γ) (L : ListBlank Γ) :
    ListBlank Cell :=
  L.flatMap c.enc ⟨c.width, c.enc_default⟩

end BF
