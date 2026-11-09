import Defs
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option warningAsError true
namespace Palette
def all4 (f : C → Bool) : Bool := f 0 && f 1 && f 2 && f 3
theorem all4_spec (f : C → Bool) : all4 f = true ↔ ∀ x, f x = true := by
  simp only [all4, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨h0,h1⟩,h2⟩,h3⟩ x
    fin_cases x <;> assumption
  · intro h
    exact ⟨⟨⟨h 0,h 1⟩,h 2⟩,h 3⟩
def code (a b c : C) : Nat := (2^a.val ||| 2^b.val) ||| 2^c.val
theorem code_sound : ∀ a b c d e f : C, code a b c = code d e f → pal a b c = pal d e f := by decide
end Palette
