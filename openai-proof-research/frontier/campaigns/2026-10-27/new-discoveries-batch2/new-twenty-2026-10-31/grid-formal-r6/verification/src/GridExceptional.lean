module
public import GridExceptionalCountTwo
public import GridExceptionalSubgroups
public import Mathlib.Data.SetLike.Fintype
@[expose] public section
namespace Grid343536
theorem subgroup_card_ge_ten (k : ℕ) (hk : k = 2 ∨ k = 3) :
    10 ≤ Nat.card (Subgroup (G k k ≃g G k k)) := by
  have : Finite (G k k ≃g G k k) := DFunLike.finite _
  have : Finite (Subgroup (G k k ≃g G k k)) := inferInstance
  have h := Nat.card_le_card_of_injective (explicitSubgroup k hk)
    (explicitSubgroup_injective k hk)
  simpa using h

theorem exceptional_no_iso : ExceptionalNoIso := by
  intro k hk hl ⟨e⟩
  have hc := Nat.card_congr e.toEquiv
  have hlow := subgroup_card_ge_ten k (by omega)
  have hcases : k = 2 ∨ k = 3 := by omega
  rcases hcases with rfl | rfl
  · have hu := equitable2_card_le
    omega
  · have hu := equitable3_card_le
    omega
end Grid343536
