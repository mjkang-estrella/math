module
public import URMatchingAvoidanceCount
@[expose] public section
namespace URMatching
open scoped Classical
/-- Exact finite independent prescription count, with a different prescribed
injective partial map in every colour. No consistency assumption is hidden. -/
noncomputable def prescriptionEventEquiv (N d : ℕ) (A : Fin d → Finset (Fin N))
    (f : ∀ c, A c ↪ Fin N) :
    {σ : PermutationTuples N d // ∀ c, restriction (A c) (σ c) = f c} ≃
      (∀ c, {τ : Equiv.Perm (Fin N) // restriction (A c) τ = f c}) where
  toFun σ c := ⟨σ.val c, σ.property c⟩
  invFun τ := ⟨fun c => (τ c).val, fun c => (τ c).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem independent_prescription_count (N d : ℕ) (A : Fin d → Finset (Fin N))
    (f : ∀ c, A c ↪ Fin N) :
    Fintype.card {σ : PermutationTuples N d // ∀ c, restriction (A c) (σ c) = f c} =
      ∏ c, (N - (A c).card).factorial := by
  classical
  rw [Fintype.card_congr (prescriptionEventEquiv N d A f), Fintype.card_pi]
  simp only [restriction_fiber_card]

/-- A repeated input with different outputs is impossible, in the full space. -/
theorem inconsistent_input_count (N d : ℕ) (c : Fin d) (x y z : Fin N) (h : y ≠ z) :
    Fintype.card {σ : PermutationTuples N d // σ c x = y ∧ σ c x = z} = 0 := by
  classical
  let : IsEmpty {σ : PermutationTuples N d // σ c x = y ∧ σ c x = z} :=
    ⟨fun σ => h (σ.property.1.symm.trans σ.property.2)⟩
  exact Fintype.card_eq_zero

/-- A repeated output at different inputs is equally impossible. -/
theorem inconsistent_output_count (N d : ℕ) (c : Fin d) (x y z : Fin N) (h : x ≠ y) :
    Fintype.card {σ : PermutationTuples N d // σ c x = z ∧ σ c y = z} = 0 := by
  classical
  let : IsEmpty {σ : PermutationTuples N d // σ c x = z ∧ σ c y = z} :=
    ⟨fun σ => h ((σ.val c).injective (σ.property.1.trans σ.property.2.symm))⟩
  exact Fintype.card_eq_zero
end URMatching
