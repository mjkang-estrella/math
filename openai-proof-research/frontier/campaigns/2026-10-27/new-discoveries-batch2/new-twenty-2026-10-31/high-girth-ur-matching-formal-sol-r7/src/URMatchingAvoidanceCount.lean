module
public import URMatchingPermutationFibers
@[expose] public section
namespace URMatching
open scoped Classical
/-- Exact extension multiplicity for any injection on a subset. -/
theorem restriction_fiber_card {N : ℕ} (A : Finset (Fin N)) (f : A ↪ Fin N) :
    Fintype.card {σ : Equiv.Perm (Fin N) // restriction A σ = f} =
      (N - A.card).factorial := by
  classical
  let K := Fintype.card {σ : Equiv.Perm (Fin N) // restriction A σ = f}
  have hc (g : A ↪ Fin N) :
      Fintype.card {σ : Equiv.Perm (Fin N) // restriction A σ = g} = K :=
    Fintype.card_congr (restrictionFiberEquiv A g f)
  have ht : N.factorial = Fintype.card (A ↪ Fin N) * K := by
    calc
      N.factorial = Fintype.card (Equiv.Perm (Fin N))  := by simp [Fintype.card_perm]
      _ = Fintype.card (Σ g : A ↪ Fin N,
          {σ : Equiv.Perm (Fin N) // restriction A σ = g}) :=
        (Fintype.card_congr (Equiv.sigmaFiberEquiv (restriction A))).symm
      _ = _ := by simp only [Fintype.card_sigma, hc, Finset.sum_const,
          Finset.card_univ, smul_eq_mul]
  have ha : A.card ≤ N := by simpa using A.card_le_univ
  have he : Fintype.card (A ↪ Fin N) = N.descFactorial A.card := by simp
  have hp : 0 < Fintype.card (A ↪ Fin N) := by
    let : Nonempty (A ↪ Fin N) := ⟨restriction A (Equiv.refl _)⟩
    exact Fintype.card_pos
  apply Nat.mul_left_cancel hp
  rw [← ht, he, Nat.mul_comm]
  exact (Nat.factorial_mul_descFactorial ha).symm

/-- Avoidance is equivalent to an injective image into the complement of B. -/
noncomputable def avoidingEmbeddingEquiv {N : ℕ} (A B : Finset (Fin N)) :
    {f : A ↪ Fin N // ∀ x : A, f x ∉ B} ≃ (A ↪ {y : Fin N // y ∉ B}) where
  toFun f := ⟨fun x => ⟨f.val x, f.property x⟩,
    fun _ _ h => f.val.injective (congrArg Subtype.val h)⟩
  invFun f := ⟨⟨fun x => (f x).val,
    fun _ _ h => f.injective (Subtype.ext h)⟩, fun x => (f x).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact one-colour count, including impossible rectangles and empty subsets. -/
theorem one_colour_avoidance_count {N : ℕ} (A B : Finset (Fin N)) :
    Fintype.card {σ : Equiv.Perm (Fin N) // AvoidsRectangle A B σ} =
      (N - B.card).descFactorial A.card * (N - A.card).factorial := by
  classical
  let E : (A ↪ Fin N) → Prop := fun f => ∀ x : A, f x ∉ B
  have eh (σ : Equiv.Perm (Fin N)) : AvoidsRectangle A B σ ↔ E (restriction A σ) := by
    constructor
    · intro h x; exact h x x.property
    · intro h x hx; exact h ⟨x, hx⟩
  calc
    _ = Fintype.card (Σ f : {f : A ↪ Fin N // E f},
        {σ : Equiv.Perm (Fin N) // restriction A σ = f.val}) :=
      (Fintype.card_congr (Equiv.sigmaSubtypeFiberEquivSubtype (restriction A) eh)).symm
    _ = Fintype.card {f : A ↪ Fin N // E f} * (N - A.card).factorial := by
      simp only [Fintype.card_sigma, restriction_fiber_card, Finset.sum_const,
        Finset.card_univ, smul_eq_mul]
    _ = _ := by
      rw [Fintype.card_congr (avoidingEmbeddingEquiv A B)]
      simp
end URMatching
