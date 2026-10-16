/- Copyright 2026 Myeongjin Kang. MIT. Kernel-checked examples and obstructions. -/
import KnMinusEdge

open scoped BigOperators
open KnMinusEdge Module
namespace KnMinusEdgeControls

/-- A non-diagonal, nonzero admissible 3×3 tensor, not just a formula evaluation. -/
theorem concrete_tensor_decomposition :
    ∃ (r : ℕ) (a b : Fin r → Fin 3 → ℚ),
      (∀ k, contract ![1,-1,2] (a k) = 0) ∧
      (∀ k, contract ![1,-1,2] (b k) = 0) ∧
      ∀ i j, (![![-4,-2,1],![-2,0,1],![1,1,0]] : Fin 3 → Fin 3 → ℚ) i j =
        ∑ k, a k i * b k j := by
  apply (tensor_kernel_iff ![1,-1,2] ![1,0,0] (by norm_num [contract, Fin.sum_univ_succ]) _).mp
  constructor
  · intro j; fin_cases j <;> norm_num [Fin.sum_univ_succ]
  · intro i; fin_cases i <;> norm_num [Fin.sum_univ_succ]

/-- The split loss at d=3 is six dimensions. -/
theorem concrete_split_dimension :
    finrank ℚ (LinearMap.ker (slotEval (![1,-1,2] : Fin 3 → ℚ))) = 6 := by
  simpa using slot_kernel_dimension (![1,-1,2] : Fin 3 → ℚ) ![1,0,0]
    (by norm_num [contract, Fin.sum_univ_succ])

/-- Zero pairing does not imply the missing-pair contraction conditions. -/
theorem nonconverse_zero_test :
    (∑ i : Fin 2, ∑ j : Fin 2,
      (![![0,1],![-1,0]] : Fin 2 → Fin 2 → ℚ) i j *
        (![1,0] : Fin 2 → ℚ) i * (![1,0] : Fin 2 → ℚ) j) = 0 ∧
    ¬(∀ j : Fin 2, ∑ i : Fin 2,
      (![1,-1] : Fin 2 → ℚ) i * ((![1,0] : Fin 2 → ℚ) i * (![1,0] : Fin 2 → ℚ) j) = 0) := by
  constructor
  · apply skew_rank_one_zero
    intro i j; fin_cases i <;> fin_cases j <;> norm_num
  · intro h
    have hz := h 0
    norm_num [Fin.sum_univ_two] at hz

/-- An injection cannot be discarded from the mixed dimension theorem:
Ea=0 from a two-dimensional space and Eb=id into one dimension. -/
theorem dropping_injectivity_breaks_bound :
    (diagonalForm (fun _ : Fin 1 => (1:ℚ))).Nondegenerate ∧
    (∀ (a : Fin 2 → ℚ) (b : Fin 1 → ℚ),
      diagonalForm (fun _ : Fin 1 => (1:ℚ))
        ((0 : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 1 → ℚ)) a) b = 0) ∧
    ¬ (finrank ℚ (Fin 2 → ℚ) + finrank ℚ (Fin 1 → ℚ) ≤ finrank ℚ (Fin 1 → ℚ)) := by
  refine ⟨diagonal_nondegenerate _ (by intro i; norm_num), ?_, ?_⟩
  · intro a b; simp
  · norm_num [Module.finrank_pi]

/-- With the zero form both maps are identity injections, but 1+1>1. -/
theorem dropping_nondegeneracy_breaks_bound :
    Function.Injective (LinearMap.id : ℚ →ₗ[ℚ] ℚ) ∧
    (∀ a b : ℚ, (0 : LinearMap.BilinForm ℚ ℚ) a b = 0) ∧
    ¬ (finrank ℚ ℚ + finrank ℚ ℚ ≤ finrank ℚ ℚ) := by
  refine ⟨Function.injective_id, ?_, ?_⟩
  · intros; rfl
  · norm_num

/-- This invalid order datum has a nonzero constant invisible to ALL twisted
tests. Its failure of rectangular nondegeneracy is proved, not merely printed. -/
theorem dropping_rectangle_nondegeneracy_breaks_detector :
    let t : Fin 2 → ℚ := ![0,1]
    let w : Fin 2 → ℚ := ![1,1]
    let S : Fin 2 → Fin 2 → ℚ := ![![0,-1],![0,0]]
    (1 : MvPolynomial (Fin 2) ℚ) ≠ 0 ∧
    Rectangle 0 0 (1 : MvPolynomial (Fin 2) ℚ) ∧
    (∀ B : MvPolynomial (Fin 2) ℚ,
      orderPair t w S 1 ((MvPolynomial.X 1 - MvPolynomial.C 1)*B) = 0) ∧
    ¬ RectangularNondegenerate 0 t w S := by
  dsimp
  refine ⟨one_ne_zero, by simp [Rectangle], ?_, ?_⟩
  · intro B
    simp [orderPair, Fin.sum_univ_two]
  · intro h
    have hz := h (MvPolynomial.X 1 - MvPolynomial.C 1)
      (by simpa using rectangle_twist 0 (1:ℚ) 1 (by simp [Rectangle]))
      (by intro B hB; simp [orderPair, Fin.sum_univ_two])
    exact twist_ne_zero (1:ℚ) hz

/-- Explicit node isolation: five rational nodes, with a=0 and target i=3.
The hypothesis is exactly the family supplied by the paper's localization. -/
theorem concrete_localization (σ : Fin 5 → ℚ)
    (htests : ∀ U V : Polynomial ℚ, U.natDegree ≤ 2 → V.natDegree ≤ 1 →
      (∑ i : Fin 5, U.eval (i:ℚ) * (i:ℚ) * V.eval (i:ℚ) * σ i) = 0) : σ 3 = 0 := by
  apply localize_away 2 1 (fun i : Fin 5 => (i:ℚ)) (fun _ => 1) σ
    (by
      intro i j h
      have hn : (i.val : ℚ) = (j.val : ℚ) := h
      apply Fin.ext; exact_mod_cast hn)
    (by decide) 0 3 (by decide) (by norm_num)
  intro U V hU hV
  simpa using htests U V hU hV

/-- The small-degree obstruction is checked separately at s=2 and s=3. -/
theorem small_s2 (P : MvPolynomial (Fin 4) ℚ)
    (hP : Budget (fun _ => 0) P) (hdiv : collision ∣ P) : P = 0 :=
  small_degree_collision_zero 0 (by decide) P hP hdiv

theorem small_s3 (P : MvPolynomial (Fin 4) ℚ)
    (hP : Budget (fun _ => 1) P) (hdiv : collision ∣ P) : P = 0 :=
  small_degree_collision_zero 1 (by decide) P hP hdiv
end KnMinusEdgeControls
