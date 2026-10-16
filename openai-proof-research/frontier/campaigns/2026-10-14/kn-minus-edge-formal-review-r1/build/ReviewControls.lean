/- Copyright 2026 Myeongjin Kang. MIT. Independent semantic review controls. -/
import KnMinusEdge
open scoped BigOperators
open KnMinusEdge Module Polynomial
namespace IndependentReview

/-- One contraction really is insufficient: a column in ker phi can have a bad row. -/
theorem one_slot_is_not_both :
    let H : Fin 2 → Fin 2 → ℚ := ![![0,0],![1,0]]
    (∀ j, ∑ i : Fin 2, (![1,0] : Fin 2 → ℚ) i * H i j = 0) ∧
    ¬ (∀ i, ∑ j : Fin 2, (![1,0] : Fin 2 → ℚ) j * H i j = 0) := by
  dsimp
  constructor
  · intro j; fin_cases j <;> norm_num [Fin.sum_univ_two]
  · intro h; have := h 1; norm_num [Fin.sum_univ_two] at this

/-- Removing normalization/surjectivity changes the actual kernel dimension. -/
theorem zero_functional_dimension :
    finrank ℚ (LinearMap.ker (slotEval (fun _ : Fin 2 => (0:ℚ)))) = 4 := by
  have hz : slotEval (fun _ : Fin 2 => (0:ℚ)) = 0 := by ext H j; simp [slotEval]
  rw [hz, LinearMap.ker_zero]
  simp [Module.finrank_pi_fintype]

/-- A nonzero admissible tensor with a normalized witness different from a basis vector. -/
theorem nonbasis_witness_tensor :
    ∃ (r : ℕ) (a b : Fin r → Fin 2 → ℚ),
      (∀ k, contract ![2,3] (a k) = 0) ∧
      (∀ k, contract ![2,3] (b k) = 0) ∧
      ∀ i j, (![![9,-6],![-6,4]] : Fin 2 → Fin 2 → ℚ) i j =
        ∑ k, a k i * b k j := by
  apply (tensor_kernel_iff ![2,3] ![-1,1] (by norm_num [KnMinusEdge.contract, Fin.sum_univ_two]) _).mp
  constructor <;> intro k <;> fin_cases k <;> norm_num [Fin.sum_univ_two]

/-- Mixed orthogonality can hold while neither image is self-isotropic. -/
theorem mixed_without_self_isotropy :
    (∀ x y : ℚ, diagonalForm (![1,1] : Fin 2 → ℚ) ![x,0] ![0,y] = 0) ∧
    diagonalForm (![1,1] : Fin 2 → ℚ) ![1,0] ![1,0] ≠ 0 ∧
    diagonalForm (![1,1] : Fin 2 → ℚ) ![0,1] ![0,1] ≠ 0 := by
  simp [diagonalForm_apply, Fin.sum_univ_two]

/-- Mixed orthogonality does not force the images to have trivial intersection. -/
theorem mixed_with_same_nonzero_image :
    (diagonalForm (![1,-1] : Fin 2 → ℚ)).Nondegenerate ∧
    (∀ x y : ℚ, diagonalForm (![1,-1] : Fin 2 → ℚ) ![x,x] ![y,y] = 0) ∧
    (![1,1] : Fin 2 → ℚ) ≠ 0 := by
  refine ⟨diagonal_nondegenerate _ (by intro i; fin_cases i <;> norm_num), ?_, ?_⟩
  · intro x y; simp [diagonalForm_apply, Fin.sum_univ_two]
  · intro h; have := congrFun h 0; norm_num at this

/-- The second injection is essential too, independent of the first. -/
theorem second_injection_essential :
    Function.Injective (LinearMap.id : ℚ →ₗ[ℚ] ℚ) ∧
    (∀ (x : ℚ) (y : Fin 2 → ℚ),
      diagonalForm (fun _ : Fin 1 => (1:ℚ)) (fun _ => x)
        ((0 : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 1 → ℚ)) y) = 0) ∧
    ¬ (finrank ℚ ℚ + finrank ℚ (Fin 2 → ℚ) ≤ finrank ℚ (Fin 1 → ℚ)) := by
  refine ⟨Function.injective_id, ?_, ?_⟩
  · intros; simp
  · norm_num [Module.finrank_pi]

/-- Valid full summed tests with nonzero sigma at the excluded endpoint.
This prevents accidental extrapolation of isolation to i=a. -/
theorem excluded_endpoint_can_survive :
    (∀ U V : ℚ[X], ∑ i : Fin 3, U.eval (i:ℚ) * (i:ℚ) * V.eval (i:ℚ) *
      (Pi.single 0 1 : Fin 3 → ℚ) i = 0) ∧
    (Pi.single 0 1 : Fin 3 → ℚ) 0 ≠ 0 := by
  constructor
  · intro U V; simp [Pi.single_apply]
  · simp

/-- Nonzero sigma supported at a satisfies the hypotheses on real distinct nodes;
isolation is still valid at b and every other node, without star order data. -/
theorem localization_nontrivial_instance :
    (Pi.single 0 1 : Fin 3 → ℚ) 2 = 0 := by
  apply localize_away 1 0 (fun i : Fin 3 => (i:ℚ)) (fun _ => 1)
    (Pi.single 0 1)
    (by intro i j h; have hn : (i.val:ℚ) = (j.val:ℚ) := h; apply Fin.ext; exact_mod_cast hn)
    (by decide) 0 2 (by decide) (by norm_num)
  intro U V hU hV
  simp [Pi.single_apply]

/-- A square constant test can detect constants although all twisted tests
miss the nonzero constant 1. Thus this weaker detection cannot replace hM. -/
theorem constant_square_does_not_detect_twist :
    let t : Fin 2 → ℚ := ![0,1]
    let w : Fin 2 → ℚ := ![1,1]
    let S : Fin 2 → Fin 2 → ℚ := ![![0,-1],![0,0]]
    (∀ a : ℚ, (∀ b : ℚ, orderPair t w S (MvPolynomial.C a) (MvPolynomial.C b) = 0) → a = 0) ∧
    (∀ B : MvPolynomial (Fin 2) ℚ,
      orderPair t w S 1 ((MvPolynomial.X 1 - MvPolynomial.C 1)*B) = 0) ∧
    ¬ RectangularNondegenerate 0 t w S := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro a h; have := h 1; simpa [orderPair, Fin.sum_univ_two] using this
  · intro B; simp [orderPair, Fin.sum_univ_two]
  · intro h
    have hz := h (MvPolynomial.X 1 - MvPolynomial.C 1)
      (by simpa using rectangle_twist 0 (1:ℚ) 1 (by simp [Rectangle]))
      (by intro B hB; simp [orderPair, Fin.sum_univ_two])
    exact twist_ne_zero (1:ℚ) hz

/-- A twist can vanish at a node while a different node supplies a nonzero
pairing. No inverse of the twist on the node set exists. -/
theorem twist_root_and_detected_constant :
    MvPolynomial.eval (![0,1] : Fin 2 → ℚ)
      (MvPolynomial.X 1 - MvPolynomial.C 1) = 0 ∧
    orderPair (![0,1] : Fin 2 → ℚ) ![1,1]
      (![![0,-1],![1,0]] : Fin 2 → Fin 2 → ℚ)
      1 ((MvPolynomial.X 1 - MvPolynomial.C 1)*1) ≠ 0 := by
  norm_num [orderPair, Fin.sum_univ_two]

/-- The specialized collision factor is a nonzero polynomial, yet has zeros. -/
theorem nonzero_specialization_has_root :
    missingSpecialization (0:ℚ) 1 (collision : MvPolynomial (Fin 4) ℚ) ≠ 0 ∧
    MvPolynomial.eval (![0,2] : Fin 2 → ℚ)
      (missingSpecialization (0:ℚ) 1 collision) = 0 := by
  refine ⟨collision_specialization_ne_zero 0 1, ?_⟩
  norm_num [missingSpecialization, collision]

/-- Over a finite field, a nonzero polynomial can vanish at every point.
No core proof may silently use pointwise equality as polynomial equality. -/
theorem finite_field_pointwise_trap :
    (MvPolynomial.X 0 ^ 2 - MvPolynomial.X 0 : MvPolynomial (Fin 1) (ZMod 2)) ≠ 0 ∧
    (∀ point : Fin 1 → ZMod 2,
      MvPolynomial.eval point (MvPolynomial.X 0 ^ 2 - MvPolynomial.X 0) = 0) := by
  constructor
  · intro h
    have hc := congrArg (fun p : MvPolynomial (Fin 1) (ZMod 2) => p.coeff (Finsupp.single (0:Fin 1) 2)) h
    norm_num [MvPolynomial.X_pow_eq_monomial] at hc
  · intro point
    simp only [map_sub, map_pow, MvPolynomial.eval_X]
    generalize hz : point 0 = z
    fin_cases z <;> decide

/-- With fewer nodes/without the degree inequality, vanishing is insufficient. -/
theorem too_few_roots :
    (X*(X-1) : ℚ[X]) ≠ 0 ∧
    (X*(X-1) : ℚ[X]).eval 0 = 0 ∧ (X*(X-1) : ℚ[X]).eval 1 = 0 := by
  refine ⟨mul_ne_zero X_ne_zero (by intro h; have := congrArg (Polynomial.eval 2) h; norm_num at this), ?_, ?_⟩ <;> norm_num

/-- In natDegree/degreeOf conventions the zero polynomial has degree zero. -/
theorem zero_degree_convention :
    (0 : ℚ[X]).natDegree = 0 ∧
    (0 : MvPolynomial (Fin 4) ℚ).degreeOf 0 = 0 ∧
    Budget (fun _ => 0) (0 : MvPolynomial (Fin 4) ℚ) := by
  simp [Budget]

/-- Skew does not imply alternating in characteristic two. The explicit
CharZero restriction on skew_rank_one_zero prevents this counterexample. -/
theorem characteristic_two_skew_trap :
    (∀ i j : Fin 1, (1:ZMod 2) = -(1:ZMod 2)) ∧
    (∑ i : Fin 1, ∑ j : Fin 1, (1:ZMod 2)) ≠ 0 := by
  decide

/-- Each inserted missing-slot factor has its own job, in opposite endpoint
orders. The shared nonzero P=x+u-1 belongs to the first missing-slot kernel. -/
theorem both_local_factors_needed :
    let P : MvPolynomial (Fin 4) ℚ := MvPolynomial.X 0 + MvPolynomial.X 1 - 1
    missingSpecialization 0 1 P = 0 ∧ missingSpecialization 1 0 P = 0 ∧
    MvPolynomial.eval ![2,3,0,1] (localTest 0 P 1 1 1) = 0 ∧
    MvPolynomial.eval ![2,3,1,0] (localTest 0 P 1 1 1) = 0 ∧
    (2+3-1 : ℚ)*(3-1)*(3-0)*(1-2)*(1-0) ≠ 0 ∧
    (2+3-1 : ℚ)*(3-0)*(3-1)*(0-2)*(1-0) ≠ 0 := by
  norm_num [missingSpecialization, localTest]

end IndependentReview
