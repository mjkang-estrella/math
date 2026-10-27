import Cubic

namespace CStarSendov

open scoped ComplexOrder
open Polynomial

abbrev Time := Set.Icc (0 : ℝ) 1
def timeZero : Time := ⟨0, by constructor <;> norm_num⟩
def timeOne : Time := ⟨1, by constructor <;> norm_num⟩
instance : Nonempty Time := ⟨timeZero⟩
abbrev FunctionAlgebra := C(Time, ℂ)

noncomputable def rootOneMap : FunctionAlgebra :=
  ⟨fun t => rootOne t, continuous_const⟩
noncomputable def rootPlusMap : FunctionAlgebra :=
  ⟨fun t => rootPlus t, rootPlus_continuous.comp continuous_subtype_val⟩
noncomputable def rootMinusMap : FunctionAlgebra :=
  ⟨fun t => rootMinus t, rootMinus_continuous.comp continuous_subtype_val⟩
noncomputable def criticalPlusMap : FunctionAlgebra :=
  ⟨fun t => criticalPlus t, criticalPlus_continuous.comp continuous_subtype_val⟩
noncomputable def criticalMinusMap : FunctionAlgebra :=
  ⟨fun t => criticalMinus t, criticalMinus_continuous.comp continuous_subtype_val⟩

noncomputable def roots : Fin 3 → FunctionAlgebra :=
  ![rootOneMap, rootPlusMap, rootMinusMap]
noncomputable def criticals : Fin 2 → FunctionAlgebra :=
  ![criticalPlusMap, criticalMinusMap]

noncomputable def sourceValue (z : FunctionAlgebra) : FunctionAlgebra :=
  (z - roots 0) * (z - roots 1) * (z - roots 2)

noncomputable def sourceDeleted (z : FunctionAlgebra) : FunctionAlgebra :=
  (z - roots 1) * (z - roots 2) + (z - roots 0) * (z - roots 2) +
    (z - roots 0) * (z - roots 1)

noncomputable def sourcePolynomial : Polynomial FunctionAlgebra :=
  (X - C (roots 0)) * (X - C (roots 1)) * (X - C (roots 2))

theorem sourcePolynomial_monic : sourcePolynomial.Monic := by
  exact ((monic_X_sub_C _).mul (monic_X_sub_C _)).mul (monic_X_sub_C _)

theorem sourcePolynomial_degree : sourcePolynomial.natDegree = 3 := by
  unfold sourcePolynomial
  rw [((monic_X_sub_C _).mul (monic_X_sub_C _)).natDegree_mul (monic_X_sub_C _),
    (monic_X_sub_C _).natDegree_mul (monic_X_sub_C _)]
  simp

theorem sourcePolynomial_eval (z : FunctionAlgebra) :
    sourcePolynomial.eval z = sourceValue z := by
  simp [sourcePolynomial, sourceValue]

theorem sourcePolynomial_derivative_eval (z : FunctionAlgebra) :
    sourcePolynomial.derivative.eval z = sourceDeleted z := by
  simp [sourcePolynomial, sourceDeleted, derivative_mul]
  ring

theorem sourceDeleted_apply (z : FunctionAlgebra) (t : Time) :
    sourceDeleted z t = cubicDeleted t (z t) := by
  rfl

theorem sourceDeleted_factorization (z : FunctionAlgebra) :
    sourceDeleted z = 3 * (z - criticalPlusMap) * (z - criticalMinusMap) := by
  ext t
  exact cubicDeleted_factorization t (z t)

theorem sourcePolynomial_derivative_split :
    sourcePolynomial.derivative = C 3 * (X - C criticalPlusMap) *
      (X - C criticalMinusMap) := by
  apply Polynomial.ext
  intro n
  apply ContinuousMap.ext
  intro t
  let ev : FunctionAlgebra →+* ℂ := (ContinuousMap.evalAlgHom ℂ ℂ t).toRingHom
  have hm : sourcePolynomial.derivative.map ev =
      (C 3 * (X - C criticalPlusMap) * (X - C criticalMinusMap)).map ev := by
    rw [← Polynomial.derivative_map]
    simp only [sourcePolynomial, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C]
    exact scalar_polynomial_split (t : ℝ)
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff n) hm
  simp only [Polynomial.coeff_map] at hc
  exact hc

theorem sourceDeleted_plus : sourceDeleted criticalPlusMap = 0 := by
  ext t
  exact criticalPlus_zero t

theorem sourceDeleted_minus : sourceDeleted criticalMinusMap = 0 := by
  ext t
  exact criticalMinus_zero t

def sourceClosedDisc (a : FunctionAlgebra) (r : ℝ) (z : FunctionAlgebra) : Prop :=
  (z - a) * star (z - a) ≤ Real.sqrt r • (1 : FunctionAlgebra)

def sourceUnitDisc (a z : FunctionAlgebra) : Prop := (z - a) * star (z - a) ≤ 1

theorem sourceUnitDisc_eq_radius_one (a z : FunctionAlgebra) :
    sourceUnitDisc a z ↔ sourceClosedDisc a 1 z := by
  simp [sourceClosedDisc, sourceUnitDisc]

theorem sourceUnitDisc_iff (a z : FunctionAlgebra) :
    sourceUnitDisc a z ↔ ∀ t : Time, ‖z t - a t‖ ≤ 1 := by
  unfold sourceUnitDisc
  rw [ContinuousMap.le_def]
  constructor
  · intro h t
    have ht := h t
    change (z t - a t) * (starRingEnd ℂ) (z t - a t) ≤ (1 : ℂ) at ht
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at ht
    have hs : ‖z t - a t‖ ^ 2 ≤ 1 := Complex.real_le_real.mp ht
    nlinarith [norm_nonneg (z t - a t)]
  · intro h t
    change (z t - a t) * (starRingEnd ℂ) (z t - a t) ≤ (1 : ℂ)
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    apply Complex.real_le_real.mpr
    nlinarith [h t, norm_nonneg (z t - a t)]

theorem roots_norm_le (i : Fin 3) : ‖roots i‖ ≤ (9 : ℝ) / 10 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro t
  fin_cases i
  · exact le_of_eq (rootOne_norm t)
  · change ‖rootPlus t‖ ≤ (9 : ℝ) / 10
    rw [rootPlus_norm]
    norm_num
  · change ‖rootMinus t‖ ≤ (9 : ℝ) / 10
    rw [rootMinus_norm]
    norm_num

theorem criticals_norm_le (i : Fin 2) : ‖criticals i‖ ≤ (9 : ℝ) / 10 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro t
  fin_cases i
  · exact (criticalPlus_norm_lt t).le
  · exact (criticalMinus_norm_lt t).le

theorem criticals_norm_lt (i : Fin 2) : ‖criticals i‖ < (9 : ℝ) / 10 := by
  have hn : ‖criticals i‖ ≤ (33 : ℝ) / 40 := by
    apply (ContinuousMap.norm_le _ (by norm_num)).mpr
    intro t
    have hq : ‖branch t‖ ≤ (7 : ℝ) / 4 := by
      nlinarith [branch_norm_sq_bound t, norm_nonneg (branch t)]
    fin_cases i
    · change ‖(3/10:ℂ) * (1 + branch t)‖ ≤ (33:ℝ)/40
      have h := norm_add_le (1:ℂ) (branch t)
      norm_num [norm_mul] at h ⊢
      linarith
    · change ‖(3/10:ℂ) * (1 - branch t)‖ ≤ (33:ℝ)/40
      have h := norm_sub_le (1:ℂ) (branch t)
      norm_num [norm_mul] at h ⊢
      linarith
  linarith

theorem roots_in_source_disc (i : Fin 3) : sourceUnitDisc 0 (roots i) := by
  apply (sourceUnitDisc_iff _ _).mpr
  intro t
  simp only [ContinuousMap.zero_apply, sub_zero]
  have h := (ContinuousMap.norm_le _ (by norm_num : (0:ℝ) ≤ 9/10)).mp (roots_norm_le i) t
  linarith

theorem criticals_in_source_disc (i : Fin 2) : sourceUnitDisc 0 (criticals i) := by
  apply (sourceUnitDisc_iff _ _).mpr
  intro t
  simp only [ContinuousMap.zero_apply, sub_zero]
  have h := (ContinuousMap.norm_le _ (by norm_num : (0:ℝ) ≤ 9/10)).mp (criticals_norm_le i) t
  linarith

theorem criticals_are_zeros (i : Fin 2) : sourceDeleted (criticals i) = 0 := by
  fin_cases i
  · exact sourceDeleted_plus
  · exact sourceDeleted_minus

theorem sourceValue_roots (i : Fin 3) : sourceValue (roots i) = 0 := by
  fin_cases i <;> simp [sourceValue]

theorem roots_pointwise_injective (t : Time) :
    Function.Injective (fun i : Fin 3 => roots i t) := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals simp only [roots, rootOneMap, rootPlusMap, rootMinusMap] at h
  all_goals first | rfl | exact False.elim ((rootPlus_ne_rootOne t) h) |
    exact False.elim ((rootMinus_ne_rootOne t) h) |
    exact False.elim ((rootPlus_ne_rootMinus t) h) |
    exact False.elim ((rootPlus_ne_rootOne t) h.symm) |
    exact False.elim ((rootMinus_ne_rootOne t) h.symm) |
    exact False.elim ((rootPlus_ne_rootMinus t) h.symm)

theorem criticals_pointwise_injective (t : Time) :
    Function.Injective (fun i : Fin 2 => criticals i t) := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals simp only [criticals, criticalPlusMap, criticalMinusMap] at h
  all_goals first | rfl | exact False.elim ((critical_branches_ne t) h) |
    exact False.elim ((critical_branches_ne t) h.symm)

theorem minus_sup_distance_gt : (21 : ℝ)/20 < ‖roots 0 - criticalMinusMap‖ := by
  have h : ‖rootOne 0 - criticalMinus 0‖ ≤ ‖roots 0 - criticalMinusMap‖ := by
    exact ContinuousMap.norm_coe_le_norm (roots 0 - criticalMinusMap) timeZero
  linarith [bad_minus_endpoint]

theorem plus_sup_distance_gt : (21 : ℝ)/20 < ‖roots 0 - criticalPlusMap‖ := by
  have h : ‖rootOne 1 - criticalPlus 1‖ ≤ ‖roots 0 - criticalPlusMap‖ := by
    exact ContinuousMap.norm_coe_le_norm (roots 0 - criticalPlusMap) timeOne
  linarith [bad_plus_endpoint]

theorem minus_fails_source_disc : ¬ sourceUnitDisc (roots 0) criticalMinusMap := by
  intro h
  have ht := (sourceUnitDisc_iff _ _).mp h timeZero
  change ‖criticalMinus 0 - rootOne 0‖ ≤ 1 at ht
  rw [norm_sub_rev] at ht
  linarith [bad_minus_endpoint]

theorem plus_fails_source_disc : ¬ sourceUnitDisc (roots 0) criticalPlusMap := by
  intro h
  have ht := (sourceUnitDisc_iff _ _).mp h timeOne
  change ‖criticalPlus 1 - rootOne 1‖ ≤ 1 at ht
  rw [norm_sub_rev] at ht
  linarith [bad_plus_endpoint]

end CStarSendov
