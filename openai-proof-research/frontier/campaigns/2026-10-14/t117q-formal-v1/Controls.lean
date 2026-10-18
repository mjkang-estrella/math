import T117Q

/- Original hypothesis controls: Myeongjin Kang, MIT. -/
open scoped MatrixOrder ComplexOrder
open Matrix
namespace T117QControls

noncomputable def p : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
noncomputable def r : Matrix (Fin 2) (Fin 2) ℂ := !![1/2, 1/2; 1/2, 1/2]

theorem p_selfadjoint : pᴴ = p := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [p, Matrix.conjTranspose_apply]

theorem r_selfadjoint : rᴴ = r := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [r, Matrix.conjTranspose_apply]

theorem p_idempotent : p * p = p := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [p, Matrix.mul_apply, Fin.sum_univ_two]

theorem r_idempotent : r * r = r := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [r, Matrix.mul_apply, Fin.sum_univ_two]

theorem p_positive : 0 ≤ p := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self p).nonneg
  simpa only [p_selfadjoint, p_idempotent] using h

theorem r_positive : 0 ≤ r := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self r).nonneg
  simpa only [r_selfadjoint, r_idempotent] using h

theorem projections_need_not_commute : p * r ≠ r * p := by
  intro h
  have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) h
  norm_num [p, r, Matrix.mul_apply, Fin.sum_univ_two] at he

theorem noncommuting_positive_pairing : 0 ≤ T117Q.realTrace (p * r) :=
  T117Q.trace_product_nonneg p_positive r_positive

theorem positive_trace_hypothesis_necessary :
    ¬ (∀ Y A B : Matrix (Fin 1) (Fin 1) ℂ,
      A ≤ B → T117Q.realTrace (Y * A) ≤ T117Q.realTrace (Y * B)) := by
  intro h
  have ht := h (-1) 0 1 (by exact zero_le_one)
  norm_num [T117Q.realTrace, Matrix.trace, Fin.sum_univ_succ] at ht

theorem positive_threshold_necessary :
    ∃ Q P : Matrix (Fin 1) (Fin 1) ℂ,
      0 ≤ Q ∧ (0 : ℝ) • (1 - P) ≤ Q ∧
      Q ≤ (0 : ℝ) • (1 - (1/2 : ℝ) • 1) ∧ ¬ (1/2 : ℝ) • 1 ≤ P := by
  refine ⟨0, 0, le_rfl, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro h
    have hd := (sub_nonneg.mpr h).posSemidef.diag_nonneg (i := 0)
    have hr := (RCLike.nonneg_iff.mp hd).1
    norm_num [Matrix.smul_apply] at hr

theorem nonempty_family_necessary :
    ¬ (∀ b : ℝ, (∀ i ∈ (∅ : Finset ℕ), (0 : ℝ) ≤ b) → (1 : ℝ) ≤ 2 * b) := by
  intro h
  have ht := h 0 (by simp)
  norm_num at ht


theorem cutoff_keeps_threshold {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (h : ℝ) : T117Q.cutoff U (fun _ => h) h = 1 := by
  unfold T117Q.cutoff
  simp only [le_refl, ite_true]
  exact T117Q.model_one U

theorem cutoff_discards_strictly_above {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) {h a : ℝ} (ha : h < a) :
    T117Q.cutoff U (fun _ => a) h = 0 := by
  unfold T117Q.cutoff
  simp only [not_le.mpr ha, ite_false]
  exact T117Q.model_zero U

end T117QControls
