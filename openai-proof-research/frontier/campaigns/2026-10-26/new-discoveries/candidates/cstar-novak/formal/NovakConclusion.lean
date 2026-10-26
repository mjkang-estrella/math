import NovakWitness

open scoped Matrix.Norms.Operator ComplexOrder
open Matrix
namespace Novak
noncomputable def points : Fin 4 → M₂ := ![0,U,U+V,V]
noncomputable def inputs (i : Fin 4) (l : Fin 2) : M₂ := if l=0 then points i else 0
noncomputable def c : ℝ := Real.cos (Real.pi*Real.sqrt 15)
noncomputable def cosineTable : Matrix (Fin 4) (Fin 4) M₂ :=
  !![1,1,-1,1; 1,1,1,scalar c; -1,1,1,1; 1,scalar c,1,1]

lemma cosine_table (i j : Fin 4) :
    operatorCos (points i-points j) = cosineTable i j := by
  have h₁ : U-(U+V) = -V := by abel
  have h₂ : V-(U+V) = -U := by abel
  have h₃ : V-U = -(U-V) := by abel
  have h₄ : operatorCos (-V + -U) = -1 := by
    have he : -V + -U = -(U+V) := by abel
    rw [he, cos_neg, cos_sum]
  fin_cases i <;> fin_cases j <;>
    simp [points, cosineTable, c, cos_zero, cos_neg, cos_U, cos_V, cos_sum,
      cos_difference, h₁, h₂, h₃, h₄, -neg_sub]

noncomputable def sourceBlock (x : Fin 4 → Fin 2 → M₂) (i j : Fin 4) : M₂ :=
  ((2:ℂ)⁻¹ • (1+operatorCos (x i 0-x j 0))) *
  ((2:ℂ)⁻¹ • (1+operatorCos (x i 1-x j 1))) - scalar (1/4)
noncomputable def sourceMatrix (x : Fin 4 → Fin 2 → M₂) :
    Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) ℂ :=
  fun i j => sourceBlock x i.1 j.1 i.2 j.2

lemma source_block (i j : Fin 4) :
    sourceBlock inputs i j = (2:ℂ)⁻¹ • (1+cosineTable i j)-scalar (1/4) := by
  simp only [sourceBlock, inputs, ite_true, show ¬((1:Fin 2)=0) by decide,
    ite_false, sub_self, cos_zero, cosine_table]
  have h : (2:ℂ)⁻¹ • (1+(1:M₂)) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.ofNat_apply]
  rw [h, mul_one]

noncomputable def signs : Fin 4 → ℂ := ![1,-1,1,-1]
noncomputable def witness (i : Fin 4 × Fin 2) : ℂ := if i.2=0 then signs i.1 else 0

lemma quadratic_form : star witness ⬝ᵥ (sourceMatrix inputs *ᵥ witness) = (c-3:ℝ) := by
  simp [dotProduct, Matrix.mulVec, sourceMatrix, source_block, witness, signs,
    Fintype.sum_prod_type, Fin.sum_univ_succ, cosineTable, scalar]
  ring

lemma not_posSemidef : ¬ (sourceMatrix inputs).PosSemidef := by
  intro h
  have hh := h.dotProduct_mulVec_nonneg witness
  rw [quadratic_form] at hh
  have hh' : (0:ℝ) ≤ c-3 := by exact_mod_cast hh
  have hc : c ≤ 1 := Real.cos_le_one _
  linarith

lemma inputs_selfAdjoint (i : Fin 4) (l : Fin 2) : (inputs i l).IsHermitian := by
  fin_cases i <;> fin_cases l <;>
    simp [inputs, points, U, V, plane_selfAdjoint, Matrix.IsHermitian.add]

lemma source_hermitian : (sourceMatrix inputs).IsHermitian := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.conjTranspose_apply, sourceMatrix, source_block, cosineTable,
      scalar]

theorem source_counterexample_351633 :
    (∀ i l, (inputs i l).IsHermitian) ∧
    (sourceMatrix inputs).IsHermitian ∧ ¬ (sourceMatrix inputs).PosSemidef :=
  ⟨inputs_selfAdjoint, source_hermitian, not_posSemidef⟩
end Novak
