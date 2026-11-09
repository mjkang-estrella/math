import Mathlib

open Matrix
namespace WeakMajorizationCounterexample

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

def A : Mat := !![0, 0; 0, -2]
def B : Mat := !![0, 1; 1, 0]
def Q (k : ℕ) (a b : Mat) : Mat :=
  ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) • (a ^ j * b ^ (k - j))
noncomputable def R (k : ℕ) (a b : Mat) : Mat := (1 / 2 : ℂ) • (Q k a b + (Q k a b).conjTranspose)

def WeakMajorized {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  ∀ k ≤ n, ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), x i ≤
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), y i

theorem weakMajorized_sum {n : ℕ} {x y : Fin n → ℝ}
    (h : WeakMajorized x y) : ∑ i, x i ≤ ∑ i, y i := by
  simpa [WeakMajorized] using h n le_rfl

theorem trace_real_eigenvalues {n : Type*} [Fintype n] [DecidableEq n]
    {a : Matrix n n ℂ} (ha : a.IsHermitian) :
    a.trace.re = ∑ i, ha.eigenvalues₀ i := by
  have hh := ha.trace_eq_sum_eigenvalues
  have hre := congrArg Complex.re hh
  simp at hre
  rw [hre]
  unfold Matrix.IsHermitian.eigenvalues
  exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm _

theorem A_hermitian : A.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A, Matrix.conjTranspose_apply]

theorem B_hermitian : B.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [B, Matrix.conjTranspose_apply]

theorem H_fifth : (A + B) ^ 5 = !![-12, 29; 29, -70] := by
  norm_num [A, B, pow_succ, Matrix.mul_fin_two]

theorem Q_fifth : Q 5 A B = !![0, 1; 121, -122] := by
  norm_num [Q, A, B, Finset.sum_range_succ, pow_succ, Matrix.mul_fin_two, Nat.choose]

theorem R_fifth : R 5 A B = !![0, 61; 61, -122] := by
  rw [R, Q_fifth]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply]

theorem H_fifth_hermitian : ((A + B) ^ 5).IsHermitian := by
  exact (A_hermitian.add B_hermitian).pow 5

theorem R_fifth_hermitian : (R 5 A B).IsHermitian := by
  rw [R_fifth]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply]

theorem H_trace : (((A + B) ^ 5).trace).re = -82 := by
  rw [H_fifth]
  norm_num [Matrix.trace, Fin.sum_univ_two]

theorem R_trace : ((R 5 A B).trace).re = -122 := by
  rw [R_fifth]
  norm_num [Matrix.trace, Fin.sum_univ_two]

theorem source_counterexample :
    A.IsHermitian ∧ B.IsHermitian ∧ 5 ≤ (5 : ℕ) ∧
    ¬ WeakMajorized H_fifth_hermitian.eigenvalues₀ R_fifth_hermitian.eigenvalues₀ := by
  refine ⟨A_hermitian, B_hermitian, le_rfl, ?_⟩
  intro h
  have ht := weakMajorized_sum h
  rw [← trace_real_eigenvalues H_fifth_hermitian,
    ← trace_real_eigenvalues R_fifth_hermitian, H_trace, R_trace] at ht
  norm_num at ht

end WeakMajorizationCounterexample
