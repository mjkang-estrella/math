import VendiJensen

open Finset Matrix
namespace VendiMatrix

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma conjugate_diag (U : Matrix n n ℝ) (lam : n → ℝ) (i : n) :
    (U * Matrix.diagonal lam * Uᵀ) i i = ∑ j,lam j*(U i j)^2 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def positiveSpectrum {Z : Matrix n n ℝ} (hZ : Z.PosSemidef) : Finset n :=
  Finset.univ.filter (fun j => 0<hZ.1.eigenvalues j)

noncomputable def weights {Z : Matrix n n ℝ} (hZ : Z.PosSemidef) (i j : n) : ℝ :=
  (hZ.1.eigenvectorUnitary i j)^2

lemma spectral_form {Z : Matrix n n ℝ} (hZ : Z.PosSemidef) :
    Z = (hZ.1.eigenvectorUnitary : Matrix n n ℝ) * Matrix.diagonal hZ.1.eigenvalues *
      (hZ.1.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
  simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hZ.1.spectral_theorem

lemma unitary_transpose {Z : Matrix n n ℝ} (hZ : Z.PosSemidef) :
    (hZ.1.eigenvectorUnitary : Matrix n n ℝ)ᵀ * hZ.1.eigenvectorUnitary=1 := by
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using Unitary.coe_star_mul_self hZ.1.eigenvectorUnitary

lemma spectral_square {Z : Matrix n n ℝ} (hZ : Z.PosSemidef) :
    Z*Z=(hZ.1.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal (fun j => (hZ.1.eigenvalues j)^2) *
      (hZ.1.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
  let U : Matrix n n ℝ := hZ.1.eigenvectorUnitary
  let D := Matrix.diagonal hZ.1.eigenvalues
  have hs : Z=U*D*Uᵀ := spectral_form hZ
  have hu : Uᵀ*U=1 := unitary_transpose hZ
  calc
    Z*Z = (U*D)*(Uᵀ*U)*(D*Uᵀ) := by rw [hs]; noncomm_ring
    _ = U*(D*D)*Uᵀ := by rw [hu]; noncomm_ring
    _ = _ := by simp [D, Matrix.diagonal_mul_diagonal, pow_two, Matrix.mul_assoc, U]

lemma weights_column {Z : Matrix n n ℝ} (hZ : Z.PosSemidef) (j : n) :
    ∑ i,weights hZ i j=1 := by
  have h := congrArg (fun M : Matrix n n ℝ => M j j) (unitary_transpose hZ)
  simpa [Matrix.mul_apply, Matrix.transpose_apply, weights, pow_two] using h

lemma full_diag_frame {Z : Matrix n n ℝ} (hZ : Z.PosSemidef) (i : n) :
    ∑ j,hZ.1.eigenvalues j*weights hZ i j = Z i i := by
  have h := congrArg (fun M : Matrix n n ℝ => M i i) (spectral_form hZ)
  rw [conjugate_diag] at h
  exact h.symm

lemma full_square_frame {Z : Matrix n n ℝ} (hZ : Z.PosSemidef) (i : n) :
    ∑ j,(hZ.1.eigenvalues j)^2*weights hZ i j = (Z*Z) i i := by
  have h := congrArg (fun M : Matrix n n ℝ => M i i) (spectral_square hZ)
  rw [conjugate_diag] at h
  exact h.symm

lemma sum_support_of_zero {Z : Matrix n n ℝ} (hZ : Z.PosSemidef) (f : n → ℝ)
    (hf : ∀ j,hZ.1.eigenvalues j=0 → f j=0) :
    (∑j∈positiveSpectrum hZ,f j)=∑j,f j := by
  unfold positiveSpectrum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hp : 0<hZ.1.eigenvalues j
  · simp [hp]
  · have hz : hZ.1.eigenvalues j=0 := by
      have hn := hZ.eigenvalues_nonneg j
      linarith
    simp [hp,hf j hz]

lemma support_diag_frame {Z : Matrix n n ℝ} (hZ : Z.PosSemidef) (i : n) :
    ∑j∈positiveSpectrum hZ,hZ.1.eigenvalues j*weights hZ i j=Z i i := by
  rw [sum_support_of_zero hZ _ (by intro j hj; simp [hj])]
  exact full_diag_frame hZ i

lemma support_square_frame {Z : Matrix n n ℝ} (hZ : Z.PosSemidef) (i : n) :
    ∑j∈positiveSpectrum hZ,(hZ.1.eigenvalues j)^2*weights hZ i j=(Z*Z) i i := by
  rw [sum_support_of_zero hZ _ (by intro j hj; simp [hj])]
  exact full_square_frame hZ i

omit [DecidableEq n] in
lemma energy_le_row {Z : Matrix n n ℝ} (hZ : Z.PosSemidef)
    (hentry : ∀ i j,0≤Z i j ∧ Z i j≤1) (i : n) :
    (Z*Z) i i≤∑j,Z i j := by
  rw [Matrix.mul_apply]
  apply Finset.sum_le_sum
  intro j _
  have hsym : Z j i=Z i j := by simpa using hZ.1.apply i j
  rw [hsym]
  have h := hentry i j
  nlinarith

/-- Positive-spectrum energy bound for the actual PSD matrix, including singular matrices. -/
theorem source_spectral_energy_bound (Z : Matrix n n ℝ) (hZ : Z.PosSemidef)
    (hdiag : ∀ i,Z i i=1) (q : ℝ) (hq : q<1) :
    (∑i,((Z*Z) i i)^(q-1))≤
      ∑j∈positiveSpectrum hZ,(hZ.1.eigenvalues j)^q := by
  have h := VendiJensen.spectral_energy_bound (positiveSpectrum hZ) hZ.1.eigenvalues
    (weights hZ)
    (by intro j hj; exact (Finset.mem_filter.mp hj).2)
    (by intro i j _; exact sq_nonneg _)
    (by intro i; rw [support_diag_frame,hdiag])
    (by intro j _; exact weights_column hZ j) q hq
  simpa only [support_square_frame] using h

/-- Source trace/row-sum comparison with positive-spectrum powers at every rank. -/
theorem source_spectral_row_bound (Z : Matrix n n ℝ) (hZ : Z.PosSemidef)
    (hdiag : ∀ i,Z i i=1) (hentry : ∀ i j,0≤Z i j ∧ Z i j≤1)
    (q : ℝ) (hq : q<1) :
    (∑i,(∑j,Z i j)^(q-1))≤
      ∑j∈positiveSpectrum hZ,(hZ.1.eigenvalues j)^q := by
  apply VendiJensen.spectral_row_bound (positiveSpectrum hZ) hZ.1.eigenvalues
    (weights hZ)
    (by intro j hj; exact (Finset.mem_filter.mp hj).2)
    (by intro i j _; exact sq_nonneg _)
    (by intro i; rw [support_diag_frame,hdiag])
    (by intro j _; exact weights_column hZ j) (fun i=>∑j,Z i j) _ q hq
  intro i
  rw [support_square_frame]
  exact energy_le_row hZ hentry i

/-- The minimum-positive-eigenvalue route for the negative-infinity endpoint. -/
theorem source_min_le_row (Z : Matrix n n ℝ) (hZ : Z.PosSemidef)
    (hdiag : ∀ i,Z i i=1) (hentry : ∀ i j,0≤Z i j ∧ Z i j≤1)
    (m : ℝ) (hm : ∀ j∈positiveSpectrum hZ,m≤hZ.1.eigenvalues j) (i : n) :
    m≤∑j,Z i j := by
  have h := VendiJensen.min_le_energy (positiveSpectrum hZ) hZ.1.eigenvalues
    (weights hZ i)
    (by intro j hj; exact (Finset.mem_filter.mp hj).2)
    (by intro j _; exact sq_nonneg _)
    (by rw [support_diag_frame,hdiag]) m hm
  rw [support_square_frame] at h
  exact h.trans (energy_le_row hZ hentry i)

end VendiMatrix
