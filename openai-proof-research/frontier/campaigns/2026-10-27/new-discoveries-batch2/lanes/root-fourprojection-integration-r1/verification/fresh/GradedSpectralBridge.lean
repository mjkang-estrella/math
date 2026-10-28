import PolarFrameBridge
import HSBridge
import SpectralCore
import ContractiveBridge

open Matrix Unitary
open scoped BigOperators ComplexOrder
namespace FourProjection
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Coordinates in the independently chosen spectral bases of A and B. -/
noncomputable def spectralCoords {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (K : Matrix I J ℂ) : Matrix I J ℂ :=
  star (hA.eigenvectorUnitary : Matrix I I ℂ) * K *
    (hB.eigenvectorUnitary : Matrix J J ℂ)

 theorem cfc_sqrt_one_add {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    cfc Real.sqrt (1 + A) = cfc (fun t : ℝ => Real.sqrt (1 + t)) A := by
  rw [cfc_comp' Real.sqrt (fun t : ℝ => 1 + t) A (ha := hA.isSelfAdjoint)]
  congr 1
  rw [cfc_const_add 1 (fun t : ℝ => t) A (ha := hA.isSelfAdjoint),
    cfc_id' ℝ A hA.isSelfAdjoint]
  simp

 theorem cfc_sqrt_one_sub {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    cfc Real.sqrt (1 - A) = cfc (fun t : ℝ => Real.sqrt (1 - t)) A := by
  rw [cfc_comp' Real.sqrt (fun t : ℝ => 1 - t) A (ha := hA.isSelfAdjoint)]
  congr 1
  rw [cfc_sub (fun _ : ℝ => 1) (fun t : ℝ => t) A,
    cfc_const_one ℝ A hA.isSelfAdjoint, cfc_id' ℝ A hA.isSelfAdjoint]

/-- Arbitrary two-sided functional calculus becomes multiplication by scalar weights. -/
theorem spectralCoords_cfc_mul {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (K : Matrix I J ℂ)
    (f g : ℝ → ℝ) (i : I) (j : J) :
    spectralCoords hA hB (cfc f A * K * cfc g B) i j =
      (f (hA.eigenvalues i) : ℂ) * spectralCoords hA hB K i j *
        (g (hB.eigenvalues j) : ℂ) := by
  have hv := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hw := Unitary.coe_star_mul_self hB.eigenvectorUnitary
  rw [hA.cfc_eq, hB.cfc_eq]
  simp only [spectralCoords, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.mul_assoc, ← Matrix.mul_assoc (star (hA.eigenvectorUnitary : Matrix I I ℂ))
      (hA.eigenvectorUnitary : Matrix I I ℂ), hv, Matrix.one_mul,
    hw, Matrix.mul_one]
  simp only [← Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Function.comp_def, RCLike.ofReal_eq_complex_ofReal]
  ring

/-- Grading transports the genuine CFC square root of 1+A to that of 1-A. -/
theorem sqrt_grading {A : Matrix I I ℂ} (hA : A.IsHermitian)
    (G : Matrix I I ℂ) (hG : G * G = 1) (hanti : G * A * G = -A) :
    G * cfc Real.sqrt (1 + A) * G = cfc Real.sqrt (1 - A) := by
  have he : (1 - A) * G = G * (1 + A) := by
    have ha := congrArg (fun X : Matrix I I ℂ => X * G) hanti
    simp only [Matrix.mul_assoc, hG, Matrix.mul_one, Matrix.neg_mul] at ha
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]
    rw [ha]
    abel
  have hf := hermitian_cfc_intertwine (isHermitian_one.sub hA)
    (isHermitian_one.add hA) G he Real.sqrt
  have hf' := congrArg (fun X : Matrix I I ℂ => X * G) hf
  simpa only [Matrix.mul_assoc, hG, Matrix.mul_one] using hf'.symm

/-- The matrix equation yields the scalar equation in two independent spectral bases. -/
theorem spectral_entry_relation {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (K L : Matrix I J ℂ)
    (hrel : cfc Real.sqrt (1 + A) * K * cfc Real.sqrt (1 + B) +
      cfc Real.sqrt (1 - A) * L * cfc Real.sqrt (1 - B) = 0) (i : I) (j : J) :
    ((Real.sqrt (1 + hA.eigenvalues i) * Real.sqrt (1 + hB.eigenvalues j) : ℝ) : ℂ) *
        spectralCoords hA hB K i j +
    ((Real.sqrt (1 - hA.eigenvalues i) * Real.sqrt (1 - hB.eigenvalues j) : ℝ) : ℂ) *
        spectralCoords hA hB L i j = 0 := by
  have he := congrArg (fun M : Matrix I J ℂ => spectralCoords hA hB M i j) hrel
  rw [cfc_sqrt_one_add hA, cfc_sqrt_one_add hB,
    cfc_sqrt_one_sub hA, cfc_sqrt_one_sub hB] at he
  have hadd (M N : Matrix I J ℂ) :
      spectralCoords hA hB (M + N) = spectralCoords hA hB M + spectralCoords hA hB N := by
    simp [spectralCoords, Matrix.mul_add, Matrix.add_mul]
  rw [hadd, Matrix.add_apply, spectralCoords_cfc_mul, spectralCoords_cfc_mul] at he
  simp only [spectralCoords, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply] at he
  simp only [Complex.ofReal_mul]
  dsimp only [spectralCoords]
  linear_combination he

/-- Strict spectral bounds are obtained from the actual matrix spectrum. -/
theorem spectral_bounds {A : Matrix I I ℂ} (hA : A.IsHermitian)
    (hsp : ∀ t ∈ spectrum ℝ A, -1 < t ∧ t < 1) (i : I) :
    -1 < hA.eigenvalues i ∧ hA.eigenvalues i < 1 ∧ hA.eigenvalues i ^ 2 < 1 := by
  obtain ⟨hl, hu⟩ := hsp _ (hA.eigenvalues_mem_spectrum_real i)
  have hp : 0 < (1 + hA.eigenvalues i) * (1 - hA.eigenvalues i) :=
    mul_pos (by linarith) (by linarith)
  exact ⟨hl, hu, by nlinarith⟩

/-- Spectral coordinates preserve the actual Hilbert--Schmidt square. -/
theorem hsSq_spectralCoords {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (K : Matrix I J ℂ) :
    hsSq (spectralCoords hA hB K) = hsSq K := by
  unfold spectralCoords
  rw [hsSq_mul_coisometry _ _ (coe_mul_star_self hB.eigenvectorUnitary)]
  apply hsSq_isometry_mul
  simpa only [← star_eq_conjTranspose, star_star, Unitary.coe_star] using
    coe_mul_star_self hA.eigenvectorUnitary

 theorem spectralCoords_add {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (K L : Matrix I J ℂ) :
    spectralCoords hA hB (K + L) = spectralCoords hA hB K + spectralCoords hA hB L := by
  simp [spectralCoords, Matrix.mul_add, Matrix.add_mul]

/-- Trace of the square in the actual spectral basis, with no assumed eigenvalue array. -/
theorem trace_square_eq_spectral_sum {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    (trace (A * A)).re = ∑ i, hA.eigenvalues i ^ 2 := by
  let P : Matrix I I ℂ := hA.eigenvectorUnitary
  let D : Matrix I I ℂ := diagonal (fun i => (hA.eigenvalues i : ℂ))
  have hp : star P * P = 1 := coe_star_mul_self hA.eigenvectorUnitary
  have ha : A = P * D * star P := hA.spectral_theorem
  have he : A * A = P * (D * D) * star P := by
    rw [ha]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (star P) P, hp, Matrix.one_mul]
  rw [he, Matrix.mul_assoc, trace_mul_comm P, Matrix.mul_assoc (D * D), hp, Matrix.mul_one]
  simp [D, diagonal_mul_diagonal, trace_diagonal, pow_two]

/-- Genuine Hermitian-matrix endpoint. The input is the CFC matrix equation and
positive-semidefinite Gram complements, not spectral arrays or row bounds. -/
theorem hermitian_spectral_bound {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAsp : ∀ t ∈ spectrum ℝ A, -1 < t ∧ t < 1)
    (hBsp : ∀ t ∈ spectrum ℝ B, -1 < t ∧ t < 1)
    (K L : Matrix I J ℂ) (hK : GramContractive K) (hL : GramContractive L)
    (hrel : cfc Real.sqrt (1 + A) * K * cfc Real.sqrt (1 + B) +
      cfc Real.sqrt (1 - A) * L * cfc Real.sqrt (1 - B) = 0) :
    hsSq (K + L) / 4 ≤ (trace (A * A) + trace (B * B)).re / 2 := by
  let a := hA.eigenvalues
  let b := hB.eigenvalues
  let k := spectralCoords hA hB K
  let l := spectralCoords hA hB L
  let u := fun i j => Real.sqrt (1 + a i) * Real.sqrt (1 + b j)
  let v := fun i j => Real.sqrt (1 - a i) * Real.sqrt (1 - b j)
  have ha (i : I) := spectral_bounds hA hAsp i
  have hb (j : J) := spectral_bounds hB hBsp j
  have hk : GramContractive k := hK.unitary_change hA.eigenvectorUnitary hB.eigenvectorUnitary
  have hl : GramContractive l := hL.unitary_change hA.eigenvectorUnitary hB.eigenvectorUnitary
  have hu (i : I) (j : J) : u i j ^ 2 = (1 + a i) * (1 + b j) := by
    dsimp [u]
    rw [mul_pow, Real.sq_sqrt (by dsimp [a]; linarith [ha i]),
      Real.sq_sqrt (by dsimp [b]; linarith [hb j])]
  have hv (i : I) (j : J) : v i j ^ 2 = (1 - a i) * (1 - b j) := by
    dsimp [v]
    rw [mul_pow, Real.sq_sqrt (by dsimp [a]; linarith [ha i]),
      Real.sq_sqrt (by dsimp [b]; linarith [hb j])]
  have h := spectral_core a b k l u v (fun i => (ha i).2.2) (fun j => (hb j).2.2)
    (fun i j => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (fun i j => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hu hv
    (spectral_entry_relation hA hB K L hrel)
    (row_bound_of_gramContractive hk) (col_bound_of_gramContractive hk)
    (row_bound_of_gramContractive hl) (col_bound_of_gramContractive hl)
  have he : (∑ i, ∑ j, Complex.normSq (k i j + l i j)) = hsSq (K + L) := by
    change hsSq (spectralCoords hA hB K + spectralCoords hA hB L) = _
    rw [← spectralCoords_add, hsSq_spectralCoords]
  rw [he] at h
  simpa only [Complex.add_re, trace_square_eq_spectral_sum hA,
    trace_square_eq_spectral_sum hB] using h

/-- Unitary gradings need no extra contraction premise for the graded copy. -/
theorem graded_spectral_bound {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAsp : ∀ t ∈ spectrum ℝ A, -1 < t ∧ t < 1)
    (hBsp : ∀ t ∈ spectrum ℝ B, -1 < t ∧ t < 1)
    (G : unitary (Matrix I I ℂ)) (H : unitary (Matrix J J ℂ))
    (K : Matrix I J ℂ) (hK : GramContractive K)
    (hrel : cfc Real.sqrt (1 + A) * K * cfc Real.sqrt (1 + B) +
      cfc Real.sqrt (1 - A) * ((G : Matrix I I ℂ) * K * (H : Matrix J J ℂ)) *
        cfc Real.sqrt (1 - B) = 0) :
    hsSq (K + (G : Matrix I I ℂ) * K * (H : Matrix J J ℂ)) / 4 ≤
      (trace (A * A) + trace (B * B)).re / 2 := by
  apply hermitian_spectral_bound hA hB hAsp hBsp K _ hK _ hrel
  simpa only [Unitary.coe_star, star_star] using hK.unitary_change (star G) H

end FourProjection
