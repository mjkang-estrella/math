import Mathlib

open Matrix Polynomial
namespace SymplecticOrbitCounterexample
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

abbrev Mat := Matrix (Fin 6) (Fin 6) ℝ

def J : Mat :=
  !![0,1,0,0,0,0; -1,0,0,0,0,0; 0,0,0,1,0,0;
     0,0,-1,0,0,0; 0,0,0,0,0,1; 0,0,0,0,-1,0]
def A0 : Mat :=
  !![0,1,0,0,0,0; -1,0,0,0,0,0; 0,0,0,1,0,0;
     0,0,-1,0,0,0; 0,0,0,0,0,2; 0,0,0,0,-2,0]
def A1 : Mat :=
  !![0,1,0,0,0,0; -1,0,-1,0,0,0; 0,1,0,1,0,0;
     0,0,-1,0,0,0; 0,0,0,0,0,2; 0,0,0,0,-2,0]

def K0 : Mat := -J * A0
def K1 : Mat := -J * A1

def IsSymplectic (P : Mat) : Prop := P.transpose * J * P = J
def Equivalent (M N : Mat) : Prop := ∃ P : Mat, IsSymplectic P ∧ N = P.transpose * M * P

theorem J_squared : J * J = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [J, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem A0_skew : A0.transpose = -A0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A0]
theorem A1_skew : A1.transpose = -A1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A1]

def inverse0 : Mat :=
  !![0,-1,0,0,0,0; 1,0,0,0,0,0; 0,0,0,-1,0,0;
     0,0,1,0,0,0; 0,0,0,0,0,-(1/2); 0,0,0,0,1/2,0]
def inverse1 : Mat :=
  !![0,-1,0,1,0,0; 1,0,0,0,0,0; 0,0,0,-1,0,0;
     -1,0,1,0,0,0; 0,0,0,0,0,-(1/2); 0,0,0,0,1/2,0]

theorem A0_inverse : A0 * inverse0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A0, inverse0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
theorem A1_inverse : A1 * inverse1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A1, inverse1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem A0_nonsingular : A0.det ≠ 0 := by
  have h := congrArg Matrix.det A0_inverse
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact left_ne_zero_of_mul_eq_one h

theorem A1_nonsingular : A1.det ≠ 0 := by
  have h := congrArg Matrix.det A1_inverse
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact left_ne_zero_of_mul_eq_one h

theorem A0_nonscalar : ∀ c : ℝ, A0 ≠ c • J := by
  intro c h
  have h0 := congrArg (fun a : Mat => a 0 1) h
  have h4 := congrArg (fun a : Mat => a 4 5) h
  norm_num [A0,J] at h0 h4
  linarith

theorem A1_nonscalar : ∀ c : ℝ, A1 ≠ c • J := by
  intro c h
  have h1 := congrArg (fun a : Mat => a 1 2) h
  norm_num [A1,J] at h1

theorem K0_quadratic : (K0 - 1) * (K0 - (2 : ℝ) • 1) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [K0, J, A0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem K1_not_quadratic : (K1 - 1) * (K1 - (2 : ℝ) • 1) ≠ 0 := by
  intro h
  have he := congrArg (fun a : Mat => a 0 2) h
  norm_num [K1, J, A1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] at he

theorem no_congruence : ¬ Equivalent A0 A1 := by
  rintro ⟨P, hP, hA⟩
  let L : Mat := -J * P.transpose * J
  have hLP : L * P = 1 := by
    dsimp [L]
    calc
      -J * P.transpose * J * P = -J * (P.transpose * J * P) := by noncomm_ring
      _ = -J * J := by rw [hP]
      _ = 1 := by rw [neg_mul, J_squared]; simp
  have hPL : P * L = 1 := mul_eq_one_comm.mp hLP
  have hK : L * K0 * P = K1 := by
    dsimp [L, K0, K1]
    calc
      -J * P.transpose * J * (-J * A0) * P = -J * P.transpose * (J * -J) * A0 * P := by noncomm_ring
      _ = -J * (P.transpose * A0 * P) := by rw [mul_neg, J_squared]; simp [mul_assoc]
      _ = -J * A1 := by rw [← hA]
  have hfactor1 : K1 - 1 = L * (K0 - 1) * P := by
    rw [mul_sub, sub_mul, hK, mul_one, hLP]
  have hfactor2 : K1 - (2 : ℝ) • 1 = L * (K0 - (2 : ℝ) • 1) * P := by
    rw [mul_sub, sub_mul, hK, mul_smul_comm, mul_one, smul_mul_assoc, hLP]
  apply K1_not_quadratic
  rw [hfactor1, hfactor2]
  calc
    L * (K0 - 1) * P * (L * (K0 - (2 : ℝ) • 1) * P) =
        L * (K0 - 1) * (P * L) * (K0 - (2 : ℝ) • 1) * P := by noncomm_ring
    _ = L * ((K0 - 1) * (K0 - (2 : ℝ) • 1)) * P := by rw [hPL]; simp [mul_assoc]
    _ = 0 := by rw [K0_quadratic]; simp

def sourcePf {R : Type*} [CommRing R] (m : ℕ)
    (M : Matrix (Fin (2*m)) (Fin (2*m)) R) : R :=
  ∑ σ : Equiv.Perm (Fin (2*m)), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) *
    ∏ i : Fin m, M (σ ⟨2*i.val, by omega⟩) (σ ⟨2*i.val+1, by omega⟩)

def keep01 : Fin 4 → Fin 6 := ![0,1,2,3]
def keep02 : Fin 4 → Fin 6 := ![0,1,4,5]
def keep12 : Fin 4 → Fin 6 := ![2,3,4,5]
def pair0 : Fin 2 → Fin 6 := ![0,1]
def pair1 : Fin 2 → Fin 6 := ![2,3]
def pair2 : Fin 2 → Fin 6 := ![4,5]

def rawInvariant {R : Type*} [CommRing R]
    (M : Matrix (Fin 6) (Fin 6) R) (k : Fin 3) : R :=
  if k = 0 then sourcePf 3 M
  else if k = 1 then sourcePf 2 (M.submatrix keep01 keep01) +
    sourcePf 2 (M.submatrix keep02 keep02) + sourcePf 2 (M.submatrix keep12 keep12)
  else sourcePf 1 (M.submatrix pair0 pair0) +
    sourcePf 1 (M.submatrix pair1 pair1) + sourcePf 1 (M.submatrix pair2 pair2)

def pfaffian (m : ℕ) (M : Matrix (Fin (2*m)) (Fin (2*m)) ℝ) : ℝ :=
  sourcePf m M / ((2 ^ m * m.factorial : ℕ) : ℝ)

def invariant (M : Mat) (k : Fin 3) : ℝ :=
  rawInvariant M k / ((2 ^ (3-k.val) * (3-k.val).factorial : ℕ) : ℝ)

theorem invariant_zero (M : Mat) : invariant M 0 = pfaffian 3 M := by
  norm_num [invariant, rawInvariant, pfaffian]

theorem invariant_one (M : Mat) : invariant M 1 =
    pfaffian 2 (M.submatrix keep01 keep01) + pfaffian 2 (M.submatrix keep02 keep02) +
      pfaffian 2 (M.submatrix keep12 keep12) := by
  norm_num [invariant, rawInvariant, pfaffian]
  ring

theorem invariant_two (M : Mat) : invariant M 2 =
    pfaffian 1 (M.submatrix pair0 pair0) + pfaffian 1 (M.submatrix pair1 pair1) +
      pfaffian 1 (M.submatrix pair2 pair2) := by
  norm_num [invariant, rawInvariant, pfaffian]
  ring

def A0Z : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0,1,0,0,0,0; -1,0,0,0,0,0; 0,0,0,1,0,0;
     0,0,-1,0,0,0; 0,0,0,0,0,2; 0,0,0,0,-2,0]
def A1Z : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0,1,0,0,0,0; -1,0,-1,0,0,0; 0,1,0,1,0,0;
     0,0,-1,0,0,0; 0,0,0,0,0,2; 0,0,0,0,-2,0]

theorem sourcePf_cast (m : ℕ) (M : Matrix (Fin (2*m)) (Fin (2*m)) ℤ) :
    sourcePf m (fun i j => (M i j : ℝ)) = ((sourcePf m M : ℤ) : ℝ) := by
  simp [sourcePf]

theorem rawInvariant_cast (M : Matrix (Fin 6) (Fin 6) ℤ) (k : Fin 3) :
    rawInvariant (fun i j => (M i j : ℝ)) k = ((rawInvariant M k : ℤ) : ℝ) := by
  fin_cases k <;> simp [rawInvariant, Matrix.submatrix, sourcePf]

theorem A0_cast : (fun i j => (A0Z i j : ℝ)) = A0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A0Z,A0]
theorem A1_cast : (fun i j => (A1Z i j : ℝ)) = A1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A1Z,A1]

theorem integer_invariants_equal : ∀ k : Fin 3, rawInvariant A0Z k = rawInvariant A1Z k := by
  decide

theorem raw_invariants_equal (k : Fin 3) : rawInvariant A0 k = rawInvariant A1 k := by
  rw [← A0_cast, ← A1_cast, rawInvariant_cast, rawInvariant_cast, integer_invariants_equal]

theorem invariants_equal (k : Fin 3) : invariant A0 k = invariant A1 k := by
  rw [invariant, invariant, raw_invariants_equal]

theorem source_counterexample :
    A0.transpose = -A0 ∧ A1.transpose = -A1 ∧ A0.det ≠ 0 ∧ A1.det ≠ 0 ∧
    (∀ c : ℝ, A0 ≠ c • J) ∧ (∀ c : ℝ, A1 ≠ c • J) ∧
    (∀ k : Fin 3, invariant A0 k = invariant A1 k) ∧ ¬ Equivalent A0 A1 := by
  exact ⟨A0_skew, A1_skew, A0_nonsingular, A1_nonsingular, A0_nonscalar, A1_nonscalar,
    invariants_equal, no_congruence⟩

end
end SymplecticOrbitCounterexample
