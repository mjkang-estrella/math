import Mathlib

namespace KadarYu

open Matrix Finset

def UpperBandOne {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, i.val + 1 < j.val → A i j = 0

def NonzeroSuperdiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, i.val + 1 = j.val → A i j ≠ 0

theorem eigenvector_zero_of_first_zero {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hband : UpperBandOne A) (hoff : NonzeroSuperdiag A)
    (v : Fin (n + 1) → ℝ) (mu : ℝ) (heig : A *ᵥ v = mu • v)
    (hfirst : v 0 = 0) : v = 0 := by
  have hz : ∀ k : ℕ, ∀ hk : k < n + 1, v ⟨k, hk⟩ = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases hk0 : k = 0
      · subst k
        exact hfirst
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        let i : Fin (n + 1) := ⟨j, by omega⟩
        let z : Fin (n + 1) := ⟨j + 1, hk⟩
        have hi : v i = 0 := ih j (by omega) i.isLt
        have hsum : (A *ᵥ v) i = A i z * v z := by
          change (∑ l : Fin (n + 1), A i l * v l) = A i z * v z
          apply Finset.sum_eq_single z
          · intro l _ hl
            by_cases hlt : l.val < j + 1
            · rw [ih l.val hlt l.isLt, mul_zero]
            · have hne : l.val ≠ j + 1 := by
                intro h
                apply hl
                exact Fin.ext h
              have hfar : i.val + 1 < l.val := by dsimp [i]; omega
              rw [hband i l hfar, zero_mul]
          · simp
        have hrow := congrFun heig i
        rw [hsum] at hrow
        change A i z * v z = mu * v i at hrow
        rw [hi, mul_zero] at hrow
        exact (mul_eq_zero.mp hrow).resolve_left (hoff i z (by rfl))
  ext i
  exact hz i.val i.isLt

theorem eigenvector_first_ne_zero {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hband : UpperBandOne A) (hoff : NonzeroSuperdiag A)
    (v : Fin (n + 1) → ℝ) (mu : ℝ) (heig : A *ᵥ v = mu • v)
    (hv : v ≠ 0) : v 0 ≠ 0 := by
  intro h
  exact hv (eigenvector_zero_of_first_zero A hband hoff v mu heig h)

theorem eigenvectors_proportional {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hband : UpperBandOne A) (hoff : NonzeroSuperdiag A)
    (u v : Fin (n + 1) → ℝ) (mu : ℝ)
    (hu : A *ᵥ u = mu • u) (hv : A *ᵥ v = mu • v) :
    v 0 • u = u 0 • v := by
  have he : A *ᵥ (v 0 • u - u 0 • v) = mu • (v 0 • u - u 0 • v) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hu, hv]
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hz : v 0 • u - u 0 • v = 0 := by
    apply eigenvector_zero_of_first_zero A hband hoff _ mu he
    change v 0 * u 0 - u 0 * v 0 = 0
    ring
  exact sub_eq_zero.mp hz

theorem hermitian_upper_band_eigenvalues_injective {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.IsHermitian)
    (hband : UpperBandOne A) (hoff : NonzeroSuperdiag A) :
    Function.Injective hA.eigenvalues := by
  intro i j hij
  by_contra hne
  let u := hA.eigenvectorBasis i
  let v := hA.eigenvectorBasis j
  have hu : A *ᵥ u.ofLp = hA.eigenvalues i • u.ofLp := hA.mulVec_eigenvectorBasis i
  have hv : A *ᵥ v.ofLp = hA.eigenvalues i • v.ofLp := by
    rw [hij]
    exact hA.mulVec_eigenvectorBasis j
  have hp := eigenvectors_proportional A hband hoff u.ofLp v.ofLp _ hu hv
  have hvec : v.ofLp 0 • u = u.ofLp 0 • v := by
    apply PiLp.ext
    intro k
    exact congrFun hp k
  have hnz : v.ofLp ≠ 0 := by
    intro h
    have hzero : v = 0 := PiLp.ext fun k => congrFun h k
    have hn := hA.eigenvectorBasis.orthonormal.norm_eq_one j
    change ‖v‖ = 1 at hn
    rw [hzero, norm_zero] at hn
    norm_num at hn
  have hvfirst := eigenvector_first_ne_zero A hband hoff v.ofLp _ hv hnz
  have hip := congrArg (fun z => inner ℝ u z) hvec
  have huv : inner ℝ u v = 0 := hA.eigenvectorBasis.orthonormal.inner_eq_zero hne
  have huu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq]
    change ‖hA.eigenvectorBasis i‖ ^ 2 = 1
    rw [hA.eigenvectorBasis.orthonormal.norm_eq_one]
    norm_num
  simp only [inner_smul_right, huu, huv, mul_one, mul_zero] at hip
  exact hvfirst hip

theorem hermitian_upper_band_charpoly_separable {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.IsHermitian)
    (hband : UpperBandOne A) (hoff : NonzeroSuperdiag A) :
    A.charpoly.Separable := by
  rw [hA.charpoly_eq]
  exact Polynomial.separable_prod_X_sub_C_iff.mpr
    (hermitian_upper_band_eigenvalues_injective A hA hband hoff)

theorem hermitian_upper_band_charpoly_squarefree {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.IsHermitian)
    (hband : UpperBandOne A) (hoff : NonzeroSuperdiag A) :
    Squarefree A.charpoly :=
  (hermitian_upper_band_charpoly_separable A hA hband hoff).squarefree

theorem hermitian_upper_band_charpoly_squarefree_any_dimension {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hband : UpperBandOne A) (hoff : NonzeroSuperdiag A) :
    Squarefree A.charpoly := by
  cases n with
  | zero => simp only [Matrix.charpoly_isEmpty]; exact squarefree_one
  | succ n => exact hermitian_upper_band_charpoly_squarefree A hA hband hoff

noncomputable def jacobiMatrix (n : ℕ) (diag off : ℕ → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if i = j then diag i.val else
  if i.val + 1 = j.val then off i.val else
  if j.val + 1 = i.val then off j.val else 0

theorem jacobiMatrix_hermitian (n : ℕ) (diag off : ℕ → ℝ) :
    (jacobiMatrix n diag off).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases h : i = j
  · subst j
    simp [jacobiMatrix]
  · have h' : j ≠ i := Ne.symm h
    by_cases hij : i.val + 1 = j.val
    · have hji : j.val + 1 ≠ i.val := by omega
      simp [jacobiMatrix, h, h', hij, hji]
    · by_cases hji : j.val + 1 = i.val
      · simp [jacobiMatrix, h, h', hij, hji]
      · simp [jacobiMatrix, h, h', hij, hji]

theorem jacobiMatrix_band (n : ℕ) (diag off : ℕ → ℝ) :
    UpperBandOne (jacobiMatrix n diag off) := by
  intro i j h
  have hne : i ≠ j := by intro he; have := congrArg Fin.val he; omega
  have hij : i.val + 1 ≠ j.val := by omega
  have hji : j.val + 1 ≠ i.val := by omega
  simp [jacobiMatrix, hne, hij, hji]

theorem jacobiMatrix_off_nonzero (n : ℕ) (diag off : ℕ → ℝ)
    (hoff : ∀ i : ℕ, i + 1 < n → off i ≠ 0) :
    NonzeroSuperdiag (jacobiMatrix n diag off) := by
  intro i j h
  have hne : i ≠ j := by intro he; have := congrArg Fin.val he; omega
  have ho : off i.val ≠ 0 := hoff i.val (by omega)
  simpa [jacobiMatrix, hne, h] using ho

theorem jacobiMatrix_charpoly_squarefree (n : ℕ) (diag off : ℕ → ℝ)
    (hoff : ∀ i : ℕ, i + 1 < n → off i ≠ 0) :
    Squarefree (jacobiMatrix n diag off).charpoly :=
  hermitian_upper_band_charpoly_squarefree_any_dimension _
    (jacobiMatrix_hermitian n diag off) (jacobiMatrix_band n diag off)
    (jacobiMatrix_off_nonzero n diag off hoff)

end KadarYu
