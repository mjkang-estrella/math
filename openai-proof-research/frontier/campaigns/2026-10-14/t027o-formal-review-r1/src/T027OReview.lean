import T027O
import Controls

/-!
Independent reviewer checks for the scoped T027O support package (MIT).
These checks are not part of the author package. They do not formalize T027O.
-/

namespace T027OReview

open Polynomial

/-! ## 1. Statement pinning, written independently of the author's pretty-printed types. -/

theorem pin_triangle_coboundary :
    ∀ {K : Type} [Field K] {ι : Type}, ι → ∀ (x : ι → ι → K),
      (∀ i, x i i = 0) →
      (∀ i j, i ≠ j → x i j + x j i = 0) →
      (∀ i j k, i ≠ j → j ≠ k → k ≠ i → x i j + x j k + x k i = 0) →
      ∃ h : ι → K, ∀ i j, x i j = h i - h j :=
  @T027O.triangle_coboundary

theorem pin_cycleDerivative {K : Type} [Field K] {ι : Type} (M E : ι → ι → K) (i j k : ι) :
    T027O.cycleDerivative M E i j k =
      (E i j * M j k * M k i + M i j * E j k * M k i + M i j * M j k * E k i) +
      (E i k * M k j * M j i + M i k * E k j * M j i + M i k * M k j * E j i) := by
  unfold T027O.cycleDerivative; ring

theorem pin_principal_minor_rigidity :
    ∀ {K : Type} [Field K] {ι : Type}, ι → ∀ (M E : ι → ι → K),
      (∀ i j, i ≠ j → M i j ≠ 0) →
      (∀ i, E i i = 0) →
      (∀ i j, i ≠ j → E i j * M j i + M i j * E j i = 0) →
      (∀ i j k, i ≠ j → j ≠ k → k ≠ i → T027O.cycleDerivative M E i j k = 0) →
      (∀ i j k, i ≠ j → j ≠ k → k ≠ i →
        M i j * M j k * M k i - M i k * M k j * M j i ≠ 0) →
      ∃ h : ι → K, ∀ i j, E i j = (h i - h j) * M i j :=
  @T027O.principal_minor_rigidity

/-- Ordered-triple quantification is harmless: the cycle polynomial is invariant
under every permutation of the three indices. -/
theorem cycleDerivative_rotate {K : Type} [Field K] {ι : Type} (M E : ι → ι → K) (i j k : ι) :
    T027O.cycleDerivative M E i j k = T027O.cycleDerivative M E j k i := by
  unfold T027O.cycleDerivative; ring

theorem cycleDerivative_swap {K : Type} [Field K] {ι : Type} (M E : ι → ι → K) (i j k : ι) :
    T027O.cycleDerivative M E i j k = T027O.cycleDerivative M E j i k := by
  unfold T027O.cycleDerivative; ring

/-! ## 2. Bridge: the explicit polynomials are first-order principal-minor derivatives. -/

/-- The polynomial-matrix path `M + t E`. -/
noncomputable def path {K : Type} [Field K] {ι : Type} (M E : ι → ι → K) : Matrix ι ι K[X] :=
  fun i j => C (M i j) + X * C (E i j)

/-- First derivative at `t = 0` of the principal minor on the ordered index list `s`. -/
noncomputable def minorDeriv {K : Type} [Field K] {ι : Type} {n : ℕ} (M E : ι → ι → K)
    (s : Fin n → ι) : K :=
  (derivative ((path M E).submatrix s s).det).eval 0

theorem minorDeriv_one {K : Type} [Field K] {ι : Type} (M E : ι → ι → K) (i : ι) :
    minorDeriv M E ![i] = E i i := by
  rw [minorDeriv, Matrix.det_fin_one]; simp [path]

theorem minorDeriv_two {K : Type} [Field K] {ι : Type} (M E : ι → ι → K) (i j : ι) :
    minorDeriv M E ![i, j] =
      E i i * M j j + M i i * E j j - (E i j * M j i + M i j * E j i) := by
  rw [minorDeriv, Matrix.det_fin_two]; simp [path, derivative_mul]

/-- Full first derivative of a 3×3 principal minor, with no hypotheses. -/
theorem minorDeriv_three {K : Type} [Field K] {ι : Type} (M E : ι → ι → K) (i j k : ι) :
    minorDeriv M E ![i, j, k] =
      (E i i * M j j * M k k + M i i * E j j * M k k + M i i * M j j * E k k)
      - (E i i * M j k * M k j + M i i * (E j k * M k j + M j k * E k j))
      - (E j j * M i k * M k i + M j j * (E i k * M k i + M i k * E k i))
      - (E k k * M i j * M j i + M k k * (E i j * M j i + M i j * E j i))
      + T027O.cycleDerivative M E i j k := by
  rw [minorDeriv, Matrix.det_fin_three]
  simp [path, derivative_mul, T027O.cycleDerivative]
  ring

/-- Under stationary 1×1 minors, the author's pair polynomial is minus the 2×2 derivative. -/
theorem pair_iff_minor2 {K : Type} [Field K] {ι : Type} (M E : ι → ι → K)
    (hdiag : ∀ i, E i i = 0) (i j : ι) :
    minorDeriv M E ![i, j] = 0 ↔ E i j * M j i + M i j * E j i = 0 := by
  rw [minorDeriv_two, hdiag i, hdiag j]
  constructor <;> intro h <;> linear_combination -h

/-- Under stationary 1×1 and 2×2 minors, the cycle polynomial is the 3×3 derivative. -/
theorem cycle_eq_minor3 {K : Type} [Field K] {ι : Type} (M E : ι → ι → K)
    (hdiag : ∀ i, E i i = 0)
    (hpair : ∀ i j, i ≠ j → E i j * M j i + M i j * E j i = 0)
    (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    minorDeriv M E ![i, j, k] = T027O.cycleDerivative M E i j k := by
  rw [minorDeriv_three, hdiag i, hdiag j, hdiag k, hpair j k hjk,
    hpair i k (Ne.symm hki), hpair i j hij]
  ring

/-- Prose form of the lemma, using actual derivative-of-minor hypotheses for sizes 1, 2, 3
(the only sizes the prose proof uses), over an arbitrary field and index type. -/
theorem rigidity_from_minor_derivatives {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (o : ι) (M E : ι → ι → K)
    (hnz : ∀ i j, i ≠ j → M i j ≠ 0)
    (h1 : ∀ i, minorDeriv M E ![i] = 0)
    (h2 : ∀ i j, i ≠ j → minorDeriv M E ![i, j] = 0)
    (h3 : ∀ i j k, i ≠ j → j ≠ k → k ≠ i → minorDeriv M E ![i, j, k] = 0)
    (hgeneric : ∀ i j k, i ≠ j → j ≠ k → k ≠ i →
      M i j * M j k * M k i - M i k * M k j * M j i ≠ 0) :
    ∃ h : ι → K, ∀ i j, E i j =
      (Matrix.diagonal h * Matrix.of M - Matrix.of M * Matrix.diagonal h) i j := by
  have hdiag : ∀ i, E i i = 0 := fun i => by rw [← minorDeriv_one M E i]; exact h1 i
  have hpair : ∀ i j, i ≠ j → E i j * M j i + M i j * E j i = 0 :=
    fun i j hij => (pair_iff_minor2 M E hdiag i j).mp (h2 i j hij)
  have htri : ∀ i j k, i ≠ j → j ≠ k → k ≠ i → T027O.cycleDerivative M E i j k = 0 :=
    fun i j k hij hjk hki => by
      rw [← cycle_eq_minor3 M E hdiag hpair i j k hij hjk hki]; exact h3 i j k hij hjk hki
  obtain ⟨h, hh⟩ := T027O.principal_minor_rigidity o M E hnz hdiag hpair htri hgeneric
  refine ⟨h, fun i j => ?_⟩
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  rw [hh i j]; ring

/-! ## 3. Degenerate index types and characteristic. -/

/-- One index: the theorem applies, and forces `E = 0`. -/
theorem degenerate_one (M E : Fin 1 → Fin 1 → ℚ) (hdiag : ∀ i, E i i = 0) :
    ∃ h : Fin 1 → ℚ, ∀ i j, E i j = (h i - h j) * M i j :=
  T027O.principal_minor_rigidity 0 M E (fun i j hij => absurd (Subsingleton.elim i j) hij) hdiag
    (fun i j hij => absurd (Subsingleton.elim i j) hij)
    (fun i j _ hij => absurd (Subsingleton.elim i j) hij)
    (fun i j _ hij => absurd (Subsingleton.elim i j) hij)

/-- Two indices: the triangle hypotheses are vacuous and the theorem still applies. -/
theorem degenerate_two (M E : Fin 2 → Fin 2 → ℚ)
    (hnz : ∀ i j, i ≠ j → M i j ≠ 0) (hdiag : ∀ i, E i i = 0)
    (hpair : ∀ i j, i ≠ j → E i j * M j i + M i j * E j i = 0) :
    ∃ h : Fin 2 → ℚ, ∀ i j, E i j = (h i - h j) * M i j :=
  T027O.principal_minor_rigidity 0 M E hnz hdiag hpair
    (by intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> simp)
    (by intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> simp)

/-- A positive 4×4 instance over ZMod 5 with a nonzero E: no characteristic-zero input. -/
def M5 : Fin 4 → Fin 4 → ZMod 5 := !![0, 4, 4, 1; 4, 0, 3, 2; 1, 3, 0, 1; 1, 1, 1, 0]
def h5 : Fin 4 → ZMod 5 := ![0, 1, 2, 4]
def E5 : Fin 4 → Fin 4 → ZMod 5 := fun i j => (h5 i - h5 j) * M5 i j

theorem E5_ne_zero : E5 0 1 ≠ 0 := by decide

theorem M5_nz : ∀ i j : Fin 4, i ≠ j → M5 i j ≠ 0 := by decide
theorem E5_diag : ∀ i : Fin 4, E5 i i = 0 := by decide
theorem E5_pair : ∀ i j : Fin 4, i ≠ j → E5 i j * M5 j i + M5 i j * E5 j i = 0 := by decide
theorem E5_cycle : ∀ i j k : Fin 4, i ≠ j → j ≠ k → k ≠ i →
    E5 i j * M5 j k * M5 k i + M5 i j * E5 j k * M5 k i +
    M5 i j * M5 j k * E5 k i + E5 i k * M5 k j * M5 j i +
    M5 i k * E5 k j * M5 j i + M5 i k * M5 k j * E5 j i = 0 := by decide
theorem M5_generic : ∀ i j k : Fin 4, i ≠ j → j ≠ k → k ≠ i →
    M5 i j * M5 j k * M5 k i - M5 i k * M5 k j * M5 j i ≠ 0 := by decide

theorem positive_char5 : ∃ h : Fin 4 → ZMod 5, ∀ i j, E5 i j = (h i - h j) * M5 i j := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact T027O.principal_minor_rigidity 0 M5 E5 M5_nz E5_diag E5_pair
    (fun i j k a b c => by unfold T027O.cycleDerivative; exact E5_cycle i j k a b c) M5_generic

/-! ## 4. Each hypothesis is non-deletable (rational counterexamples). -/

/-- Deleting `hdiag`. -/
theorem drop_hdiag :
    ¬ ∃ h : Fin 1 → ℚ, ∀ i j, (fun _ _ => (1 : ℚ)) i j = (h i - h j) * (fun _ _ => (1 : ℚ)) i j := by
  rintro ⟨h, hh⟩; have := hh 0 0; norm_num at this

/-- Deleting `hnz`: zero 2×2 M; every other hypothesis holds (triangles vacuous). -/
def zM : Fin 2 → Fin 2 → ℚ := fun _ _ => 0
def zE : Fin 2 → Fin 2 → ℚ := !![0, 1; 0, 0]

theorem drop_hnz_others :
    (∀ i, zE i i = 0) ∧ (∀ i j, i ≠ j → zE i j * zM j i + zM i j * zE j i = 0) := by
  constructor
  · intro i; fin_cases i <;> simp [zE]
  · intro i j _; simp [zM]

theorem drop_hnz_fails : ¬ ∃ h : Fin 2 → ℚ, ∀ i j, zE i j = (h i - h j) * zM i j := by
  rintro ⟨h, hh⟩; have := hh 0 1; simp [zE, zM] at this

/-- Deleting `hpair`: on two indices the remaining hypotheses hold. -/
def pM : Fin 2 → Fin 2 → ℚ := !![0, 1; 1, 0]

theorem drop_hpair_others : (∀ i j, i ≠ j → pM i j ≠ 0) ∧ (∀ i, pM i i = 0) := by
  constructor
  · intro i j; fin_cases i <;> fin_cases j <;> simp [pM]
  · intro i; fin_cases i <;> simp [pM]

theorem drop_hpair_fails : ¬ ∃ h : Fin 2 → ℚ, ∀ i j, pM i j = (h i - h j) * pM i j := by
  rintro ⟨h, hh⟩
  have a := hh 0 1; have b := hh 1 0
  simp [pM] at a b; linarith

/-- Deleting `htri`: generic M, antisymmetric x with nonzero triangle sum. -/
def tx : Fin 3 → Fin 3 → ℚ := !![0, 1, -1; -1, 0, 1; 1, -1, 0]
def tE : Fin 3 → Fin 3 → ℚ := fun i j => tx i j * T027OControls.genericM i j

theorem drop_htri_others :
    (∀ i, tE i i = 0) ∧ (∀ i j, i ≠ j → tE i j * T027OControls.genericM j i +
      T027OControls.genericM i j * tE j i = 0) := by
  constructor
  · intro i; fin_cases i <;> simp [tE, tx, T027OControls.genericM]
  · intro i j _; fin_cases i <;> fin_cases j <;> norm_num [tE, tx, T027OControls.genericM]

theorem drop_htri_violated : T027O.cycleDerivative T027OControls.genericM tE 0 1 2 ≠ 0 := by
  norm_num [T027O.cycleDerivative, tE, tx, T027OControls.genericM]

theorem drop_htri_fails :
    ¬ ∃ h : Fin 3 → ℚ, ∀ i j, tE i j = (h i - h j) * T027OControls.genericM i j := by
  rintro ⟨h, hh⟩
  have a := hh 0 1; have b := hh 1 2; have c := hh 2 0
  norm_num [tE, tx, T027OControls.genericM] at a b c; linarith

/-- The author's genericity counterexample is characteristic-sensitive: over ZMod 3 the same
cyclic E is a diagonal commutator, so the ℚ control is the right setting for necessity. -/
theorem author_control_char3 :
    ∃ h : Fin 3 → ZMod 3, ∀ i j,
      (!![0, 1, -1; -1, 0, 1; 1, -1, 0] : Matrix (Fin 3) (Fin 3) (ZMod 3)) i j =
        (h i - h j) * (!![0, 1, 1; 1, 0, 1; 1, 1, 0] : Matrix (Fin 3) (Fin 3) (ZMod 3)) i j :=
  ⟨![0, 2, 1], by intro i j; fin_cases i <;> fin_cases j <;> decide⟩

end T027OReview
