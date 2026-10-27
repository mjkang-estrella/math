import ReducedHeadTailDensity

namespace KadarYu

open Matrix Finset Polynomial

noncomputable def headTailCommonFactor (h : ℕ)
    (A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (c : ℝ) : Polynomial ℝ :=
  GCDMonoid.gcd (headTailPolynomial h A c 0) (headTailPolynomial h A c 1)

noncomputable def headTailReduced (h : ℕ)
    (A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (c : ℝ) (s : ℕ) : Polynomial ℝ :=
  headTailPolynomial h A c s / headTailCommonFactor h A c

theorem headTailCommonFactor_monic (h : ℕ)
    (A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (c : ℝ) :
    (headTailCommonFactor h A c).Monic := by
  classical
  have hn : headTailPolynomial h A c 1 ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hm := Polynomial.monic_normalize (p := headTailCommonFactor h A c)
    (gcd_ne_zero_of_right hn)
  simpa only [headTailCommonFactor, _root_.normalize_gcd] using hm

theorem headTailCommonFactor_dvd (h : ℕ)
    (A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (c : ℝ) :
    ∀ s, headTailCommonFactor h A c ∣ headTailPolynomial h A c s := by
  intro s
  induction s using Nat.twoStepInduction with
  | zero => exact gcd_dvd_left _ _
  | one => exact gcd_dvd_right _ _
  | more s ih0 ih1 =>
    rw [headTailPolynomial_recurrence]
    exact dvd_sub (dvd_mul_of_dvd_right ih1 X) (dvd_mul_of_dvd_right ih0 (C (c ^ 2)))

theorem headTailReduced_factor (h : ℕ)
    (A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (c : ℝ) (s : ℕ) :
    headTailPolynomial h A c s = headTailCommonFactor h A c * headTailReduced h A c s :=
  (EuclideanDomain.mul_div_cancel' (headTailCommonFactor_monic h A c).ne_zero
    (headTailCommonFactor_dvd h A c s)).symm

theorem headTailReduced_monic (h : ℕ)
    (A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (c : ℝ) (s : ℕ) :
    (headTailReduced h A c s).Monic := by
  apply (headTailCommonFactor_monic h A c).of_mul_monic_left
  rw [← headTailReduced_factor]
  exact Matrix.charpoly_monic _

theorem headTailReduced_recurrence (h : ℕ)
    (A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (c : ℝ) (hc : c ^ 2 = 1) (s : ℕ) :
    headTailReduced h A c (s + 2) =
      X * headTailReduced h A c (s + 1) - headTailReduced h A c s := by
  apply mul_left_cancel₀ (headTailCommonFactor_monic h A c).ne_zero
  calc
    _ = headTailPolynomial h A c (s + 2) := (headTailReduced_factor h A c (s + 2)).symm
    _ = X * headTailPolynomial h A c (s + 1) - headTailPolynomial h A c s := by
      rw [headTailPolynomial_recurrence, hc, C_1, one_mul]
    _ = _ := by
      rw [headTailReduced_factor h A c (s + 1), headTailReduced_factor h A c s]
      ring

theorem headTailReduced_coprime (h : ℕ)
    (A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (c : ℝ) (hc : c ^ 2 = 1) :
    ∀ s, IsCoprime (headTailReduced h A c s) (headTailReduced h A c (s + 1)) := by
  intro s
  induction s with
  | zero => exact isCoprime_div_gcd_div_gcd (Matrix.charpoly_monic _).ne_zero
  | succ s ih =>
    have hh := coprime_recurrence_step (p := headTailReduced h A c s)
      (q := headTailReduced h A c (s + 1)) (L := X) (by norm_num : (1 : ℝ) ≠ 0) ih
    rw [headTailReduced_recurrence h A c hc s]
    simpa only [C_1, one_mul] using hh

theorem headTailReduced_root_distribution (h : ℕ)
    {A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hA : A.IsHermitian)
    (c : ℝ) (hc : c ^ 2 = 1) :
    Squarefree (X * headTailReduced h A c 0 - headTailReduced h A c 1) ∧
    (∀ s, Squarefree (headTailReduced h A c s)) ∧
    (∃ N C : ℕ, C ≤ 2 * (h + 1) ∧ ∀ s, N ≤ s →
      exteriorRootCount (headTailReduced h A c s) = C) ∧
    Set.Icc (-2 : ℝ) 2 ⊆ closure
      {y : ℝ | y ∈ Set.Icc (-2 : ℝ) 2 ∧ ∃ s : ℕ, (headTailReduced h A c s).eval y = 0} :=
  reduced_headTail_root_distribution h hA c hc (headTailCommonFactor h A c)
    (headTailReduced h A c) (headTailCommonFactor_monic h A c)
    (headTailReduced_monic h A c) (headTailReduced_factor h A c)
    (headTailReduced_coprime h A c hc)

end KadarYu
