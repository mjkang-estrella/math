import PartitionExpansion

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace PeakonCoefficients

open Matrix

variable {n : Type*}

def sourceA (r : n → ℂ) (q : n → ℝ) (nu : ℂ) : Matrix n n ℂ :=
  fun i j => r i * r j * Complex.sinh (nu / 2 * ((q i - q j : ℝ) : ℂ))

def sourceT (r : n → ℂ) (q : n → ℝ) (nu : ℂ) : Matrix n n ℂ :=
  fun i j => r i * r j * Complex.cosh (nu / 2 * ((q i - q j : ℝ) : ℂ))

def sourceS (r : n → ℂ) (q : n → ℝ) (nu : ℂ) : Matrix n n ℂ :=
  fun i j => (Real.sign (q i - q j) : ℂ) * sourceA r q nu i j

def sourceU (r : n → ℂ) (q : n → ℝ) (nu : ℂ) : n → ℂ :=
  fun i => r i * Complex.exp (nu / 2 * (q i : ℂ))

def sourceV (r : n → ℂ) (q : n → ℝ) (nu : ℂ) : n → ℂ :=
  fun i => r i * Complex.exp (-(nu / 2 * (q i : ℂ)))

theorem sourceA_eq_skew (r : n → ℂ) (q : n → ℝ) (nu : ℂ) :
    sourceA r q nu = skewPart (sourceU r q nu) (sourceV r q nu) := by
  apply Matrix.ext
  intro i j
  have hp : nu / 2 * ((q i - q j : ℝ) : ℂ) =
      nu / 2 * (q i : ℂ) + -(nu / 2 * (q j : ℂ)) := by push_cast; ring
  have hn : -(nu / 2 * ((q i - q j : ℝ) : ℂ)) =
      nu / 2 * (q j : ℂ) + -(nu / 2 * (q i : ℂ)) := by push_cast; ring
  simp only [sourceA, Complex.sinh, skewPart, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, sourceU, sourceV]
  rw [hn, hp, Complex.exp_add, Complex.exp_add]
  ring

theorem sourceT_eq_symmetric (r : n → ℂ) (q : n → ℝ) (nu : ℂ) :
    sourceT r q nu = symmetricPart (sourceU r q nu) (sourceV r q nu) := by
  apply Matrix.ext
  intro i j
  have hp : nu / 2 * ((q i - q j : ℝ) : ℂ) =
      nu / 2 * (q i : ℂ) + -(nu / 2 * (q j : ℂ)) := by push_cast; ring
  have hn : -(nu / 2 * ((q i - q j : ℝ) : ℂ)) =
      nu / 2 * (q j : ℂ) + -(nu / 2 * (q i : ℂ)) := by push_cast; ring
  simp only [sourceT, Complex.cosh, symmetricPart, Matrix.smul_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, sourceU, sourceV]
  rw [hn, hp, Complex.exp_add, Complex.exp_add]
  ring

theorem sourceA_zero_of_equal (r : n → ℂ) (q : n → ℝ) (nu : ℂ) (i j : n)
    (hq : q i = q j) : sourceA r q nu i j = 0 := by
  simp [sourceA, hq]


variable [LinearOrder n]

theorem sourceS_add_A_ordered (r : n → ℂ) (q : n → ℝ) (nu : ℂ) (hq : Antitone q) :
    sourceS r q nu + sourceA r q nu = upperKernel (sourceU r q nu) (sourceV r q nu) := by
  apply Matrix.ext
  intro i j
  have ha := congrFun (congrFun (sourceA_eq_skew r q nu) i) j
  simp only [skewPart, Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
    smul_eq_mul] at ha
  rcases lt_trichotomy i j with hij | hij | hij
  · have hqij : q j ≤ q i := hq hij.le
    rcases eq_or_lt_of_le hqij with heq | hlt
    · have hz := sourceA_zero_of_equal r q nu i j heq.symm
      simp only [Matrix.add_apply, sourceS, upperKernel, hij, ↓reduceIte, hz, mul_zero, zero_add]
      linear_combination 2 * ha - 2 * hz
    · have hs := Real.sign_of_pos (sub_pos.mpr hlt)
      simp only [Matrix.add_apply, sourceS, upperKernel, hij, ↓reduceIte, hs,
        Complex.ofReal_one, one_mul]
      linear_combination 2 * ha
  · subst j
    simp [sourceS, sourceA, upperKernel]
  · have hqij : q i ≤ q j := hq hij.le
    rcases eq_or_lt_of_le hqij with heq | hlt
    · have hz := sourceA_zero_of_equal r q nu i j heq
      simp [Matrix.add_apply, sourceS, upperKernel, not_lt_of_ge hij.le, hz]
    · have hs := Real.sign_of_neg (sub_neg.mpr hlt)
      simp [Matrix.add_apply, sourceS, upperKernel, not_lt_of_ge hij.le, hs]

end PeakonCoefficients
