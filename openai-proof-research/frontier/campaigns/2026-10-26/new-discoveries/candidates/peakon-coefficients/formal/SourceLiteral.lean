import SourcePermutation

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace PeakonCoefficients

open Matrix

variable {N : ℕ}

def particleRoots (p : Fin N → ℝ) : Fin N → ℂ := fun i => (Real.sqrt (p i) : ℂ)

def literalA (p q : Fin N → ℝ) (nu : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (Real.sqrt (p i * p j) : ℂ) * Complex.sinh (nu / 2 * ((q i - q j : ℝ) : ℂ))

def literalT (p q : Fin N → ℝ) (nu : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (Real.sqrt (p i * p j) : ℂ) * Complex.cosh (nu / 2 * ((q i - q j : ℝ) : ℂ))

def literalS (p q : Fin N → ℝ) (nu : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (Real.sign (q i - q j) : ℂ) * literalA p q nu i j

def spectralLambda (z gamma : ℂ) : ℂ := (z ^ 2 - 1) / (2 * z + gamma)

def spectralXi (z gamma : ℂ) : ℂ := (z ^ 2 + gamma * z + 1) / (2 * z + gamma)

def literalLax (p q : Fin N → ℝ) (nu z gamma : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  literalS p q nu + spectralLambda z gamma • literalT p q nu +
    spectralXi z gamma • literalA p q nu

def literalHamiltonian (p q : Fin N → ℝ) (nu gamma : ℂ) (k : ℕ) : ℂ :=
  (k : ℂ) * Matrix.trace ((literalT p q nu + (gamma / 2) • literalA p q nu) *
    (literalS p q nu + literalA p q nu) ^ (k - 1))

theorem spectral_curve (z gamma : ℂ) (hz : 2 * z + gamma ≠ 0) :
    spectralXi z gamma ^ 2 = spectralLambda z gamma ^ 2 +
      gamma * spectralLambda z gamma + 1 := by
  have hx : spectralXi z gamma * (2 * z + gamma) = z ^ 2 + gamma * z + 1 :=
    div_mul_cancel₀ _ hz
  have hl : spectralLambda z gamma * (2 * z + gamma) = z ^ 2 - 1 :=
    div_mul_cancel₀ _ hz
  have hxs := congrArg (fun w : ℂ => w ^ 2) hx
  have hls := congrArg (fun w : ℂ => w ^ 2) hl
  have hp : (z ^ 2 + gamma * z + 1) ^ 2 - (z ^ 2 - 1) ^ 2 -
      gamma * (z ^ 2 - 1) * (2 * z + gamma) - (2 * z + gamma) ^ 2 = 0 := by ring
  apply (mul_right_cancel₀ (pow_ne_zero 2 hz))
  linear_combination hxs - hls - gamma * (2 * z + gamma) * hl + hp

theorem literalA_eq_source (p q : Fin N → ℝ) (nu : ℂ) (hp : ∀ i, 0 ≤ p i) :
    literalA p q nu = sourceA (particleRoots p) q nu := by
  apply Matrix.ext
  intro i j
  simp only [literalA, sourceA, particleRoots, Real.sqrt_mul (hp i), Complex.ofReal_mul]

theorem literalT_eq_source (p q : Fin N → ℝ) (nu : ℂ) (hp : ∀ i, 0 ≤ p i) :
    literalT p q nu = sourceT (particleRoots p) q nu := by
  apply Matrix.ext
  intro i j
  simp only [literalT, sourceT, particleRoots, Real.sqrt_mul (hp i), Complex.ofReal_mul]

theorem literalS_eq_source (p q : Fin N → ℝ) (nu : ℂ) (hp : ∀ i, 0 ≤ p i) :
    literalS p q nu = sourceS (particleRoots p) q nu := by
  unfold literalS sourceS
  rw [literalA_eq_source p q nu hp]

theorem literalLax_eq_source (p q : Fin N → ℝ) (nu z gamma : ℂ) (hp : ∀ i, 0 ≤ p i) :
    literalLax p q nu z gamma = sourceLax (particleRoots p) q nu
      (spectralLambda z gamma) (spectralXi z gamma) := by
  simp only [literalLax, sourceLax, literalS_eq_source p q nu hp,
    literalA_eq_source p q nu hp, literalT_eq_source p q nu hp]

theorem literalHamiltonian_eq_source (p q : Fin N → ℝ) (nu gamma : ℂ)
    (hp : ∀ i, 0 ≤ p i) (k : ℕ) :
    literalHamiltonian p q nu gamma k = sourceHamiltonian (particleRoots p) q nu gamma k := by
  simp only [literalHamiltonian, sourceHamiltonian, literalS_eq_source p q nu hp,
    literalA_eq_source p q nu hp, literalT_eq_source p q nu hp]

theorem literal_source_partition (p q : Fin N → ℝ) (nu z gamma : ℂ)
    (hp : ∀ i, 0 ≤ p i) (hz : 2 * z + gamma ≠ 0) (m : ℕ) (hm : 0 < m) :
    Matrix.trace (literalLax p q nu z gamma ^ m) =
      ∑ j ∈ Finset.range m, ∑ k ∈ (Finset.Icc 1 N).sym (j + 1),
        if k.val.sum = m then coefficientWeight (K := ℂ) m k.val *
          spectralLambda z gamma ^ (j + 1) *
            (k.val.map (literalHamiltonian p q nu gamma)).prod else 0 := by
  rw [literalLax_eq_source p q nu z gamma hp]
  simpa only [literalHamiltonian_eq_source p q nu gamma hp] using
    source_trace_partition (particleRoots p) q nu (spectralLambda z gamma)
      (spectralXi z gamma) gamma (spectral_curve z gamma hz) m hm

end PeakonCoefficients
