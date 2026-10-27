import InputEvaluation
import QuadraticCertificate

set_option warningAsError true

open Matrix
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace SquaredPolya

/-- Exactly the coefficient in Moslehian--Fu Conjecture 2.16, first display. -/
def sourceCoefficient (m₁ M₁ m₂ M₂ : ℝ) : ℝ :=
  (1 / 4 : ℝ) * (Real.sqrt (M₁ * M₂ / (m₁ * m₂)) +
    Real.sqrt (m₁ * m₂ / (M₁ * M₂))) ^ 2

/-- The literal source assertion restricted to finite-dimensional complex operators.
A refutation of this restricted universal assertion suffices for the source conjecture. -/
def SourceClaim329636First : Prop :=
  ∀ (V W : Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (A B : Matrix V V ℂ) (Φ : Matrix V V ℂ →ₗ[ℂ] Matrix W W ℂ)
    (m₁ M₁ m₂ M₂ : ℝ),
    Φ 1 = 1 →
    (∀ Z, Z.PosSemidef → (Φ Z).PosSemidef) →
    0 < m₁ → m₁ ≤ M₁ → 0 < m₂ → m₂ ≤ M₂ →
    (A - m₁ ^ 2 • (1 : Matrix V V ℂ)).PosSemidef →
    (M₁ ^ 2 • (1 : Matrix V V ℂ) - A).PosSemidef →
    (B - m₂ ^ 2 • (1 : Matrix V V ℂ)).PosSemidef →
    (M₂ ^ 2 • (1 : Matrix V V ℂ) - B).PosSemidef →
    (sourceCoefficient m₁ M₁ m₂ M₂ •
        (Φ (geometricMean A B) * Φ (geometricMean A B)) -
      geometricMean (Φ A) (Φ B) * geometricMean (Φ A) (Φ B)).PosSemidef

theorem sourceCoefficient_witness :
    sourceCoefficient 1 32 1 32 = (1025 / 64 : ℝ)^2 := by
  norm_num [sourceCoefficient, Real.sqrt_div]

theorem literal_matrix_failure :
    ¬ (sourceCoefficient 1 32 1 32 •
        (blockAverage (geometricMean inputU inputV) *
          blockAverage (geometricMean inputU inputV)) -
      geometricMean (blockAverage inputU) (blockAverage inputV) *
        geometricMean (blockAverage inputU) (blockAverage inputV)).PosSemidef := by
  rw [sourceCoefficient_witness, inputMean_image, inputU_image, inputV_image,
    geometricMean_fg]
  exact matrix_defect_not_posSemidef

theorem source_counterexample_329636_first : ¬ SourceClaim329636First := by
  intro h
  apply literal_matrix_failure
  apply h (Fin 2 ⊕ Fin 2) (Fin 2) inputU inputV blockAverage 1 32 1 32
      blockAverage_unital (fun Z hZ => blockAverage_positive hZ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · simpa using inputU_lower
  · norm_num
    exact inputU_upper
  · simpa using inputV_lower
  · norm_num
    exact inputV_upper


end SquaredPolya
