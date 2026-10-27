import SourceDefs

open scoped Matrix.Norms.Operator ComplexOrder MatrixOrder
open Matrix
namespace LinMajorization

noncomputable def eigenTopSum {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) (k : ℕ) : ℝ :=
  ((List.ofFn hM.eigenvalues₀).take k).sum

def EigenMajorizes {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) : Prop :=
  (∀ k : ℕ, k ≤ n → eigenTopSum hY k ≤ eigenTopSum hX k) ∧
    eigenTopSum hX n = eigenTopSum hY n

theorem sourceLeft_hermitian {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (B : Matrix (Fin n) (Fin n) ℂ) (p : ℝ) :
    (sourceLeft A B p).IsHermitian := by
  exact ((hA.pow 2).add (CFC.rpow_nonneg.posSemidef)).isHermitian

theorem sourceRight_hermitian {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (B : Matrix (Fin n) (Fin n) ℂ) (p : ℝ) :
    (sourceRight A B p).IsHermitian := by
  exact ((hA.pow 2).add (CFC.rpow_nonneg.posSemidef)).isHermitian

def SourceConjecture332939 : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef),
    B.PosSemidef → ∀ p : ℝ, 0 < p →
    EigenMajorizes (sourceLeft_hermitian hA B p) (sourceRight_hermitian hA B p)

end LinMajorization
