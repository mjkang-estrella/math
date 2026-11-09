import PolynomialConvexity.Source

namespace PolynomialConvexity
noncomputable section
open Finset

/-- Relabel coordinates, even when the edge values repeat. -/
def tuplePerm {n L d : ℕ} (σ : Equiv.Perm (Fin d)) :
    (Fin d → Edge n L) ≃ (Fin d → Edge n L) where
  toFun e := e ∘ σ
  invFun e := e ∘ σ.symm
  left_inv e := by ext i; simp
  right_inv e := by ext i; simp

theorem weight_perm {n L d : ℕ} (x : Edge n L → ℝ)
    (e : Fin d → Edge n L) (σ : Equiv.Perm (Fin d)) :
    weight x (tuplePerm σ e) = weight x e := by
  exact Equiv.prod_comp σ (fun i => x (e i))

/-- This finite sum is the candidate mixed moment coefficient, not an expectation. -/
def symCoefficient {n L d : ℕ} (e : Fin d → Edge n L) : ℝ :=
  ∑ σ : Equiv.Perm (Fin d), coefficient (tuplePerm σ e)

theorem sum_reindex {n L d : ℕ} (x : Edge n L → ℝ)
    (σ : Equiv.Perm (Fin d)) :
    (∑ e : Fin d → Edge n L, weight x e * coefficient (tuplePerm σ e)) =
      sourcePolynomial n L d x := by
  calc
    _ = ∑ e : Fin d → Edge n L,
        weight x (tuplePerm σ e) * coefficient (tuplePerm σ e) := by
      simp_rw [weight_perm]
    _ = _ := (tuplePerm σ).sum_comp (fun e => weight x e * coefficient e)

/-- The exact factorial normalization, independently of the analytic moment bridge. -/
theorem symmetrized_sum {n L d : ℕ} (x : Edge n L → ℝ) :
    (∑ e : Fin d → Edge n L, weight x e * symCoefficient e) =
      (Nat.factorial d : ℝ) * sourcePolynomial n L d x := by
  simp only [symCoefficient, mul_sum]
  rw [sum_comm]
  simp_rw [sum_reindex]
  simp [Fintype.card_perm]

end
end PolynomialConvexity
