import ArrowheadSpectral

open Finset Matrix
open scoped RealInnerProductSpace
namespace FlatBernoulli
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def centerOrbit (t v : ι → ℝ) (n : ℕ) : EuclideanSpace ℝ (Option ι) :=
  ((arrowhead t v).toEuclideanLin^n) centerVector

theorem centerMoment_eq_orbit (t v : ι → ℝ) (n : ℕ) :
    centerMoment t v n = centerOrbit t v n none := by
  simp [centerMoment, centerOrbit, centerVector, EuclideanSpace.inner_single_left]

theorem centerOrbit_zero_node (t v : ι → ℝ) (i : ι) :
    centerOrbit t v 0 (some i) = 0 := by
  simp [centerOrbit, centerVector, EuclideanSpace.basisFun_apply]

theorem centerOrbit_succ (t v : ι → ℝ) (n : ℕ) :
    centerOrbit t v (n+1) = (arrowhead t v).toEuclideanLin (centerOrbit t v n) := by
  simp only [centerOrbit, pow_succ', Module.End.mul_apply]

theorem centerMoment_succ (t v : ι → ℝ) (n : ℕ) :
    centerMoment t v (n+1) = ∑ i, v i*centerOrbit t v n (some i) := by
  rw [centerMoment_eq_orbit, centerOrbit_succ]
  change ((arrowhead t v) *ᵥ (centerOrbit t v n).ofLp) none = _
  exact arrowhead_mulVec_none t v _

theorem centerOrbit_succ_node (t v : ι → ℝ) (n : ℕ) (i : ι) :
    centerOrbit t v (n+1) (some i) = v i*centerMoment t v n +
      t i*centerOrbit t v n (some i) := by
  rw [centerOrbit_succ, centerMoment_eq_orbit]
  change ((arrowhead t v) *ᵥ (centerOrbit t v n).ofLp) (some i) = _
  exact arrowhead_mulVec_some t v _ i

theorem centerOrbit_node_expansion (t v : ι → ℝ) (n : ℕ) (i : ι) :
    centerOrbit t v (n+1) (some i) =
      v i*(∑ k ∈ Finset.range (n+1), t i^k*centerMoment t v (n-k)) := by
  induction n with
  | zero =>
    rw [centerOrbit_succ_node, centerOrbit_zero_node]
    simp
  | succ n hn =>
    rw [centerOrbit_succ_node, hn]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul, Nat.sub_zero]
    have he : (∑ k ∈ Finset.range (n+1), t i^(k+1)*centerMoment t v (n+1-(k+1))) =
        t i*(∑ k ∈ Finset.range (n+1), t i^k*centerMoment t v (n-k)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [show n+1-(k+1)=n-k by omega, pow_succ]
      ring
    rw [he]
    ring

theorem centerMoment_convolution (t v : ι → ℝ) (n : ℕ) :
    centerMoment t v (n+2) = ∑ k ∈ Finset.range (n+1),
      (∑ i, v i^2*t i^k)*centerMoment t v (n-k) := by
  rw [show n+2 = (n+1)+1 by omega, centerMoment_succ]
  simp_rw [centerOrbit_node_expansion, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end FlatBernoulli
