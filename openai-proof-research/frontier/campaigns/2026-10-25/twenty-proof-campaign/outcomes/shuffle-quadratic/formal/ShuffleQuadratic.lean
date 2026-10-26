import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Tactic

namespace ShuffleQuadratic
open Finset Matrix

/-- Exact binomial transform of an arbitrary quadratic, including rank zero. -/
theorem binomial_quadratic (r : ℕ) (a b c : ℝ) :
    (∑ k ∈ range (r + 1), (r.choose k : ℝ) *
      (a * (k : ℝ)^2 + b * k + c)) =
    (2 : ℝ)^r * (a * r * (r + 1) / 4 + b * r / 2 + c) := by
  induction r generalizing a b c with
  | zero => simp
  | succ r ih =>
    rw [show r + 1 + 1 = r + 2 by omega]
    rw [Finset.sum_choose_succ_mul (fun k _ => a * (k : ℝ)^2 + b * k + c)]
    rw [← sum_add_distrib]
    have he : (∑ k ∈ range (r + 1),
        ((r.choose k : ℝ) * (a * (k : ℝ)^2 + b * k + c) +
        (r.choose k : ℝ) * (a * ((k + 1 : ℕ) : ℝ)^2 + b * (k + 1 : ℕ) + c))) =
        ∑ k ∈ range (r + 1), (r.choose k : ℝ) *
          ((2*a) * (k : ℝ)^2 + (2*a+2*b) * k + (a+b+2*c)) := by
      apply sum_congr rfl
      intro k _
      push_cast
      ring
    rw [he, ih]
    push_cast
    rw [pow_succ]
    ring

/-- Extending beyond the binomial support adds only zeros. -/
theorem binomial_quadratic_extended (n r : ℕ) (hr : r < n) (a b c : ℝ) :
    (∑ k ∈ range n, (r.choose k : ℝ) * (a*(k : ℝ)^2+b*k+c)) =
      (2 : ℝ)^r * (a*r*(r+1)/4+b*r/2+c) := by
  rw [← binomial_quadratic r a b c]
  symm
  apply sum_subset (range_mono (by omega))
  intro k _ hk
  have hrk : r < k := by simp only [mem_range] at hk; omega
  simp [Nat.choose_eq_zero_of_lt hrk]

/-- Source formula at one-based coordinate k, evaluated over the reals. -/
noncomputable def vEntry (n k : ℝ) : ℝ := n^2 - 3*n*k + 3*k*(k+1)/2 - 1

/-- Source matrix with zero-based finite indices: paper i = i.val + 1. -/
noncomputable def positionMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ((i.val.choose j.val : ℝ) + i.val.choose (n-1-j.val)) /
    (2 : ℝ)^(i.val+1)

noncomputable def quadraticVector (n : ℕ) : Fin n → ℝ :=
  fun k => vEntry n (k.val+1)

/-- The reflection is proved at the level of the finite sum. -/
theorem reflected_sum (n r : ℕ) :
    (∑ k ∈ range n, (r.choose (n-1-k) : ℝ) * vEntry n (k+1)) =
      ∑ k ∈ range n, (r.choose k : ℝ) * vEntry n (n-k) := by
  rw [← sum_range_reflect (fun k => (r.choose k : ℝ) * vEntry n (n-k)) n]
  apply sum_congr rfl
  intro k hk
  have hs : k + 1 + (n - 1 - k) = n := by
    have := mem_range.mp hk
    omega
  have hs' : (k : ℝ) + 1 + (n - 1 - k : ℕ) = n := by exact_mod_cast hs
  congr 1
  congr 1
  linarith

/-- Symmetrization in real coordinates; reflection in the finite sum is handled above. -/
theorem quadratic_reflection (n k : ℕ) :
    vEntry n (k+1) + vEntry n (n-k) =
      3*(k : ℝ)^2 + (3*(1-(n : ℝ)))*k + ((n : ℝ)-1)*(n-2)/2 := by
  unfold vEntry
  ring

/-- The undivided row sum is evaluated exactly for every row. -/
theorem row_numerator (n r : ℕ) (hr : r < n) :
    (∑ k ∈ range n, ((r.choose k : ℝ) + r.choose (n-1-k)) * vEntry n (k+1)) =
      (2 : ℝ)^r * vEntry n (r+1) / 2 := by
  simp_rw [add_mul]
  rw [sum_add_distrib, reflected_sum, ← sum_add_distrib]
  simp_rw [← mul_add]
  have he : (∑ k ∈ range n, (r.choose k : ℝ) *
      (vEntry n (k+1) + vEntry n (n-k))) =
      ∑ k ∈ range n, (r.choose k : ℝ) *
        (3*(k : ℝ)^2 + (3*(1-(n : ℝ)))*k + ((n : ℝ)-1)*(n-2)/2) := by
    apply sum_congr rfl
    intro k _
    rw [quadratic_reflection n k]
  rw [he, binomial_quadratic_extended n r hr]
  unfold vEntry
  ring

/-- Equality of the actual finite matrix-vector product. -/
theorem quadratic_mulVec (n : ℕ) :
    positionMatrix n *ᵥ quadraticVector n = (1/4 : ℝ) • quadraticVector n := by
  funext i
  simp only [Matrix.mulVec, dotProduct, positionMatrix, quadraticVector,
    Pi.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun k =>
    ((i.val.choose k : ℝ) + i.val.choose (n-1-k)) / (2 : ℝ)^(i.val+1) *
      vEntry n ((k : ℝ)+1)) n]
  simp_rw [div_mul_eq_mul_div]
  rw [← sum_div, row_numerator n i.val i.isLt]
  rw [pow_succ]
  field_simp
  ring

/-- Its first component is strictly positive for n at least three. -/
theorem first_entry_positive (n : ℕ) (hn : 3 ≤ n) :
    0 < vEntry n 1 := by
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have he : vEntry n 1 = ((n : ℝ)-1)*(n-2) := by unfold vEntry; ring
  rw [he]
  exact mul_pos (by linarith) (by linarith)

theorem quadraticVector_ne_zero (n : ℕ) (hn : 3 ≤ n) : quadraticVector n ≠ 0 := by
  intro hz
  have h := congrFun hz ⟨0, by omega⟩
  have hp := first_entry_positive n hn
  norm_num [quadraticVector] at h
  rw [h] at hp
  exact (lt_irrefl 0) hp

/-- Clay's Conjecture 1, expressed using mathlib's nonzero eigenvector predicate. -/
theorem quadratic_hasEigenvector (n : ℕ) (hn : 3 ≤ n) :
    Module.End.HasEigenvector (positionMatrix n).toLin' (1/4 : ℝ) (quadraticVector n) := by
  apply Module.End.hasEigenvector_iff.mpr
  constructor
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact quadratic_mulVec n
  · exact quadraticVector_ne_zero n hn

theorem quarter_hasEigenvalue (n : ℕ) (hn : 3 ≤ n) :
    Module.End.HasEigenvalue (positionMatrix n).toLin' (1/4 : ℝ) :=
  (quadratic_hasEigenvector n hn).hasUnifEigenvalue

/-- The geometric multiplicity is at least one. -/
theorem quarter_eigenspace_dimension (n : ℕ) (hn : 3 ≤ n) :
    1 ≤ Module.finrank ℝ (Module.End.eigenspace (positionMatrix n).toLin' (1/4 : ℝ)) := by
  have he := quarter_hasEigenvalue n hn
  rw [Module.End.hasEigenvalue_iff] at he
  have hd := (Module.finrank_pos_iff (R := ℝ)).mpr (Submodule.nontrivial_iff_ne_bot.mpr he)
  exact hd

/-- Explicit agreement with the paper's one-based entry formula. -/
theorem positionMatrix_one_based (n i j : ℕ)
    (hi : 1 ≤ i ∧ i ≤ n) (hj : 1 ≤ j ∧ j ≤ n) :
    positionMatrix n ⟨i-1, by omega⟩ ⟨j-1, by omega⟩ =
      ((Nat.choose (i-1) (j-1) : ℝ) + Nat.choose (i-1) (n-j)) / (2 : ℝ)^i := by
  have he : n - 1 - (j - 1) = n - j := by omega
  simp only [positionMatrix, he, Nat.sub_add_cancel hi.1]

theorem quadraticVector_one_based (n k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) :
    quadraticVector n ⟨k-1, by omega⟩ =
      (n : ℝ)^2 - 3*n*k + 3*k*(k+1)/2 - 1 := by
  have he : ((k-1 : ℕ) : ℝ) + 1 = k := by
    exact_mod_cast (Nat.sub_add_cancel hk.1)
  simp only [quadraticVector, he, vEntry]

end ShuffleQuadratic
