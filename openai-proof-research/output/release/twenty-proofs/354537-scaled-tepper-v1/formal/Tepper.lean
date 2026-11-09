import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic

open Polynomial Finset
open scoped BigOperators
namespace ScaledTepper

/-- The alternating signs agree after multiplication by the outer parity. -/
theorem sign_identity (n k : ℕ) (hk : k ≤ n) :
    (-1 : ℝ)^n * (-1 : ℝ)^(n-k) = (-1 : ℝ)^k := by
  have he : n + (n-k) = 2*(n-k)+k := by omega
  rw [← pow_add, he, pow_add, pow_mul]
  norm_num

/-- A real polynomial evaluated at an affine progression satisfies the scaled identity. -/
theorem scaled_identity (P : ℝ[X]) (x l : ℝ) (hl : l ≠ 0) :
    (∑ k ∈ range (P.natDegree + 1), (-1 : ℝ)^k * (P.natDegree.choose k : ℝ) *
      P.eval (x-l*k)) = P.leadingCoeff * l^P.natDegree * (P.natDegree.factorial : ℝ) := by
  let q : ℝ[X] := C (-l) * X + C x
  let Q := P.comp q
  have hq : q.natDegree = 1 := natDegree_linear (neg_ne_zero.mpr hl)
  have hc : q.leadingCoeff = -l := leadingCoeff_linear (neg_ne_zero.mpr hl)
  have hd : Q.natDegree = P.natDegree := by
    dsimp [Q]
    rw [natDegree_comp, hq, mul_one]
  have hQ : Q.leadingCoeff = P.leadingCoeff * (-l)^P.natDegree := by
    dsimp [Q]
    rw [leadingCoeff_comp (by omega : q.natDegree ≠ 0), hc]
  have H := congrFun Q.fwdDiff_iter_degree_eq_factorial 0
  rw [hd, fwdDiff_iter_eq_sum_shift] at H
  simp only [Q, q, eval_comp, eval_add, eval_mul, eval_C, eval_X,
    zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul, Int.cast_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast,
    Pi.smul_apply, Pi.natCast_apply, smul_eq_mul] at H
  have H' := congrArg (fun v : ℝ => (-1 : ℝ)^P.natDegree * v) H
  rw [Finset.mul_sum] at H'
  have heval (k : ℕ) : -l * (k : ℝ) + x = x-l*k := by ring
  simp_rw [heval] at H'
  have hs : (∑ k ∈ range (P.natDegree+1), (-1 : ℝ)^P.natDegree *
      (((-1 : ℝ)^(P.natDegree-k) * (P.natDegree.choose k : ℝ)) * P.eval (x-l*k))) =
      ∑ k ∈ range (P.natDegree+1), (-1 : ℝ)^k * (P.natDegree.choose k : ℝ) *
        P.eval (x-l*k) := by
    apply sum_congr rfl
    intro k hk
    rw [← mul_assoc, ← mul_assoc, sign_identity _ _ (by have := mem_range.mp hk; omega)]
  rw [hs] at H'
  rw [hQ] at H'
  have hn : (-1 : ℝ)^P.natDegree * (-l)^P.natDegree = l^P.natDegree := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    _ = (-1 : ℝ)^P.natDegree *
        (P.leadingCoeff * (-l)^P.natDegree * (P.natDegree.factorial : ℝ)) := H'
    _ = P.leadingCoeff * ((-1 : ℝ)^P.natDegree * (-l)^P.natDegree) *
        (P.natDegree.factorial : ℝ) := by ring
    _ = _ := by rw [hn]

/-- Exact positive-integer step version of Conjecture 4.5 / MathDB 354537. -/
theorem mathdb354537 (P : ℝ[X]) (n l : ℕ) (hl : 0 < l)
    (hn : P.natDegree = n) (x : ℝ) :
    (∑ k ∈ range (n + 1), (-1 : ℝ)^k * (n.choose k : ℝ) *
      P.eval (x-(l : ℝ)*k)) = P.leadingCoeff * (l : ℝ)^n * (n.factorial : ℝ) := by
  simpa only [hn] using scaled_identity P x (l : ℝ) (by exact_mod_cast hl.ne')

end ScaledTepper
