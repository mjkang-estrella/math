import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
namespace Riordan
open Polynomial Finset
-- Natural coefficients; reduction modulo 2 gives the source's binary Riordan array.
def gc (n : ℕ) : ℕ := if n ∈ ([0,1,3,6,7,8,12,13] : List ℕ) then 1 else 0
noncomputable def g : Polynomial ℕ := ∑ i ∈ range 14, monomial i (gc i)
theorem g_coeff (n : ℕ) : g.coeff n = gc n := by
  simp only [g, finsetSum_coeff, coeff_monomial]
  by_cases h : n < 14
  · simp [Finset.sum_ite_eq', h]
  · simp [Finset.sum_ite_eq', h, gc]
    omega

def pc : ℕ → ℕ → ℕ
| 0, n => if n = 0 then 1 else 0
| k+1, n => ∑ i ∈ range (n+1), gc i * pc k (n-i)

theorem pc_coeff (k n : ℕ) : pc k n = (g^k).coeff n := by
  induction k generalizing n with
  | zero => simp [pc, Polynomial.coeff_one]
  | succ k ih =>
    rw [pow_succ']
    simp only [pc, coeff_mul, g_coeff, ← ih]
    exact (Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => gc i * pc k j) n).symm
theorem pc_0_0 : pc 0 0 = 1 := by
  decide

theorem pc_0_1 : pc 0 1 = 0 := by
  norm_num [pc, sum_range_succ, gc]
theorem pc_0_2 : pc 0 2 = 0 := by
  norm_num [pc, sum_range_succ, gc]
theorem pc_0_3 : pc 0 3 = 0 := by
  norm_num [pc, sum_range_succ, gc]
theorem pc_0_4 : pc 0 4 = 0 := by
  norm_num [pc, sum_range_succ, gc]
theorem pc_0_5 : pc 0 5 = 0 := by
  norm_num [pc, sum_range_succ, gc]
theorem pc_0_6 : pc 0 6 = 0 := by
  norm_num [pc, sum_range_succ, gc]
theorem pc_0_7 : pc 0 7 = 0 := by
  norm_num [pc, sum_range_succ, gc]
theorem pc_0_8 : pc 0 8 = 0 := by
  norm_num [pc, sum_range_succ, gc]
theorem pc_0_9 : pc 0 9 = 0 := by
  norm_num [pc, sum_range_succ, gc]
theorem pc_0_10 : pc 0 10 = 0 := by
  norm_num [pc, sum_range_succ, gc]
theorem pc_0_11 : pc 0 11 = 0 := by
  norm_num [pc, sum_range_succ, gc]
theorem pc_0_12 : pc 0 12 = 0 := by
  norm_num [pc, sum_range_succ, gc]
theorem pc_0_13 : pc 0 13 = 0 := by
  norm_num [pc, sum_range_succ, gc]
theorem pc_1_0 : pc 1 0 = 1 := by
  decide

theorem pc_1_1 : pc 1 1 = 1 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_0_0, pc_0_1]
theorem pc_1_2 : pc 1 2 = 0 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_0_0, pc_0_1, pc_0_2]
theorem pc_1_3 : pc 1 3 = 1 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_0_0, pc_0_1, pc_0_2, pc_0_3]
theorem pc_1_4 : pc 1 4 = 0 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_0_0, pc_0_1, pc_0_2, pc_0_3, pc_0_4]
theorem pc_1_5 : pc 1 5 = 0 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_0_0, pc_0_1, pc_0_2, pc_0_3, pc_0_4, pc_0_5]
theorem pc_1_6 : pc 1 6 = 1 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_0_0, pc_0_1, pc_0_2, pc_0_3, pc_0_4, pc_0_5, pc_0_6]
theorem pc_1_7 : pc 1 7 = 1 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_0_0, pc_0_1, pc_0_2, pc_0_3, pc_0_4, pc_0_5, pc_0_6, pc_0_7]
theorem pc_1_8 : pc 1 8 = 1 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_0_0, pc_0_1, pc_0_2, pc_0_3, pc_0_4, pc_0_5, pc_0_6, pc_0_7, pc_0_8]
theorem pc_1_9 : pc 1 9 = 0 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_0_0, pc_0_1, pc_0_2, pc_0_3, pc_0_4, pc_0_5, pc_0_6, pc_0_7, pc_0_8, pc_0_9]
theorem pc_1_10 : pc 1 10 = 0 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_0_0, pc_0_1, pc_0_2, pc_0_3, pc_0_4, pc_0_5, pc_0_6, pc_0_7, pc_0_8, pc_0_9, pc_0_10]
theorem pc_1_11 : pc 1 11 = 0 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_0_0, pc_0_1, pc_0_2, pc_0_3, pc_0_4, pc_0_5, pc_0_6, pc_0_7, pc_0_8, pc_0_9, pc_0_10, pc_0_11]
theorem pc_1_12 : pc 1 12 = 1 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_0_0, pc_0_1, pc_0_2, pc_0_3, pc_0_4, pc_0_5, pc_0_6, pc_0_7, pc_0_8, pc_0_9, pc_0_10, pc_0_11, pc_0_12]
theorem pc_1_13 : pc 1 13 = 1 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_0_0, pc_0_1, pc_0_2, pc_0_3, pc_0_4, pc_0_5, pc_0_6, pc_0_7, pc_0_8, pc_0_9, pc_0_10, pc_0_11, pc_0_12, pc_0_13]
theorem pc_2_0 : pc 2 0 = 1 := by
  decide

theorem pc_2_1 : pc 2 1 = 2 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_1_0, pc_1_1]
theorem pc_2_2 : pc 2 2 = 1 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_1_0, pc_1_1, pc_1_2]
theorem pc_2_3 : pc 2 3 = 2 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_1_0, pc_1_1, pc_1_2, pc_1_3]
theorem pc_2_4 : pc 2 4 = 2 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_1_0, pc_1_1, pc_1_2, pc_1_3, pc_1_4]
theorem pc_2_5 : pc 2 5 = 0 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_1_0, pc_1_1, pc_1_2, pc_1_3, pc_1_4, pc_1_5]
theorem pc_2_6 : pc 2 6 = 3 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_1_0, pc_1_1, pc_1_2, pc_1_3, pc_1_4, pc_1_5, pc_1_6]
theorem pc_2_7 : pc 2 7 = 4 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_1_0, pc_1_1, pc_1_2, pc_1_3, pc_1_4, pc_1_5, pc_1_6, pc_1_7]
theorem pc_2_8 : pc 2 8 = 4 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_1_0, pc_1_1, pc_1_2, pc_1_3, pc_1_4, pc_1_5, pc_1_6, pc_1_7, pc_1_8]
theorem pc_2_9 : pc 2 9 = 4 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_1_0, pc_1_1, pc_1_2, pc_1_3, pc_1_4, pc_1_5, pc_1_6, pc_1_7, pc_1_8, pc_1_9]
theorem pc_2_10 : pc 2 10 = 2 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_1_0, pc_1_1, pc_1_2, pc_1_3, pc_1_4, pc_1_5, pc_1_6, pc_1_7, pc_1_8, pc_1_9, pc_1_10]
theorem pc_2_11 : pc 2 11 = 2 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_1_0, pc_1_1, pc_1_2, pc_1_3, pc_1_4, pc_1_5, pc_1_6, pc_1_7, pc_1_8, pc_1_9, pc_1_10, pc_1_11]
theorem pc_2_12 : pc 2 12 = 3 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_1_0, pc_1_1, pc_1_2, pc_1_3, pc_1_4, pc_1_5, pc_1_6, pc_1_7, pc_1_8, pc_1_9, pc_1_10, pc_1_11, pc_1_12]
theorem pc_3_0 : pc 3 0 = 1 := by
  decide

theorem pc_3_1 : pc 3 1 = 3 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_2_0, pc_2_1]
theorem pc_3_2 : pc 3 2 = 3 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_2_0, pc_2_1, pc_2_2]
theorem pc_3_3 : pc 3 3 = 4 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_2_0, pc_2_1, pc_2_2, pc_2_3]
theorem pc_3_4 : pc 3 4 = 6 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_2_0, pc_2_1, pc_2_2, pc_2_3, pc_2_4]
theorem pc_3_5 : pc 3 5 = 3 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_2_0, pc_2_1, pc_2_2, pc_2_3, pc_2_4, pc_2_5]
theorem pc_3_6 : pc 3 6 = 6 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_2_0, pc_2_1, pc_2_2, pc_2_3, pc_2_4, pc_2_5, pc_2_6]
theorem pc_3_7 : pc 3 7 = 12 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_2_0, pc_2_1, pc_2_2, pc_2_3, pc_2_4, pc_2_5, pc_2_6, pc_2_7]
theorem pc_3_8 : pc 3 8 = 12 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_2_0, pc_2_1, pc_2_2, pc_2_3, pc_2_4, pc_2_5, pc_2_6, pc_2_7, pc_2_8]
theorem pc_3_9 : pc 3 9 = 16 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_2_0, pc_2_1, pc_2_2, pc_2_3, pc_2_4, pc_2_5, pc_2_6, pc_2_7, pc_2_8, pc_2_9]
theorem pc_3_10 : pc 3 10 = 15 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_2_0, pc_2_1, pc_2_2, pc_2_3, pc_2_4, pc_2_5, pc_2_6, pc_2_7, pc_2_8, pc_2_9, pc_2_10]
theorem pc_3_11 : pc 3 11 = 12 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_2_0, pc_2_1, pc_2_2, pc_2_3, pc_2_4, pc_2_5, pc_2_6, pc_2_7, pc_2_8, pc_2_9, pc_2_10, pc_2_11]
theorem pc_4_0 : pc 4 0 = 1 := by
  decide

theorem pc_4_1 : pc 4 1 = 4 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_3_0, pc_3_1]
theorem pc_4_2 : pc 4 2 = 6 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_3_0, pc_3_1, pc_3_2]
theorem pc_4_3 : pc 4 3 = 8 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_3_0, pc_3_1, pc_3_2, pc_3_3]
theorem pc_4_4 : pc 4 4 = 13 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_3_0, pc_3_1, pc_3_2, pc_3_3, pc_3_4]
theorem pc_4_5 : pc 4 5 = 12 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_3_0, pc_3_1, pc_3_2, pc_3_3, pc_3_4, pc_3_5]
theorem pc_4_6 : pc 4 6 = 14 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_3_0, pc_3_1, pc_3_2, pc_3_3, pc_3_4, pc_3_5, pc_3_6]
theorem pc_4_7 : pc 4 7 = 28 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_3_0, pc_3_1, pc_3_2, pc_3_3, pc_3_4, pc_3_5, pc_3_6, pc_3_7]
theorem pc_4_8 : pc 4 8 = 34 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_3_0, pc_3_1, pc_3_2, pc_3_3, pc_3_4, pc_3_5, pc_3_6, pc_3_7, pc_3_8]
theorem pc_4_9 : pc 4 9 = 44 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_3_0, pc_3_1, pc_3_2, pc_3_3, pc_3_4, pc_3_5, pc_3_6, pc_3_7, pc_3_8, pc_3_9]
theorem pc_4_10 : pc 4 10 = 56 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_3_0, pc_3_1, pc_3_2, pc_3_3, pc_3_4, pc_3_5, pc_3_6, pc_3_7, pc_3_8, pc_3_9, pc_3_10]
theorem pc_5_0 : pc 5 0 = 1 := by
  decide

theorem pc_5_1 : pc 5 1 = 5 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_4_0, pc_4_1]
theorem pc_5_2 : pc 5 2 = 10 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_4_0, pc_4_1, pc_4_2]
theorem pc_5_3 : pc 5 3 = 15 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_4_0, pc_4_1, pc_4_2, pc_4_3]
theorem pc_5_4 : pc 5 4 = 25 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_4_0, pc_4_1, pc_4_2, pc_4_3, pc_4_4]
theorem pc_5_5 : pc 5 5 = 31 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_4_0, pc_4_1, pc_4_2, pc_4_3, pc_4_4, pc_4_5]
theorem pc_5_6 : pc 5 6 = 35 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_4_0, pc_4_1, pc_4_2, pc_4_3, pc_4_4, pc_4_5, pc_4_6]
theorem pc_5_7 : pc 5 7 = 60 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_4_0, pc_4_1, pc_4_2, pc_4_3, pc_4_4, pc_4_5, pc_4_6, pc_4_7]
theorem pc_5_8 : pc 5 8 = 85 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_4_0, pc_4_1, pc_4_2, pc_4_3, pc_4_4, pc_4_5, pc_4_6, pc_4_7, pc_4_8]
theorem pc_5_9 : pc 5 9 = 110 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_4_0, pc_4_1, pc_4_2, pc_4_3, pc_4_4, pc_4_5, pc_4_6, pc_4_7, pc_4_8, pc_4_9]
theorem pc_6_0 : pc 6 0 = 1 := by
  decide

theorem pc_6_1 : pc 6 1 = 6 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_5_0, pc_5_1]
theorem pc_6_2 : pc 6 2 = 15 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_5_0, pc_5_1, pc_5_2]
theorem pc_6_3 : pc 6 3 = 26 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_5_0, pc_5_1, pc_5_2, pc_5_3]
theorem pc_6_4 : pc 6 4 = 45 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_5_0, pc_5_1, pc_5_2, pc_5_3, pc_5_4]
theorem pc_6_5 : pc 6 5 = 66 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_5_0, pc_5_1, pc_5_2, pc_5_3, pc_5_4, pc_5_5]
theorem pc_6_6 : pc 6 6 = 82 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_5_0, pc_5_1, pc_5_2, pc_5_3, pc_5_4, pc_5_5, pc_5_6]
theorem pc_6_7 : pc 6 7 = 126 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_5_0, pc_5_1, pc_5_2, pc_5_3, pc_5_4, pc_5_5, pc_5_6, pc_5_7]
theorem pc_6_8 : pc 6 8 = 192 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_5_0, pc_5_1, pc_5_2, pc_5_3, pc_5_4, pc_5_5, pc_5_6, pc_5_7, pc_5_8]
theorem pc_7_0 : pc 7 0 = 1 := by
  decide

theorem pc_7_1 : pc 7 1 = 7 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_6_0, pc_6_1]
theorem pc_7_2 : pc 7 2 = 21 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_6_0, pc_6_1, pc_6_2]
theorem pc_7_3 : pc 7 3 = 42 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_6_0, pc_6_1, pc_6_2, pc_6_3]
theorem pc_7_4 : pc 7 4 = 77 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_6_0, pc_6_1, pc_6_2, pc_6_3, pc_6_4]
theorem pc_7_5 : pc 7 5 = 126 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_6_0, pc_6_1, pc_6_2, pc_6_3, pc_6_4, pc_6_5]
theorem pc_7_6 : pc 7 6 = 175 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_6_0, pc_6_1, pc_6_2, pc_6_3, pc_6_4, pc_6_5, pc_6_6]
theorem pc_7_7 : pc 7 7 = 260 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_6_0, pc_6_1, pc_6_2, pc_6_3, pc_6_4, pc_6_5, pc_6_6, pc_6_7]
theorem pc_8_0 : pc 8 0 = 1 := by
  decide

theorem pc_8_1 : pc 8 1 = 8 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_7_0, pc_7_1]
theorem pc_8_2 : pc 8 2 = 28 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_7_0, pc_7_1, pc_7_2]
theorem pc_8_3 : pc 8 3 = 64 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_7_0, pc_7_1, pc_7_2, pc_7_3]
theorem pc_8_4 : pc 8 4 = 126 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_7_0, pc_7_1, pc_7_2, pc_7_3, pc_7_4]
theorem pc_8_5 : pc 8 5 = 224 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_7_0, pc_7_1, pc_7_2, pc_7_3, pc_7_4, pc_7_5]
theorem pc_8_6 : pc 8 6 = 344 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_7_0, pc_7_1, pc_7_2, pc_7_3, pc_7_4, pc_7_5, pc_7_6]
theorem pc_9_0 : pc 9 0 = 1 := by
  decide

theorem pc_9_1 : pc 9 1 = 9 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_8_0, pc_8_1]
theorem pc_9_2 : pc 9 2 = 36 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_8_0, pc_8_1, pc_8_2]
theorem pc_9_3 : pc 9 3 = 93 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_8_0, pc_8_1, pc_8_2, pc_8_3]
theorem pc_9_4 : pc 9 4 = 198 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_8_0, pc_8_1, pc_8_2, pc_8_3, pc_8_4]
theorem pc_9_5 : pc 9 5 = 378 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_8_0, pc_8_1, pc_8_2, pc_8_3, pc_8_4, pc_8_5]
theorem pc_10_0 : pc 10 0 = 1 := by
  decide

theorem pc_10_1 : pc 10 1 = 10 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_9_0, pc_9_1]
theorem pc_10_2 : pc 10 2 = 45 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_9_0, pc_9_1, pc_9_2]
theorem pc_10_3 : pc 10 3 = 130 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_9_0, pc_9_1, pc_9_2, pc_9_3]
theorem pc_10_4 : pc 10 4 = 300 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_9_0, pc_9_1, pc_9_2, pc_9_3, pc_9_4]
theorem pc_11_0 : pc 11 0 = 1 := by
  decide

theorem pc_11_1 : pc 11 1 = 11 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_10_0, pc_10_1]
theorem pc_11_2 : pc 11 2 = 55 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_10_0, pc_10_1, pc_10_2]
theorem pc_11_3 : pc 11 3 = 176 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_10_0, pc_10_1, pc_10_2, pc_10_3]
theorem pc_12_0 : pc 12 0 = 1 := by
  decide

theorem pc_12_1 : pc 12 1 = 12 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_11_0, pc_11_1]
theorem pc_12_2 : pc 12 2 = 66 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_11_0, pc_11_1, pc_11_2]
theorem pc_13_0 : pc 13 0 = 1 := by
  decide

theorem pc_13_1 : pc 13 1 = 13 := by
  rw [pc]
  norm_num [sum_range_succ, gc, pc_12_0, pc_12_1]
theorem pc_14_0 : pc 14 0 = 1 := by
  decide

-- The coefficient formula is Definition 2.2, in zero-based vertex indices:
-- [z^(i-j-1)] g^(j+1), reduced modulo 2.
def entry (i j : ℕ) : ℕ :=
  if i = j then 0 else pc (min i j + 1) (max i j - min i j - 1) % 2
noncomputable def sourceEntry (i j : ℕ) : ℕ :=
  if i = j then 0 else (g ^ (min i j + 1)).coeff (max i j - min i j - 1) % 2
theorem entry_source (i j : ℕ) : entry i j = sourceEntry i j := by
  simp only [entry, sourceEntry, pc_coeff]

def A : Fin 15 → Fin 15 → ℤ := fun i j => entry i j

def x : Fin 15 → ℤ := ![-1,1,0,0,-1,1,0,1,1,-2,0,1,1,-1,1]
theorem entries : ∀ i j : Fin 15, entry i j = ![![0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1], ![1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], ![1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0], ![0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0], ![1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0], ![0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1], ![1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]] i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [entry, pc_0_0, pc_0_1, pc_0_2, pc_0_3, pc_0_4, pc_0_5, pc_0_6, pc_0_7, pc_0_8, pc_0_9, pc_0_10, pc_0_11, pc_0_12, pc_0_13, pc_1_0, pc_1_1, pc_1_2, pc_1_3, pc_1_4, pc_1_5, pc_1_6, pc_1_7, pc_1_8, pc_1_9, pc_1_10, pc_1_11, pc_1_12, pc_1_13, pc_2_0, pc_2_1, pc_2_2, pc_2_3, pc_2_4, pc_2_5, pc_2_6, pc_2_7, pc_2_8, pc_2_9, pc_2_10, pc_2_11, pc_2_12, pc_3_0, pc_3_1, pc_3_2, pc_3_3, pc_3_4, pc_3_5, pc_3_6, pc_3_7, pc_3_8, pc_3_9, pc_3_10, pc_3_11, pc_4_0, pc_4_1, pc_4_2, pc_4_3, pc_4_4, pc_4_5, pc_4_6, pc_4_7, pc_4_8, pc_4_9, pc_4_10, pc_5_0, pc_5_1, pc_5_2, pc_5_3, pc_5_4, pc_5_5, pc_5_6, pc_5_7, pc_5_8, pc_5_9, pc_6_0, pc_6_1, pc_6_2, pc_6_3, pc_6_4, pc_6_5, pc_6_6, pc_6_7, pc_6_8, pc_7_0, pc_7_1, pc_7_2, pc_7_3, pc_7_4, pc_7_5, pc_7_6, pc_7_7, pc_8_0, pc_8_1, pc_8_2, pc_8_3, pc_8_4, pc_8_5, pc_8_6, pc_9_0, pc_9_1, pc_9_2, pc_9_3, pc_9_4, pc_9_5, pc_10_0, pc_10_1, pc_10_2, pc_10_3, pc_10_4, pc_11_0, pc_11_1, pc_11_2, pc_11_3, pc_12_0, pc_12_1, pc_12_2, pc_13_0, pc_13_1, pc_14_0]

theorem kernel : ∀ i : Fin 15, ∑ j : Fin 15, A i j * x j = 0 := by
  intro i
  fin_cases i <;> norm_num [A, entries, x, Fin.sum_univ_succ]
theorem odd_nonzero : x 0 ≠ 0 := by decide
-- Even source vertices are odd zero-based indices; their induced graph is null.
theorem even_independent : ∀ i j : Fin 7, entry (2*i.val+1) (2*j.val+1) = 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [entry, pc_0_0, pc_0_1, pc_0_2, pc_0_3, pc_0_4, pc_0_5, pc_0_6, pc_0_7, pc_0_8, pc_0_9, pc_0_10, pc_0_11, pc_0_12, pc_0_13, pc_1_0, pc_1_1, pc_1_2, pc_1_3, pc_1_4, pc_1_5, pc_1_6, pc_1_7, pc_1_8, pc_1_9, pc_1_10, pc_1_11, pc_1_12, pc_1_13, pc_2_0, pc_2_1, pc_2_2, pc_2_3, pc_2_4, pc_2_5, pc_2_6, pc_2_7, pc_2_8, pc_2_9, pc_2_10, pc_2_11, pc_2_12, pc_3_0, pc_3_1, pc_3_2, pc_3_3, pc_3_4, pc_3_5, pc_3_6, pc_3_7, pc_3_8, pc_3_9, pc_3_10, pc_3_11, pc_4_0, pc_4_1, pc_4_2, pc_4_3, pc_4_4, pc_4_5, pc_4_6, pc_4_7, pc_4_8, pc_4_9, pc_4_10, pc_5_0, pc_5_1, pc_5_2, pc_5_3, pc_5_4, pc_5_5, pc_5_6, pc_5_7, pc_5_8, pc_5_9, pc_6_0, pc_6_1, pc_6_2, pc_6_3, pc_6_4, pc_6_5, pc_6_6, pc_6_7, pc_6_8, pc_7_0, pc_7_1, pc_7_2, pc_7_3, pc_7_4, pc_7_5, pc_7_6, pc_7_7, pc_8_0, pc_8_1, pc_8_2, pc_8_3, pc_8_4, pc_8_5, pc_8_6, pc_9_0, pc_9_1, pc_9_2, pc_9_3, pc_9_4, pc_9_5, pc_10_0, pc_10_1, pc_10_2, pc_10_3, pc_10_4, pc_11_0, pc_11_1, pc_11_2, pc_11_3, pc_12_0, pc_12_1, pc_12_2, pc_13_0, pc_13_1, pc_14_0]
-- Odd source vertices induce exactly the smaller Riordan graph for the SAME g.
theorem odd_copy : ∀ i j : Fin 8, entry (2*i.val) (2*j.val) = entry i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [entry, pc_0_0, pc_0_1, pc_0_2, pc_0_3, pc_0_4, pc_0_5, pc_0_6, pc_0_7, pc_0_8, pc_0_9, pc_0_10, pc_0_11, pc_0_12, pc_0_13, pc_1_0, pc_1_1, pc_1_2, pc_1_3, pc_1_4, pc_1_5, pc_1_6, pc_1_7, pc_1_8, pc_1_9, pc_1_10, pc_1_11, pc_1_12, pc_1_13, pc_2_0, pc_2_1, pc_2_2, pc_2_3, pc_2_4, pc_2_5, pc_2_6, pc_2_7, pc_2_8, pc_2_9, pc_2_10, pc_2_11, pc_2_12, pc_3_0, pc_3_1, pc_3_2, pc_3_3, pc_3_4, pc_3_5, pc_3_6, pc_3_7, pc_3_8, pc_3_9, pc_3_10, pc_3_11, pc_4_0, pc_4_1, pc_4_2, pc_4_3, pc_4_4, pc_4_5, pc_4_6, pc_4_7, pc_4_8, pc_4_9, pc_4_10, pc_5_0, pc_5_1, pc_5_2, pc_5_3, pc_5_4, pc_5_5, pc_5_6, pc_5_7, pc_5_8, pc_5_9, pc_6_0, pc_6_1, pc_6_2, pc_6_3, pc_6_4, pc_6_5, pc_6_6, pc_6_7, pc_6_8, pc_7_0, pc_7_1, pc_7_2, pc_7_3, pc_7_4, pc_7_5, pc_7_6, pc_7_7, pc_8_0, pc_8_1, pc_8_2, pc_8_3, pc_8_4, pc_8_5, pc_8_6, pc_9_0, pc_9_1, pc_9_2, pc_9_3, pc_9_4, pc_9_5, pc_10_0, pc_10_1, pc_10_2, pc_10_3, pc_10_4, pc_11_0, pc_11_1, pc_11_2, pc_11_3, pc_12_0, pc_12_1, pc_12_2, pc_13_0, pc_13_1, pc_14_0]

-- Literal source conjecture: for every proper Bell-type Riordan coefficient sequence,
-- finite io-decomposability forces the odd coordinates of each zero eigenvector to vanish.
-- We specialize its universal quantifier only to the explicit polynomial g.
theorem refutation :
    g.coeff 0 = 1 ∧
    (∀ i j : Fin 7, sourceEntry (2*i.val+1) (2*j.val+1) = 0) ∧
    (∀ i j : Fin 8, sourceEntry (2*i.val) (2*j.val) = sourceEntry i j) ∧
    (∃ v : Fin 15 → ℤ, (∀ i : Fin 15, ∑ j : Fin 15,
      (sourceEntry i j : ℤ) * v j = 0) ∧ v 0 ≠ 0) := by
  refine ⟨by norm_num [g_coeff, gc], ?_, ?_, x, ?_, odd_nonzero⟩
  · simpa only [← entry_source] using even_independent
  · simpa only [← entry_source] using odd_copy
  · simpa only [← entry_source, A] using kernel

-- Literal binary Riordan matrix B(z*g,z*g), symmetrized as Definition 2.2.
noncomputable def bell (p : Polynomial ℕ) (i j : ℕ) : ℕ :=
  if i = j then 0 else ((X*p)^(min i j + 1)).coeff (max i j) % 2

theorem bell_source (i j : ℕ) : bell g i j = sourceEntry i j := by
  by_cases h : i = j
  · simp [bell, sourceEntry, h]
  · have hm : min i j + 1 ≤ max i j := by omega
    simp only [bell, sourceEntry, h, if_false, mul_pow, coeff_X_pow_mul', hm, if_true]
    congr 2 <;> omega

def xR : Fin 15 → ℝ := fun i => x i

theorem kernelR : ∀ i : Fin 15, ∑ j : Fin 15, (entry i j : ℝ) * xR j = 0 := by
  intro i
  fin_cases i <;> norm_num [entries, xR, x, Fin.sum_univ_succ]

def SourceConjecture : Prop := ∀ (p : Polynomial ℕ) (n : ℕ), p.coeff 0 % 2 = 1 →
  (∀ i j : Fin (n/2), bell p (2*i.val+1) (2*j.val+1) = 0) →
  (∀ i j : Fin ((n+1)/2), bell p (2*i.val) (2*j.val) = bell p i j) →
  ∀ v : Fin n → ℝ, (∃ k, v k ≠ 0) →
  (∀ i, ∑ j : Fin n, (bell p i j : ℝ) * v j = 0) →
  ∀ i : Fin ((n+1)/2), v ⟨2*i.val, by omega⟩ = 0

theorem source_conjecture_false : ¬ SourceConjecture := by
  intro H
  have hp : g.coeff 0 % 2 = 1 := by norm_num [g_coeff, gc]
  have he : ∀ i j : Fin (15/2), bell g (2*i.val+1) (2*j.val+1) = 0 := by
    simpa only [bell_source, ← entry_source] using even_independent
  have ho : ∀ i j : Fin ((15+1)/2), bell g (2*i.val) (2*j.val) = bell g i j := by
    simpa only [bell_source, ← entry_source] using odd_copy
  have hv : ∃ k, xR k ≠ 0 := ⟨0, by norm_num [xR, x]⟩
  have hk : ∀ i : Fin 15, ∑ j : Fin 15, (bell g i j : ℝ) * xR j = 0 := by
    simpa only [bell_source, ← entry_source] using kernelR
  have bad := H g 15 hp he ho xR hv hk (0 : Fin 8)
  norm_num [xR, x] at bad

#print axioms source_conjecture_false
end Riordan
