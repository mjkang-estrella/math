import Mathlib.Tactic
import BitEncoding
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
set_option linter.unusedSimpArgs false
namespace Nut8
lemma list_range_sum (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

lemma row_list_sum (m n : ℕ) (f : ℕ → ℕ → ℕ) :
    ((List.range m).flatMap (fun i => (List.range n).map (f i))).sum =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, f i j := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, Finset.sum_range_succ, ih, list_range_sum]

lemma row_sum (m n : ℕ) (f : ℕ → ℕ) :
    (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, f (i*n+j)) =
      ∑ k ∈ Finset.range (m*n), f k := by
  simp_rw [Finset.sum_range]
  rw [← Fintype.sum_prod_type (fun p : Fin m × Fin n => f (p.1.val*n+p.2.val))]
  convert Equiv.sum_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m*n))
    (fun k : Fin (m*n) => f k.val) using 1;
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

/-- Row-major encoding is a binary word, with no carries between cells. -/
lemma row_encode (n : ℕ) (b : ℕ → Bool) :
    ((List.range n).flatMap (fun i => (List.range n).map
      (fun j => if b (i*n+j) then 2^(i*n+j) else 0))).sum = encodeBits (n*n) b := by
  rw [row_list_sum]
  exact row_sum n n (fun k => if b k then 2^k else 0)

lemma row_encode_testBit (n : ℕ) (b : ℕ → Bool) (i j : ℕ)
    (hi : i < n) (hj : j < n) :
    (((List.range n).flatMap (fun r => (List.range n).map
      (fun c => if b (r*n+c) then 2^(r*n+c) else 0))).sum).testBit (i*n+j) = b (i*n+j) := by
  rw [row_encode, encodeBits_testBit]
  have hk : i*n+j < n*n := by nlinarith
  simp [hk]
end Nut8
