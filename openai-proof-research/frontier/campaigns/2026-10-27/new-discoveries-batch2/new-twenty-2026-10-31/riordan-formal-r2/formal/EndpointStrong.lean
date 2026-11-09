import Endpoint
import InfiniteFamily
namespace Riordan
open Finset Polynomial

-- Truncation to a finite polynomial does not alter any coefficient used below.
noncomputable def seriesTrunc (a : ℕ → ℤ) (D : ℕ) : Polynomial ℤ :=
  ∑ i ∈ range (D+1), monomial i (a i)

theorem seriesTrunc_coeff (a : ℕ → ℤ) (D d : ℕ) (hd : d ≤ D) :
    (seriesTrunc a D).coeff d = a d := by
  simp [seriesTrunc, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq',
    show d < D+1 by omega]

theorem seriesPow_trunc (a : ℕ → ℤ) (D k d : ℕ) (hd : d ≤ D) :
    seriesPow a k d = ((seriesTrunc a D)^k).coeff d := by
  induction k generalizing d with
  | zero => simp [seriesPow, Polynomial.coeff_one]
  | succ k ih =>
    rw [pow_succ', coeff_mul]
    rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (seriesTrunc a D).coeff i * ((seriesTrunc a D)^k).coeff j) d]
    rw [seriesPow_succ]
    apply sum_congr rfl
    intro i hi
    rw [seriesTrunc_coeff a D i (by have := mem_range.mp hi; omega),
      ih (d-i) (by omega)]

-- Literal binary Bell Riordan coefficient formula with integer coefficients.
noncomputable def seriesBell (a : ℕ → ℤ) (n i j : ℕ) : ℤ :=
  if i = j then 0 else
    (((X * seriesTrunc a (n-2))^(min i j+1)).coeff (max i j)) % 2

theorem seriesBell_entry (a : ℕ → ℤ) (n : ℕ) (i j : Fin n) :
    seriesBell a n i j = seriesEntry a i j := by
  by_cases he : i.val = j.val
  · simp [seriesBell, seriesEntry, he]
  · have hm : min i.val j.val+1 ≤ max i.val j.val := by omega
    have hd : max i.val j.val-min i.val j.val-1 ≤ n-2 := by
      have := i.isLt
      have := j.isLt
      omega
    simp only [seriesBell, seriesEntry, he, ite_false, mul_pow,
      coeff_X_pow_mul', hm, ite_true]
    rw [seriesPow_trunc a (n-2) _ _ hd]
    congr 2

theorem seriesBell_local (a b : ℕ → ℤ) (n : ℕ)
    (hab : ∀ d, d ≤ n-2 → a d = b d) (i j : Fin n) :
    seriesBell a n i j = seriesBell b n i j := by
  rw [seriesBell_entry, seriesBell_entry, seriesEntry_local a b n hab]

theorem h_bell_witness (i j : Fin 15) :
    seriesBell hZ 15 i j = (entry i j : ℤ) := by
  rw [seriesBell_entry, h_witness]

theorem h_witness_nat (i j : ℕ) (hi : i < 15) (hj : j < 15) :
    seriesEntry hZ i j = (entry i j : ℤ) :=
  h_witness ⟨i, hi⟩ ⟨j, hj⟩

theorem h_even_independent (i j : Fin 7) :
    seriesEntry hZ (2*i.val+1) (2*j.val+1) = 0 := by
  rw [h_witness_nat _ _ (by omega) (by omega), even_independent i j]
  rfl

theorem h_odd_copy (i j : Fin 8) :
    seriesEntry hZ (2*i.val) (2*j.val) = seriesEntry hZ i j := by
  rw [h_witness_nat _ _ (by omega) (by omega),
    h_witness_nat _ _ (by omega) (by omega), odd_copy i j]

def SeriesSingular (a : ℕ → ℤ) (n : ℕ) : Prop :=
  ∃ v : Fin n → ℝ, (∃ k, v k ≠ 0) ∧
    ∀ i : Fin n, ∑ j : Fin n, (seriesEntry a i j : ℝ) * v j = 0

-- The all-integer-series, infinite-identity reading of Conjecture 7.7.
def SourceConjectureInfiniteFamily : Prop :=
  ∀ a : ℕ → ℤ, a 0 % 2 = 1 →
    (∀ j, a (2*j+1) % 2 = a j % 2) →
    ∀ n, 2 ≤ n → SeriesSingular a n →
    ∀ v : Fin n → ℝ,
      (∀ i : Fin n, ∑ j : Fin n, (seriesEntry a i j : ℝ) * v j = 0) →
      ∀ i : Fin ((n+1)/2), v ⟨2*i.val, by omega⟩ = 0

theorem h_kernelR : ∀ i : Fin 15,
    ∑ j : Fin 15, (seriesEntry hZ i j : ℝ) * xR j = 0 := by
  intro i
  simpa only [h_witness, Int.cast_natCast] using kernelR i

theorem source_conjecture_false_infinite_family :
    ¬ SourceConjectureInfiniteFamily := by
  intro H
  have hc : hZ 0 % 2 = 1 := by simp [hZ, h_zero]
  have hi : ∀ j, hZ (2*j+1) % 2 = hZ j % 2 := by
    intro j
    simp only [hZ, h_io]
  have hs : SeriesSingular hZ 15 :=
    ⟨xR, ⟨0, by norm_num [xR, x]⟩, h_kernelR⟩
  have bad := H hZ hc hi 15 (by omega) hs xR h_kernelR (0 : Fin 8)
  norm_num [xR, x] at bad

#print axioms source_conjecture_false
#print axioms source_conjecture_false_infinite_family
end Riordan
