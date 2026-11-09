import GameRecurrence

open Finset Filter
open scoped Topology

namespace OddSubtraction

lemma centered_balance {S : Finset ℕ} {a : ℕ → ℝ} (hm : Model S a)
    (hodd : ∀ k∈S, k%2=1) (n : ℕ) :
    ((eligible S n).card:ℝ)*centered a n = ∑ k∈eligible S n, centered a (n-k) := by
  have hsign (k : ℕ) (hk : k∈eligible S n) : (-1:ℝ)^(n-k) = -(-1:ℝ)^n := by
    have hkn := (Finset.mem_filter.mp hk).2
    have hko : Odd k := Nat.odd_iff.mpr (hodd k (Finset.mem_filter.mp hk).1)
    have he : (-1:ℝ)^n = -(-1:ℝ)^(n-k) := by
      conv_lhs => rw [← Nat.sub_add_cancel hkn, pow_add, hko.neg_one_pow]
      ring
    linarith
  simp only [centered]
  have hs0 : (∑ k∈eligible S n, (-1:ℝ)^(n-k)*(1-2*a (n-k))) =
      ∑ k∈eligible S n, -(-1:ℝ)^n*(1-2*a (n-k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsign k hk]
  rw [hs0]
  have hs : (∑ k∈eligible S n, -(-1:ℝ)^n*(1-2*a (n-k))) =
      -(-1:ℝ)^n*(((eligible S n).card:ℝ)-2*∑ k∈eligible S n,a (n-k)) := by
    rw [← Finset.mul_sum]
    congr 1
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      mul_one, ← Finset.mul_sum]
  rw [hs]
  have h := hm.balance n
  linear_combination -2 * (-1:ℝ)^n * h

lemma prefixSum_add (c : ℕ → ℝ) (n k : ℕ) :
    prefixSum c (n+k)=prefixSum c n+∑ j∈Finset.range k,c (n+j) := by
  exact Finset.sum_range_add c n k

lemma prefixSum_succ_inv (c : ℕ → ℝ) (n : ℕ) :
    prefixSum c (n+1)=prefixSum c n+c n := Finset.sum_range_succ c n

lemma tail_filter_sum (c : ℕ → ℝ) {D k : ℕ} (hk : k≤D) :
    (∑ n∈Finset.range D, if k≤n then c n else 0)=prefixSum c D-prefixSum c k := by
  have hD : D=k+(D-k) := by omega
  conv_lhs => rw [hD, Finset.sum_range_add]
  have hz : (∑ n∈Finset.range k, if k≤n then c n else 0)=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [ite_eq_right (by have := Finset.mem_range.mp hn; omega)]
  rw [hz, zero_add]
  have ht : (∑ n∈Finset.range (D-k), if k≤k+n then c (k+n) else 0)=
      ∑ n∈Finset.range (D-k), c (k+n) := by simp
  rw [ht]
  conv_rhs => rw [hD, prefixSum_add]
  ring

lemma shifted_filter_sum (c : ℕ → ℝ) {D k : ℕ} (hk : k≤D) :
    (∑ n∈Finset.range D, if k≤n then c (n-k) else 0)=prefixSum c (D-k) := by
  have hD : D=k+(D-k) := by omega
  conv_lhs => rw [hD, Finset.sum_range_add]
  have hz : (∑ n∈Finset.range k, if k≤n then c (n-k) else 0)=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [ite_eq_right (by have := Finset.mem_range.mp hn; omega)]
  rw [hz, zero_add]
  simp [prefixSum]

def window (S : Finset ℕ) (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k∈S, (prefixSum c N-prefixSum c (N-k))

lemma initial_window {S : Finset ℕ} {c : ℕ → ℝ} {D : ℕ}
    (hD : ∀ k∈S, k≤D)
    (hrec : ∀ n, ((eligible S n).card:ℝ)*c n=∑ k∈eligible S n,c (n-k)) :
    window S c D=∑ k∈S,prefixSum c k := by
  have hsum := Finset.sum_congr rfl (fun n (_ : n∈Finset.range D) => hrec n)
  have hl (n : ℕ) : ((eligible S n).card:ℝ)*c n=
      ∑ k∈S, if k≤n then c n else 0 := by
    rw [← Finset.sum_filter]
    simp [eligible]
  have hr (n : ℕ) : (∑ k∈eligible S n,c (n-k))=
      ∑ k∈S, if k≤n then c (n-k) else 0 := by
    exact Finset.sum_filter ..
  simp_rw [hl, hr] at hsum
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range D)] at hsum
  have hl' : (∑ k∈S, ∑ n∈Finset.range D, if k≤n then c n else 0)=
      ∑ k∈S,(prefixSum c D-prefixSum c k) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact tail_filter_sum c (hD k hk)
  have hr' : (∑ k∈S, ∑ n∈Finset.range D, if k≤n then c (n-k) else 0)=
      ∑ k∈S,prefixSum c (D-k) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact shifted_filter_sum c (hD k hk)
  rw [hl', hr', Finset.sum_sub_distrib] at hsum
  dsimp [window]
  rw [Finset.sum_sub_distrib]
  linarith

lemma window_step {S : Finset ℕ} {c : ℕ → ℝ} {N : ℕ}
    (hN : ∀ k∈S, k≤N)
    (hrec : (S.card:ℝ)*c N=∑ k∈S,c (N-k)) :
    window S c (N+1)=window S c N := by
  have hi (k : ℕ) (hk : k∈S) :
      prefixSum c (N+1)-prefixSum c (N+1-k)=
      (prefixSum c N-prefixSum c (N-k))+(c N-c (N-k)) := by
    have he : N+1-k=(N-k)+1 := by have := hN k hk; omega
    rw [he, prefixSum_succ_inv, prefixSum_succ_inv]
    ring
  unfold window
  rw [Finset.sum_congr rfl hi, Finset.sum_add_distrib]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hrec]
  ring

lemma window_constant {S : Finset ℕ} {c : ℕ → ℝ} {D : ℕ}
    (hD : ∀ k∈S, k≤D)
    (hrec : ∀ n, (S.card:ℝ)*c (n+D)=∑ k∈S,c (n+D-k)) (n : ℕ) :
    window S c (n+D)=window S c D := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n+1+D=(n+D)+1 by omega,
      window_step (by intro k hk; have := hD k hk; omega) (hrec n), ih]

end OddSubtraction
