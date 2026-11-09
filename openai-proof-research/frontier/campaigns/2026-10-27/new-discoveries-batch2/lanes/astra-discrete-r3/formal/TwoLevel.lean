import Mathlib

/-!
Initial certificate for the key specialization in the proposed proof of
An–Đoković Conjecture 3.6. This is NOT the full inner-product theorem.
Indices are the literal one-based source indices. The definitions work over
any commutative ring, in particular over the polynomial ring ℤ[t].
-/
namespace AnDjokovic

open Finset

def doubleStar {R : Type*} [CommRing R] (n k : ℕ) (x : ℕ → R) : R :=
  (∏ i ∈ Icc 1 k, (x n - x i)) *
    ∏ i ∈ Ico (k + 1) n, (x i - x 1)

def twoLevel {R : Type*} [CommRing R] (j : ℕ) (t : R) (i : ℕ) : R :=
  if i ≤ j then t else 1

theorem doubleStar_twoLevel_lt {R : Type*} [CommRing R]
    (n k j : ℕ) (t : R) (hjk : j < k) (hkn : k < n) :
    doubleStar n k (twoLevel j t) = 0 := by
  unfold doubleStar
  have hp : (∏ i ∈ Icc 1 k, (twoLevel j t n - twoLevel j t i)) = 0 := by
    apply Finset.prod_eq_zero (i := j + 1)
    · simp only [mem_Icc]
      omega
    · simp [twoLevel, show ¬ n ≤ j by omega]
  rw [hp, zero_mul]

theorem doubleStar_twoLevel_gt {R : Type*} [CommRing R]
    (n k j : ℕ) (t : R) (hk : 1 ≤ k) (hkj : k < j) (hjn : j < n) :
    doubleStar n k (twoLevel j t) = 0 := by
  unfold doubleStar
  have hp : (∏ i ∈ Ico (k + 1) n, (twoLevel j t i - twoLevel j t 1)) = 0 := by
    apply Finset.prod_eq_zero (i := k + 1)
    · simp only [mem_Ico]
      omega
    · simp [twoLevel, show k + 1 ≤ j by omega, show 1 ≤ j by omega]
  rw [hp, mul_zero]

theorem doubleStar_twoLevel_eq {R : Type*} [CommRing R]
    (n k : ℕ) (t : R) (hk : 1 ≤ k) (hkn : k < n) :
    doubleStar n k (twoLevel k t) = (1 - t) ^ (n - 1) := by
  unfold doubleStar
  have hleft : (∏ i ∈ Icc 1 k, (twoLevel k t n - twoLevel k t i)) =
      (1 - t) ^ k := by
    calc
      _ = ∏ _i ∈ Icc 1 k, (1 - t) := by
        apply prod_congr rfl
        intro i hi
        have hi' := (mem_Icc.mp hi).2
        simp [twoLevel, hi', Nat.not_le.mpr hkn]
      _ = _ := by simp
  have hright : (∏ i ∈ Ico (k + 1) n, (twoLevel k t i - twoLevel k t 1)) =
      (1 - t) ^ (n - (k + 1)) := by
    calc
      _ = ∏ _i ∈ Ico (k + 1) n, (1 - t) := by
        apply prod_congr rfl
        intro i hi
        have hi' := (mem_Ico.mp hi).1
        simp [twoLevel, hk, show ¬ i ≤ k by omega]
      _ = _ := by simp
  rw [hleft, hright, ← pow_add]
  congr 1
  omega

theorem doubleStar_twoLevel {R : Type*} [CommRing R]
    (n k j : ℕ) (t : R) (hk : 1 ≤ k) (hkn : k < n) (hjn : j < n) :
    doubleStar n k (twoLevel j t) =
      if j = k then (1 - t) ^ (n - 1) else 0 := by
  rcases lt_trichotomy j k with h | h | h
  · rw [ite_eq_right (Nat.ne_of_lt h)]
    exact doubleStar_twoLevel_lt n k j t h hkn
  · subst j
    simpa using doubleStar_twoLevel_eq n k t hk hkn
  · rw [ite_eq_right (Ne.symm (Nat.ne_of_lt h))]
    exact doubleStar_twoLevel_gt n k j t hk h hjn

/-- The literal source pair set; no source-inner-product result is assumed. -/
def sourcePairs (n k : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 n) ×ˢ (Icc 1 n)).filter fun p =>
    p.1 + 1 < p.2 ∨ (p.1 = n ∧ p.2 ≤ k) ∨ (p.2 = 1 ∧ k < p.1 ∧ p.1 < n)

noncomputable def sourcePolynomial (n k : ℕ) : MvPolynomial ℕ ℤ :=
  ∏ p ∈ sourcePairs n k, (MvPolynomial.X p.1 - MvPolynomial.X p.2)

noncomputable def vandermonde (n : ℕ) : MvPolynomial ℕ ℤ :=
  ∏ p ∈ ((Icc 1 n) ×ˢ (Icc 1 n)).filter (fun p => p.1 < p.2),
    (MvPolynomial.X p.1 - MvPolynomial.X p.2)

/-- Monomials orthonormal, with no factorial normalization. -/
noncomputable def sourceInner (n k : ℕ) : ℤ :=
  ∑ d ∈ (sourcePolynomial n k).support,
    (sourcePolynomial n k).coeff d * (vandermonde n).coeff d

/-- The signed tail appearing in the surviving cumulative coefficient. -/
theorem alternating_tail (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n) :
    (∑ d ∈ Ico k n, ((-1 : ℤ) ^ d * (n - 1).choose d)) =
      (-1 : ℤ) ^ k * (n - 2).choose (k - 1) := by
  have hn : n - 1 ≠ 0 := by omega
  have htotal := Int.alternating_sum_range_choose_of_ne hn
  have hpre := Int.alternating_sum_range_choose_eq_choose (n := n - 2) (m := k - 1)
  have hn2 : n - 2 + 1 = n - 1 := by omega
  have hk1 : k - 1 + 1 = k := by omega
  have hn1 : n - 1 + 1 = n := by omega
  rw [hn1] at htotal
  rw [hn2, hk1] at hpre
  have hsplit := sum_range_add_sum_Ico
    (fun d => ((-1 : ℤ) ^ d * ((n - 1).choose d : ℤ))) (Nat.le_of_lt hkn)
  rw [htotal, hpre] at hsplit
  have hp : (-1 : ℤ) ^ k = -((-1 : ℤ) ^ (k - 1)) := by
    calc
      _ = (-1 : ℤ) ^ ((k - 1) + 1) := by rw [hk1]
      _ = _ := by rw [pow_succ]; ring
  rw [hp]
  linarith

/-- The defining recurrence for prefix defects has no upward step inside the path. -/
theorem prefixDefect_antitone (a : ℕ → ℕ) (n : ℕ)
    (ha : ∀ i, 2 ≤ i → i ≤ n - 1 → a i ≤ 1) :
    AntitoneOn (fun j => (∑ i ∈ Icc 1 j, (a i : ℤ)) - j) (Set.Icc 1 (n - 1)) := by
  intro j hj l hl hjl
  have hj1 : 1 ≤ j := hj.1
  induction l, hjl using Nat.le_induction with
  | base => exact le_rfl
  | succ l hjl ih =>
    have hbound : l + 1 ≤ n - 1 := hl.2
    have hai : a (l + 1) ≤ 1 := ha (l + 1) (by omega) hbound
    have hi : 1 ≤ l + 1 := by omega
    have hrec : (∑ i ∈ Icc 1 (l + 1), (a i : ℤ)) =
        (∑ i ∈ Icc 1 l, (a i : ℤ)) + a (l + 1) := by
      rw [sum_Icc_succ_top (by omega)]
    change (∑ i ∈ Icc 1 (l + 1), (a i : ℤ)) - (l + 1 : ℕ) ≤
      (∑ i ∈ Icc 1 j, (a i : ℤ)) - j
    rw [hrec]
    have hi' := ih ⟨by omega, by omega⟩
    push_cast
    linarith

/-- The numerator is a literal multivariate polynomial, not an abstract model. -/
noncomputable def doubleStarPolynomial (n k : ℕ) : MvPolynomial ℕ ℤ :=
  doubleStar n k MvPolynomial.X

theorem eval_doubleStarPolynomial (n k : ℕ) (x : ℕ → ℤ) :
    MvPolynomial.eval x (doubleStarPolynomial n k) = doubleStar n k x := by
  simp [doubleStarPolynomial, doubleStar]

theorem numerator_twoLevel (n k j : ℕ) (t : ℤ)
    (hk : 1 ≤ k) (hkn : k < n) (hjn : j < n) :
    MvPolynomial.eval (twoLevel j t) (doubleStarPolynomial n k) =
      if j = k then (1 - t) ^ (n - 1) else 0 := by
  rw [eval_doubleStarPolynomial]
  exact doubleStar_twoLevel n k j t hk hkn hjn

/-- Exact arithmetic after the two surviving first-deficit groups are found. -/
theorem twoGroup_evaluation (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n) :
    -((-1 : ℤ) ^ k * (n - 2).choose (k - 1)) *
      ((-1 : ℤ) ^ (n - k) * (n - 1).choose (k - 1)) +
    ((-1 : ℤ) ^ k * (n - 2).choose (k - 1)) *
      ((-1 : ℤ) ^ (n - (k + 1)) * (n - 1).choose k) =
    (-1 : ℤ) ^ (n - 1) * n.choose k * (n - 2).choose (k - 1) := by
  have hsgn1 : -((-1 : ℤ) ^ k * (-1 : ℤ) ^ (n - k)) = (-1 : ℤ) ^ (n - 1) := by
    rw [← pow_add, show k + (n - k) = n by omega]
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring
  have hsgn2 : (-1 : ℤ) ^ k * (-1 : ℤ) ^ (n - (k + 1)) = (-1 : ℤ) ^ (n - 1) := by
    rw [← pow_add, show k + (n - (k + 1)) = n - 1 by omega]
  have hpascal : ((n - 1).choose (k - 1) : ℤ) + (n - 1).choose k = n.choose k := by
    have h := Nat.choose_succ_succ (n - 1) (k - 1)
    rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one,
      show n - 1 + 1 = n by omega, show k - 1 + 1 = k by omega] at h
    exact_mod_cast h.symm
  calc
    _ = -((-1 : ℤ) ^ k * (-1 : ℤ) ^ (n - k)) *
        ((n - 2).choose (k - 1) * (n - 1).choose (k - 1)) +
      ((-1 : ℤ) ^ k * (-1 : ℤ) ^ (n - (k + 1))) *
        ((n - 2).choose (k - 1) * (n - 1).choose k) := by ring
    _ = (-1 : ℤ) ^ (n - 1) * (n - 2).choose (k - 1) *
        ((n - 1).choose (k - 1) + (n - 1).choose k) := by
      rw [hsgn1, hsgn2]
      ring
    _ = _ := by rw [hpascal]; ring

#print doubleStar
#print twoLevel
#print sourcePairs
#print sourcePolynomial
#print vandermonde
#print sourceInner
#print doubleStarPolynomial
#check numerator_twoLevel
#print axioms numerator_twoLevel
#check twoGroup_evaluation
#print axioms twoGroup_evaluation
#check sourceInner
#check doubleStar_twoLevel
#print axioms doubleStar_twoLevel
#check alternating_tail
#print axioms alternating_tail
#check prefixDefect_antitone
#print axioms prefixDefect_antitone

end AnDjokovic
