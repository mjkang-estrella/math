import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Multiset.Fintype
import Mathlib.Tactic

noncomputable section
open Finset Polynomial
namespace OddRootMeans

def powerSum (s : Multiset ℂ) (i : ℕ) : ℂ := (s.map (fun z => z ^ i)).sum

set_option backward.isDefEq.respectTransparency false in
lemma multiset_newton (s : Multiset ℂ) (i : ℕ) (hi : 0 < i) :
    powerSum s i = (-1 : ℂ) ^ (i + 1) * i * s.esymm i -
      ∑ a ∈ (Finset.antidiagonal i).filter (fun a => a.1 ∈ Set.Ioo 0 i),
        (-1 : ℂ) ^ a.1 * s.esymm a.1 * powerSum s a.2 := by
  classical
  have h := congrArg (MvPolynomial.aeval (fun x : s => (x : ℂ)))
    (MvPolynomial.psum_eq_mul_esymm_sub_sum s ℂ i hi)
  simp only [map_sub, map_mul, map_pow, map_neg, map_one, map_natCast,
    map_sum, MvPolynomial.aeval_esymm_eq_multiset_esymm, Multiset.map_univ_coe] at h
  have hp (k : ℕ) : MvPolynomial.aeval (fun x : s => (x : ℂ))
      (MvPolynomial.psum s ℂ k) = powerSum s k := by
    simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X]
    change (Multiset.map (fun x : s => (x : ℂ) ^ k) Finset.univ.val).sum = _
    exact congrArg Multiset.sum (Multiset.map_univ s (fun z : ℂ => z ^ k))
  simpa only [hp] using h

lemma antidiagonal_interior_sum (n : ℕ) (f : ℕ × ℕ → ℂ) :
    (∑ a ∈ (antidiagonal (n+1)).filter (fun a => a.1 ∈ Set.Ioo 0 (n+1)), f a) =
      ∑ k : Fin n, f (k+1,n-k) := by
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_range_succ, sum_range_succ']
  simp only [Set.mem_Ioo, lt_self_iff_false, and_false, ↓reduceIte,
    false_and, add_zero]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_congr
  intro k
  have hk' : (k:ℕ)<n := k.isLt
  simp [hk']

lemma multiset_newton_succ (s : Multiset ℂ) (n : ℕ) :
    powerSum s (n+1) = (-1 : ℂ) ^ (n+2) * (n+1) * s.esymm (n+1) -
      ∑ k : Fin n, (-1 : ℂ) ^ ((k:ℕ)+1) * s.esymm ((k:ℕ)+1) * powerSum s (n-k) := by
  rw [multiset_newton s (n+1) (by omega), antidiagonal_interior_sum]
  simp [Nat.add_assoc]

lemma signed_esymm_coeff (p : ℂ[X]) (hp : p.Monic) (i : ℕ) :
    (-1 : ℂ)^i * p.roots.esymm i =
      if i ≤ p.natDegree then p.coeff (p.natDegree-i) else 0 := by
  classical
  by_cases hi : i ≤ p.natDegree
  · simp only [hi, ↓reduceIte]
    have h := Polynomial.coeff_eq_esymm_roots_of_splits
      (IsAlgClosed.splits p) (Nat.sub_le p.natDegree i)
    simpa [hp.leadingCoeff, Nat.sub_sub_self hi] using h.symm
  · simp only [hi, ↓reduceIte]
    rw [Multiset.esymm_of_card_lt]
    · ring
    · rw [← (IsAlgClosed.splits p).natDegree_eq_card_roots]
      omega

lemma multiset_newton_coeff (s : Multiset ℂ) (c : ℕ → ℂ)
    (hc : ∀ i, (-1 : ℂ)^i * s.esymm i = c i) (n : ℕ) :
    powerSum s (n+1) = -(∑ k : Fin n, c ((k:ℕ)+1) * powerSum s (n-k)) -
      (n+1) * c (n+1) := by
  rw [multiset_newton_succ]
  have hs : (∑ k : Fin n, (-1 : ℂ)^((k:ℕ)+1) * s.esymm ((k:ℕ)+1) *
      powerSum s (n-k)) = ∑ k : Fin n, c ((k:ℕ)+1) * powerSum s (n-k) := by
    simp only [hc]
  rw [hs, ← hc (n+1)]
  have hpow : (-1 : ℂ)^(n+2) = -(-1 : ℂ)^(n+1) := by
    rw [pow_succ]
    ring
  rw [hpow]
  ring

lemma monic_newton_coeff (p : ℂ[X]) (hp : p.Monic) (m : ℕ)
    (hm : p.natDegree = m) (a : ℕ → ℂ)
    (hc : ∀ i ≤ m, p.coeff (m-i) = (m.choose i : ℂ) * a i) (n : ℕ) :
    powerSum p.roots (n+1) =
      -(∑ k : Fin n, (m.choose ((k:ℕ)+1) : ℂ) * a ((k:ℕ)+1) *
        powerSum p.roots (n-k)) - (n+1) * (m.choose (n+1) : ℂ) * a (n+1) := by
  have he (i : ℕ) : (-1 : ℂ)^i * p.roots.esymm i = (m.choose i : ℂ) * a i := by
    rw [signed_esymm_coeff p hp i, hm]
    by_cases hi : i≤m
    · simp only [hi, ↓reduceIte, hc i hi]
    · have hlt : m < i := by omega
      simp [hi, Nat.choose_eq_zero_of_lt hlt]
  simpa only [mul_assoc] using multiset_newton_coeff p.roots
    (fun i => (m.choose i : ℂ) * a i) he n

end OddRootMeans
