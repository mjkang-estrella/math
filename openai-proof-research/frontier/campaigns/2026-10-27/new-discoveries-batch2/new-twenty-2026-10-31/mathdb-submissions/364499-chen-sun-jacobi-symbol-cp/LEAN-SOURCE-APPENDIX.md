# Lean source appendix

Modules are listed in import order.

## ChenSunSource.lean

```lean
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.Linarith

open Matrix BigOperators

namespace ChenSun

/-- The last row and column index in the source. -/
def half (p : ℕ) : ℕ := (p - 1) / 2

/-- Row `i` and column `j` stand for `i + δ` and `j + δ`. -/
def entryMatrix (p : ℕ) [Fact p.Prime] (δ : ℕ) (w : ℤ) :
    Matrix (Fin (half p + 1 - δ)) (Fin (half p + 1 - δ)) ℤ :=
  fun i j =>
    let a : ℤ := (i : ℕ) + (δ : ℤ)
    let b : ℤ := (j : ℕ) + (δ : ℤ)
    legendreSym p (a ^ 2 - b ^ 2) + legendreSym p (a * b) * w

/-- Chen and Sun's determinant difference, with `δ = 0` or `δ = 1`. -/
noncomputable def D (p : ℕ) [Fact p.Prime] (δ : ℕ) (w : ℤ) : ℤ :=
  (entryMatrix p δ w).det - (entryMatrix p δ 0).det

def halfSum (p : ℕ) [Fact p.Prime] : ℤ :=
  ∑ i ∈ Finset.Icc 1 (half p), legendreSym p (i : ℤ)

/-- The positive odd integer specified by (1.3) or (1.5) of the source.
The domain of this specification is the odd primes. -/
def IsCp (p : ℕ) [Fact p.Prime] (c : ℕ) : Prop :=
  Odd p ∧ 0 < c ∧ Odd c ∧
    (p % 4 = 1 → ∀ w : ℤ, D p 0 w = -w * ((half p : ℤ) * (c : ℤ)) ^ 2) ∧
    (p % 4 = 3 → ∀ w : ℤ, D p 1 w = w * ((c : ℤ) * halfSum p) ^ 2)

/-- Conjecture 1.1 with the determinant-defined positive odd root exposed. -/
def Conjecture : Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime, ∀ c : ℕ,
    letI : Fact p.Prime := ⟨hp⟩
    IsCp p c → jacobiSym (p : ℤ) c = 1

theorem half_eq_div (p : ℕ) (hp : Odd p) : half p = p / 2 := by
  rw [Nat.odd_iff] at hp
  unfold half
  omega

theorem half_pos (p : ℕ) [hp : Fact p.Prime] (ho : Odd p) : 0 < half p := by
  have := hp.out.two_le
  rw [half_eq_div p ho]
  omega

theorem odd_mod_four (p : ℕ) (hp : Odd p) : p % 4 = 1 ∨ p % 4 = 3 := by
  rw [Nat.odd_iff] at hp
  omega

theorem legendre_one_to_jacobi (p c : ℕ) [Fact p.Prime]
    (hp : p % 4 = 1) (hc : Odd c) (h : legendreSym p (c : ℤ) = 1) :
    jacobiSym (p : ℤ) c = 1 := by
  rw [jacobiSym.quadratic_reciprocity_one_mod_four hp hc, ← jacobiSym.legendreSym.to_jacobiSym, h]

theorem source_one_mod_four_iff (p c : ℕ) [Fact p.Prime]
    (hp : p % 4 = 1) (hc : Odd c) :
    jacobiSym (p : ℤ) c = 1 ↔ legendreSym p (c : ℤ) = 1 := by
  rw [jacobiSym.quadratic_reciprocity_one_mod_four hp hc, ← jacobiSym.legendreSym.to_jacobiSym]

end ChenSun
```

## ChenSunRoot.lean

```lean
import ChenSunSource
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.NormNum

open Matrix BigOperators

namespace ChenSun

theorem index_lt_prime (p : ℕ) [hp : Fact p.Prime] {j : ℕ} (hj : j ≤ half p) :
    j < p := by
  have := hp.out.two_le
  unfold half at hj
  omega

theorem index_ne_zero_mod (p : ℕ) [Fact p.Prime] {j : ℕ}
    (hj0 : 0 < j) (hj : j ≤ half p) : (j : ZMod p) ≠ 0 := by
  intro hz
  have hv := ZMod.val_natCast_of_lt (index_lt_prime p hj)
  rw [hz, ZMod.val_zero] at hv
  omega

theorem halfSum_odd (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    Odd (halfSum p) := by
  apply ZMod.intCast_eq_one_iff_odd.mp
  have hh : Odd (half p) := by
    rw [Nat.odd_iff]
    unfold half
    omega
  unfold halfSum
  push_cast
  calc
    ∑ j ∈ Finset.Icc 1 (half p), (legendreSym p (j : ℤ) : ZMod 2) =
        ∑ _j ∈ Finset.Icc 1 (half p), (1 : ZMod 2) := by
      apply Finset.sum_congr rfl
      intro j hj
      obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp hj
      have hn : ((j : ℤ) : ZMod p) ≠ 0 := by
        exact_mod_cast index_ne_zero_mod p (by omega : 0 < j) hb
      rcases legendreSym.eq_one_or_neg_one p hn with h | h
      · simp [h]
      · simp [h]
    _ = (half p : ZMod 2) := by simp [Nat.card_Icc]
    _ = 1 := ZMod.natCast_eq_one_iff_odd.mpr hh

theorem halfSum_ne_zero (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    halfSum p ≠ 0 := by
  have h := halfSum_odd p hp
  rintro hz
  rw [hz] at h
  norm_num at h

/-- Recover the candidate root from the defining determinant at `w = 1`. -/
noncomputable def cp (p : ℕ) [Fact p.Prime] (_ : Odd p) : ℕ :=
  if p % 4 = 1 then
    Nat.sqrt ((-D p 0 1 / (half p : ℤ) ^ 2).toNat)
  else
    Nat.sqrt ((D p 1 1 / (halfSum p) ^ 2).toNat)

theorem cp_eq_of_spec (p c : ℕ) [Fact p.Prime] (hp : Odd p) (hc : IsCp p c) :
    cp p hp = c := by
  unfold cp
  rcases odd_mod_four p hp with h | h
  · rw [ite_eq_left h, hc.2.2.2.1 h 1]
    have hn : (half p : ℤ) ^ 2 ≠ 0 := by
      exact pow_ne_zero _ (by exact_mod_cast (half_pos p hp).ne')
    rw [show -(-(1 : ℤ) * ((half p : ℤ) * (c : ℤ)) ^ 2) =
        (c : ℤ) ^ 2 * (half p : ℤ) ^ 2 by ring, Int.mul_ediv_cancel _ hn]
    rw [← Int.natCast_pow, Int.toNat_natCast, Nat.sqrt_eq']
  · rw [ite_eq_right (by omega : p % 4 ≠ 1), hc.2.2.2.2 h 1]
    have hn : halfSum p ^ 2 ≠ 0 := pow_ne_zero _ (halfSum_ne_zero p h)
    rw [show (1 : ℤ) * ((c : ℤ) * halfSum p) ^ 2 = (c : ℤ) ^ 2 * halfSum p ^ 2 by ring,
      Int.mul_ediv_cancel _ hn]
    rw [← Int.natCast_pow, Int.toNat_natCast, Nat.sqrt_eq']

theorem cp_unique (p : ℕ) [Fact p.Prime] {c d : ℕ}
    (hc : IsCp p c) (hd : IsCp p d) : c = d :=
  (cp_eq_of_spec p c hc.1 hc).symm.trans (cp_eq_of_spec p d hc.1 hd)

theorem cp_three_spec : @IsCp 3 ⟨by decide⟩ 1 := by
  have hp : (3 : ℕ).Prime := by decide
  let : Fact (Nat.Prime 3) := ⟨hp⟩
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · intro h
    norm_num at h
  · intro _ w
    have hD : D 3 1 w = w := by
      let M (u : ℤ) : Matrix (Fin 1) (Fin 1) ℤ := entryMatrix 3 1 u
      change (M w).det - (M 0).det = w
      rw [Matrix.det_fin_one, Matrix.det_fin_one]
      change legendreSym 3 (1 ^ 2 - 1 ^ 2) + legendreSym 3 (1 * 1) * w -
        (legendreSym 3 (1 ^ 2 - 1 ^ 2) + legendreSym 3 (1 * 1) * 0) = w
      norm_num [legendreSym.at_zero, legendreSym.at_one]
    have hS : halfSum 3 = 1 := by
      rw [halfSum, show half 3 = 1 by decide, Finset.Icc_self, Finset.sum_singleton]
      exact legendreSym.at_one 3
    simp [hD, hS]

theorem cp_three : @cp 3 ⟨by decide⟩ (by decide) = 1 :=
  @cp_eq_of_spec 3 1 ⟨by decide⟩ (by decide) cp_three_spec

theorem chen_sun_three : jacobiSym 3 (@cp 3 ⟨by decide⟩ (by decide)) = 1 := by
  rw [cp_three, jacobiSym.one_right]

end ChenSun
```

## ChenSunField.lean

```lean
import ChenSunSource
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

open Matrix BigOperators

namespace ChenSun

section Factorization

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The signed binomial coefficient at the row of exponent `i`. -/
def binomialWeight (n : ℕ) (i : Fin (n + 1)) : R :=
  (-1) ^ (i : ℕ) * (n.choose i : R)

def reversedDiagonal (a : Fin (n + 1) → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  (Matrix.diagonal a).submatrix Fin.rev id

theorem det_reversedDiagonal (a : Fin (n + 1) → R) :
    (reversedDiagonal a).det =
      (↑↑(Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (n + 1)))) : R) *
        ∏ i, a i := by
  rw [reversedDiagonal, ← Matrix.det_diagonal]
  exact Matrix.det_permute Fin.revPerm (Matrix.diagonal a)

theorem vandermonde_reversedDiagonal (x a : Fin (n + 1) → R) (j k : Fin (n + 1)) :
    (Matrix.vandermonde x * reversedDiagonal a * (Matrix.vandermonde x)ᵀ) j k =
      ∑ i : Fin (n + 1), x j ^ (Fin.rev i : ℕ) * a i * x k ^ (i : ℕ) := by
  classical
  have aux (i : Fin (n + 1)) :
      (Matrix.vandermonde x * reversedDiagonal a) j i =
        x j ^ (Fin.rev i : ℕ) * a i := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
    · simp [reversedDiagonal, Matrix.vandermonde]
    · intro b _ hb
      have h : b.rev ≠ i := by
        intro e
        apply hb
        simpa using congrArg Fin.rev e
      simp [reversedDiagonal, h]
    · simp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.vandermonde_apply, aux]

theorem binomial_sum (x y : R) (n : ℕ) :
    ∑ i : Fin (n + 1), x ^ (Fin.rev i : ℕ) * binomialWeight n i * y ^ (i : ℕ) =
      (x - y) ^ n := by
  rw [sub_eq_add_neg, add_comm x (-y), add_pow, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (Fin.rev i : ℕ) = n - (i : ℕ) := by simp [Fin.val_rev]
  rw [hi, binomialWeight, neg_pow]
  ring

theorem perturbed_vandermonde (x : Fin (n + 1) → R) (q : Fin (n + 1))
    (hq : q.rev = q) (w : R) :
    (fun j k ↦ (x j - x k) ^ n + w * x j ^ (q : ℕ) * x k ^ (q : ℕ) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
      Matrix.vandermonde x *
        reversedDiagonal (fun i ↦ binomialWeight n i + if i = q then w else 0) *
          (Matrix.vandermonde x)ᵀ := by
  classical
  ext j k
  rw [vandermonde_reversedDiagonal]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, binomial_sum]
  congr 1
  rw [Finset.sum_eq_single q]
  · simp [hq]
    ring
  · intro b _ hb
    simp [hb]
  · simp

theorem det_sub_perturbed (x : Fin (n + 1) → R) (q : Fin (n + 1))
    (hq : q.rev = q) (w : R) :
    Matrix.det (fun j k ↦ (x j - x k) ^ n + w * x j ^ (q : ℕ) * x k ^ (q : ℕ)) -
      Matrix.det (fun j k ↦ (x j - x k) ^ n) =
        w * (↑↑(Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (n + 1)))) : R) *
          (∏ i ∈ Finset.univ.erase q, binomialWeight n i) *
            (Matrix.vandermonde x).det ^ 2 := by
  classical
  have hz := perturbed_vandermonde x q hq (0 : R)
  simp only [zero_mul, add_zero, ite_self] at hz
  rw [perturbed_vandermonde x q hq w, hz]
  simp only [Matrix.det_mul, Matrix.det_transpose, det_reversedDiagonal]
  have hv : q ∈ (Finset.univ : Finset (Fin (n + 1))) := Finset.mem_univ q
  rw [← Finset.prod_erase_mul _ _ hv, ← Finset.prod_erase_mul _ _ hv]
  have hprod :
      (∏ i ∈ Finset.univ.erase q, (binomialWeight n i + if i = q then w else 0 : R)) =
        ∏ i ∈ Finset.univ.erase q, binomialWeight n i := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [(Finset.mem_erase.mp hi).1]
  rw [hprod]
  simp only [ite_true]
  ring

end Factorization
end ChenSun
```

## ChenSunPairs.lean

```lean
import ChenSunField

open Matrix BigOperators

namespace ChenSun

section

variable {R : Type*} [CommRing R]

theorem rev_sign (m : ℕ) :
    Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (2 * m + 1))) = (-1) ^ m := by
  let q : Fin (2 * m + 1) := ⟨m, by omega⟩
  have hfix (i : Fin (2 * m + 1)) :
      (Fin.revPerm : Equiv.Perm (Fin (2 * m + 1))) i = i ↔ i = q := by
    rw [Fin.ext_iff, Fin.ext_iff]
    simp only [Fin.revPerm_apply, Fin.val_rev, q]
    omega
  have hs : (Fin.revPerm : Equiv.Perm (Fin (2 * m + 1))) ^ 2 = 1 := by
    ext i
    simp [pow_two]
  let : Unique (Function.fixedPoints (Fin.revPerm : Equiv.Perm (Fin (2 * m + 1)))) :=
    ⟨⟨⟨q, (hfix q).2 rfl⟩⟩, fun i ↦ Subtype.ext ((hfix i.val).1 i.property)⟩
  rw [Equiv.Perm.sign_of_pow_two_eq_one hs, Fintype.card_fin,
    Fintype.card_unique (α := Function.fixedPoints (Fin.revPerm : Equiv.Perm (Fin (2 * m + 1))))]
  congr 1
  omega

theorem paired_product (m : ℕ) (a : Fin (2 * m + 1) → R) :
    (∏ i ∈ Finset.univ.erase (⟨m, by omega⟩ : Fin (2 * m + 1)), a i) =
      ∏ i : Fin m, a ⟨i, by omega⟩ * a (⟨i, by omega⟩ : Fin (2 * m + 1)).rev := by
  classical
  let q : Fin (2 * m + 1) := ⟨m, by omega⟩
  let low (i : Fin m) : Fin (2 * m + 1) := ⟨i, by omega⟩
  let S : Finset (Fin (2 * m + 1)) := Finset.univ.erase q
  change (∏ i ∈ S, a i) = ∏ i : Fin m, a (low i) * a (low i).rev
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun i : Fin (2 * m + 1) ↦ (i : ℕ) < m),
    Finset.prod_mul_distrib]
  congr 1
  · symm
    refine Finset.prod_bij (fun i _ ↦ low i) ?_ ?_ ?_ (fun _ _ ↦ rfl)
    · intro i _
      simp only [Finset.mem_filter, S, Finset.mem_erase, Finset.mem_univ, and_true]
      refine ⟨fun e ↦ ?_, i.isLt⟩
      have h := congrArg Fin.val e
      simp only [low, q] at h
      omega
    · intro b _ d _ e
      exact Fin.ext (congrArg (Fin.val : Fin (2 * m + 1) → ℕ) e)
    · intro b hb
      have h := (Finset.mem_filter.mp hb).2
      exact ⟨⟨b, h⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · symm
    refine Finset.prod_bij (fun i _ ↦ (low i).rev) ?_ ?_ ?_ (fun _ _ ↦ rfl)
    · intro i _
      simp only [Finset.mem_filter, S, Finset.mem_erase, Finset.mem_univ, and_true]
      refine ⟨fun e ↦ ?_, ?_⟩
      · have h := congrArg Fin.val e
        simp only [Fin.val_rev, low, q] at h
        omega
      · simp only [Fin.val_rev, low]
        omega
    · intro b _ d _ e
      have h : low b = low d := Fin.rev_injective e
      exact Fin.ext (congrArg (Fin.val : Fin (2 * m + 1) → ℕ) h)
    · intro b hb
      have hge := (Finset.mem_filter.mp hb).2
      have hne := (Finset.mem_erase.mp (Finset.mem_filter.mp hb).1).1
      have hne' : (b : ℕ) ≠ m := fun e ↦ hne (Fin.ext e)
      have hlt : (b.rev : ℕ) < m := by
        simp only [Fin.val_rev]
        omega
      refine ⟨⟨b.rev, hlt⟩, Finset.mem_univ _, ?_⟩
      have he : low (⟨b.rev, hlt⟩ : Fin m) = b.rev := Fin.ext rfl
      rw [he, Fin.rev_rev]

theorem paired_binomial_weights (m : ℕ) :
    (∏ i ∈ Finset.univ.erase (⟨m, by omega⟩ : Fin (2 * m + 1)),
      (binomialWeight (2 * m) i : R)) =
      (∏ i : Fin m, ((2 * m).choose i : R)) ^ 2 := by
  rw [paired_product]
  simp only [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  simp only [binomialWeight, Fin.val_rev]
  have hi : 2 * m + 1 - ((i : ℕ) + 1) = 2 * m - (i : ℕ) := by omega
  rw [hi, Nat.choose_symm (by omega : (i : ℕ) ≤ 2 * m)]
  have hs : (-1 : R) ^ (i : ℕ) * (-1 : R) ^ (2 * m - (i : ℕ)) = 1 := by
    rw [← pow_add, show (i : ℕ) + (2 * m - (i : ℕ)) = 2 * m by omega,
      pow_mul]
    simp
  calc
    _ = ((-1 : R) ^ (i : ℕ) * (-1 : R) ^ (2 * m - (i : ℕ))) *
        ((2 * m).choose i : R) ^ 2 := by ring
    _ = _ := by rw [hs, one_mul]

end
end ChenSun
```

## ChenSunReduction.lean

```lean
import ChenSunField
import ChenSunRoot
import Mathlib.Data.Nat.Choose.Dvd

open Matrix BigOperators

namespace ChenSun

def point (p : ℕ) (i : Fin (half p + 1)) : ZMod p :=
  ((i : ℕ) : ZMod p) ^ 2

theorem twice_half (p : ℕ) (hp : Odd p) : 2 * half p = p - 1 := by
  rw [Nat.odd_iff] at hp
  unfold half
  omega

theorem point_injective (p : ℕ) [hprime : Fact p.Prime] (hp : Odd p) :
    Function.Injective (point p) := by
  intro i j hij
  have hi : (i : ℕ) ≤ half p := by omega
  have hj : (j : ℕ) ≤ half p := by omega
  have hlt : (i : ℕ) + (j : ℕ) < p := by
    have := twice_half p hp
    have := hprime.out.pos
    omega
  have hprod : ((((i : ℕ) : ZMod p) - (j : ℕ)) *
      (((i : ℕ) : ZMod p) + (j : ℕ))) = 0 := by
    change ((i : ℕ) : ZMod p) ^ 2 = ((j : ℕ) : ZMod p) ^ 2 at hij
    calc
      _ = ((i : ℕ) : ZMod p) ^ 2 - ((j : ℕ) : ZMod p) ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hij
  apply Fin.ext
  rcases mul_eq_zero.mp hprod with h | h
  · have hcast := congrArg ZMod.val (sub_eq_zero.mp h)
    simpa only [ZMod.val_natCast_of_lt (index_lt_prime p hi),
      ZMod.val_natCast_of_lt (index_lt_prime p hj)] using hcast
  · rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff] at h
    by_contra hne
    change (i : ℕ) ≠ (j : ℕ) at hne
    have hpos : 0 < (i : ℕ) + (j : ℕ) := by omega
    exact (not_le_of_gt hlt) (Nat.le_of_dvd hpos h)

theorem vandermonde_point_det_ne_zero (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    (Matrix.vandermonde (point p)).det ≠ 0 :=
  Matrix.det_vandermonde_ne_zero_iff.mpr (point_injective p hp)

def middle (p : ℕ) : Fin (half p + 1) :=
  ⟨half p / 2, by omega⟩

theorem middle_rev (p : ℕ) (hp : p % 4 = 1) : (middle p).rev = middle p := by
  apply Fin.ext
  simp only [middle, Fin.val_rev]
  unfold half
  omega

theorem entryMatrix_mod_even (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1)
    (w : ℤ) :
    (entryMatrix p 0 w).map (Int.castRingHom (ZMod p)) =
      (fun j k ↦ (point p j - point p k) ^ half p +
          (w : ZMod p) * point p j ^ (middle p : ℕ) * point p k ^ (middle p : ℕ) :
        Matrix (Fin (half p + 1)) (Fin (half p + 1)) (ZMod p)) := by
  have ho : Odd p := Nat.odd_iff.mpr (by omega)
  have hmid : 2 * (middle p : ℕ) = half p := by
    change 2 * (half p / 2) = half p
    unfold half
    omega
  ext j k
  change ((entryMatrix p 0 w j k : ℤ) : ZMod p) = _
  simp only [entryMatrix,
    Int.cast_add, Int.cast_mul, legendreSym.eq_pow, Int.cast_sub, Int.cast_pow,
    Int.cast_natCast, Nat.cast_zero, add_zero, ← half_eq_div p ho, point,
    mul_pow, ← pow_mul, hmid]
  ring

theorem D_mod_even (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) (w : ℤ) :
    (D p 0 w : ZMod p) =
      (w : ZMod p) * (↑↑(Equiv.Perm.sign (Fin.revPerm :
        Equiv.Perm (Fin (half p + 1)))) : ZMod p) *
      (∏ i ∈ Finset.univ.erase (middle p), binomialWeight (half p) i) *
      (Matrix.vandermonde (point p)).det ^ 2 := by
  unfold D
  have hmap (u : ℤ) : ((entryMatrix p 0 u).det : ZMod p) =
      ((entryMatrix p 0 u).map (Int.castRingHom (ZMod p))).det :=
    (Int.castRingHom (ZMod p)).map_det _
  change (((entryMatrix p 0 w).det - (entryMatrix p 0 0).det : ℤ) : ZMod p) = _
  rw [Int.cast_sub, hmap, hmap, entryMatrix_mod_even p hp, entryMatrix_mod_even p hp]
  simpa using det_sub_perturbed (point p) (middle p) (middle_rev p hp) (w : ZMod p)

end ChenSun
```

## ChenSunEven.lean

```lean
import ChenSunReduction
import ChenSunPairs
import Mathlib.NumberTheory.Wilson

open Matrix BigOperators

namespace ChenSun

def binomialProduct (p : ℕ) : ZMod p :=
  ∏ i ∈ Finset.range (half p / 2), ((half p).choose i : ZMod p)

theorem even_coefficient {R : Type*} [CommRing R] (n : ℕ) (he : Even n) :
    (↑↑(Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (n + 1)))) : R) *
      (∏ i ∈ Finset.univ.erase (⟨n / 2, by omega⟩ : Fin (n + 1)),
        binomialWeight n i) =
      (-1 : R) ^ (n / 2) *
        (∏ i ∈ Finset.range (n / 2), (n.choose i : R)) ^ 2 := by
  obtain ⟨m, hm⟩ := he
  obtain rfl : n = 2 * m := by omega
  have hz : 2 * m / 2 = m := by omega
  simp only [hz, rev_sign, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    Int.cast_pow, Int.cast_neg, Int.cast_one, paired_binomial_weights]
  rw [Fin.prod_univ_eq_prod_range (fun i ↦ ((2 * m).choose i : R))]

theorem D_mod_even_square (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) (w : ℤ) :
    (D p 0 w : ZMod p) =
      (w : ZMod p) * (-1) ^ (half p / 2) *
        (binomialProduct p * (Matrix.vandermonde (point p)).det) ^ 2 := by
  have he : Even (half p) := Nat.even_iff.mpr (by unfold half; omega)
  rw [D_mod_even p hp]
  rw [mul_assoc (w : ZMod p), middle, even_coefficient (half p) he]
  unfold binomialProduct
  ring

theorem binomialProduct_ne_zero (p : ℕ) [hprime : Fact p.Prime] :
    binomialProduct p ≠ 0 := by
  unfold binomialProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi hz
  rw [ZMod.natCast_eq_zero_iff] at hz
  have hlt : (half p) < p := index_lt_prime p le_rfl
  have hle : i ≤ half p := by have := Finset.mem_range.mp hi; omega
  exact hprime.out.coprime_iff_not_dvd.mp (hprime.out.coprime_choose_of_lt hlt hle) hz

theorem twice_half_cast (p : ℕ) [hprime : Fact p.Prime] (hp : Odd p) :
    (2 : ZMod p) * (half p : ZMod p) = -1 := by
  have hnat : 2 * half p + 1 = p := by
    have := twice_half p hp
    have := hprime.out.pos
    omega
  have hz : (2 : ZMod p) * (half p : ZMod p) + 1 = 0 := by
    exact_mod_cast (show ((2 * half p + 1 : ℕ) : ZMod p) = 0 by rw [hnat, ZMod.natCast_self])
  linear_combination hz

theorem cp_square_mod_even (p c : ℕ) [Fact p.Prime] (hp : p % 4 = 1)
    (hc : IsCp p c) :
    (c : ZMod p) ^ 2 = (-1) ^ (half p / 2 + 1) *
      (2 * binomialProduct p * (Matrix.vandermonde (point p)).det) ^ 2 := by
  have hs := congrArg (fun z : ℤ ↦ (z : ZMod p)) (hc.2.2.2.1 hp 1)
  push_cast at hs
  rw [D_mod_even_square p hp] at hs
  push_cast at hs
  have h2 := twice_half_cast p hc.1
  have h4 : (4 : ZMod p) * (half p : ZMod p) ^ 2 = 1 := by
    linear_combination (2 * (half p : ZMod p) - 1) * h2
  rw [pow_succ]
  linear_combination 4 * hs - (c : ZMod p) ^ 2 * h4

end ChenSun
```

## ChenSunVandermonde.lean

```lean
import ChenSunReduction
import Mathlib.NumberTheory.Wilson
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

open Matrix BigOperators
open scoped Nat

namespace ChenSun

theorem square_differences_row {R : Type*} [CommRing R] (k : ℕ) :
    (∏ j ∈ Finset.range k, ((k : R) ^ 2 - (j : R) ^ 2)) =
      (k : R) * ((2 * k - 1)! : R) ∨ k = 0 := by
  by_cases hk : k = 0
  · exact Or.inr hk
  left
  have hk0 : 0 < k := Nat.pos_of_ne_zero hk
  have hsub : (∏ j ∈ Finset.range k, ((k : R) - (j : R))) = (k ! : R) := by
    rw [← Finset.prod_range_add_one_eq_factorial k, Nat.cast_prod,
      ← Finset.prod_range_reflect (fun j : ℕ ↦ ((j + 1 : ℕ) : R)) k]
    apply Finset.prod_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [← Nat.cast_sub hj'.le, show k - j = k - 1 - j + 1 by omega]
  have hadd : (∏ j ∈ Finset.range k, ((k : R) + (j : R))) = (k.ascFactorial k : R) := by
    rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    simp only [Nat.cast_add]
  calc
    _ = ∏ j ∈ Finset.range k, ((k : R) - (j : R)) * ((k : R) + (j : R)) := by
      apply Finset.prod_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [Finset.prod_mul_distrib, hsub, hadd, ← Nat.cast_mul, ← Nat.cast_mul]
      congr 1
      calc
        k ! * k.ascFactorial k = k * ((k - 1)! * k.ascFactorial k) := by
          have hf : k ! = k * (k - 1)! := by
            cases k with
            | zero => contradiction
            | succ n => exact Nat.factorial_succ n
          rw [hf, Nat.mul_assoc]
        _ = k * (2 * k - 1)! := by rw [Nat.factorial_mul_ascFactorial' k k hk0]; congr 2; omega

/-- Vandermonde at the squares of (0,ldots,h), grouped by the larger index. -/
theorem det_square_vandermonde {R : Type*} [CommRing R] (h : ℕ) :
    (Matrix.vandermonde (fun i : Fin (h + 1) ↦ ((i : ℕ) : R) ^ 2)).det =
      (h ! : R) * ∏ i ∈ Finset.range h, ((2 * i + 1)! : R) := by
  rw [Matrix.det_vandermonde]
  rw [Finset.prod_comm' (s' := Finset.Iio) (t' := Finset.univ)
    (by intro j k; simp)]
  have hrow (k : Fin (h + 1)) :
      (∏ j ∈ Finset.Iio k, (((k : ℕ) : R) ^ 2 - ((j : ℕ) : R) ^ 2)) =
        ∏ j ∈ Finset.range (k : ℕ), (((k : ℕ) : R) ^ 2 - (j : R) ^ 2) := by
    refine Finset.prod_bij (fun j _ ↦ (j : ℕ)) ?_ ?_ ?_ (fun _ _ ↦ rfl)
    · intro j hj
      exact Finset.mem_range.mpr (show j < k from Finset.mem_Iio.mp hj)
    · intro a _ b _ h'
      exact Fin.ext h'
    · intro j hj
      have hj' := Finset.mem_range.mp hj
      exact ⟨⟨j, hj'.trans k.isLt⟩, Finset.mem_Iio.mpr (show (⟨j, hj'.trans k.isLt⟩ : Fin (h + 1)) < k from hj'), rfl⟩
  simp only [hrow, Fin.prod_univ_succ, Fin.val_zero, Finset.range_zero, Finset.prod_empty,
    one_mul, Fin.val_succ]
  rw [← Finset.prod_range_add_one_eq_factorial h, Nat.cast_prod, ← Finset.prod_mul_distrib]
  rw [Fin.prod_univ_eq_prod_range
    (fun k : ℕ ↦ ∏ j ∈ Finset.range (k + 1), (((k + 1 : ℕ) : R) ^ 2 - (j : R) ^ 2))]
  apply Finset.prod_congr rfl
  intro i _
  rcases square_differences_row (R := R) (i + 1) with h' | h'
  · simpa only [show 2 * (i + 1) - 1 = 2 * i + 1 by omega] using h'
  · omega

theorem factorial_reflection (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : n ≤ p - 1) :
    (((p - 1 - n)! : ℕ) : ZMod p) * (n ! : ZMod p) = (-1) ^ (n + 1) := by
  have h := Nat.factorial_mul_descFactorial hn
  have hc := congrArg (fun k : ℕ ↦ (k : ZMod p)) h
  push_cast at hc
  rw [ZMod.cast_descFactorial (show n ≤ p by omega), ZMod.wilsons_lemma] at hc
  have hsign : (-1 : ZMod p) ^ n * (-1) ^ n = 1 := by
    rw [← mul_pow]
    simp
  rw [pow_succ]
  linear_combination ((-1 : ZMod p) ^ n) * hc -
    (((p - 1 - n)! : ℕ) : ZMod p) * (n ! : ZMod p) * hsign

theorem odd_factorials_product_even (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) :
    (∏ i ∈ Finset.range (half p), ((2 * i + 1)! : ZMod p)) = 1 := by
  let m := half p / 2
  have hh : half p = m + m := by unfold m half; omega
  have hp' : p - 1 = 4 * m := by unfold m half; omega
  rw [hh, Finset.prod_range_add,
    ← Finset.prod_range_reflect (fun i : ℕ ↦ ((2 * (m + i) + 1)! : ZMod p)) m,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i hi
  have hi' : i < m := Finset.mem_range.mp hi
  have hn : 2 * i + 1 ≤ p - 1 := by omega
  have h := factorial_reflection p hn
  have href : p - 1 - (2 * i + 1) = 2 * (m + (m - 1 - i)) + 1 := by omega
  rw [href, mul_comm, show 2 * i + 1 + 1 = 2 * (i + 1) by omega, pow_mul] at h
  simpa using h

theorem vandermonde_eq_half_factorial (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) :
    (Matrix.vandermonde (point p)).det = ((half p)! : ZMod p) := by
  unfold point
  rw [det_square_vandermonde, odd_factorials_product_even p hp, mul_one]

end ChenSun
```

## ChenSunCharacter.lean

```lean
import ChenSunEven
import ChenSunVandermonde

open Matrix BigOperators
open scoped Nat

namespace ChenSun

private theorem prod_range_double {M : Type*} [CommMonoid M] (f : ℕ → M) (m : ℕ) :
    (∏ i ∈ Finset.range (2 * m), f i) =
      ∏ i ∈ Finset.range m, f (2 * i) * f (2 * i + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega,
      Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ _ m, ih, mul_assoc]

private theorem factorial_mod_ne_zero (p : ℕ) [hp : Fact p.Prime] {n : ℕ} (hn : n < p) :
    (n ! : ZMod p) ≠ 0 := by
  intro h
  exact (not_le_of_gt hn) (hp.out.dvd_factorial.mp ((ZMod.natCast_eq_zero_iff _ _).mp h))

theorem factorial_character_twice (p : ℕ) [Fact p.Prime] (m : ℕ)
    (χ : MulChar (ZMod p) ℤ) :
    χ ((2 * m)! : ZMod p) =
      χ 2 ^ m * χ (m ! : ZMod p) * ∏ i ∈ Finset.range m, χ ((2 * i + 1 : ℕ) : ZMod p) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ (2 * m), Nat.factorial_succ m,
      Finset.prod_range_succ, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, map_mul, map_mul,
      map_mul, ih, pow_succ]
    have hm : ((2 * m + 1 + 1 : ℕ) : ZMod p) = 2 * ((m + 1 : ℕ) : ZMod p) := by
      push_cast
      ring
    rw [hm, map_mul]
    ring

theorem factorial_product_character (p : ℕ) [Fact p.Prime] (m : ℕ)
    (hm : 2 * m < p) :
    (∏ i ∈ Finset.range (2 * m), quadraticChar (ZMod p) (i ! : ZMod p)) =
      ∏ i ∈ Finset.range m, quadraticChar (ZMod p) ((2 * i + 1 : ℕ) : ZMod p) := by
  rw [prod_range_double]
  apply Finset.prod_congr rfl
  intro i hi
  have hlt : 2 * i < p := by have := Finset.mem_range.mp hi; omega
  rw [Nat.factorial_succ (2 * i), Nat.cast_mul, map_mul, mul_left_comm,
    ← pow_two, quadraticChar_sq_one (factorial_mod_ne_zero p hlt), mul_one]

private theorem binomial_factorial_product {R : Type*} [CommRing R] (m : ℕ) :
    (∏ i ∈ Finset.range m, ((2 * m).choose i : R)) *
      ((∏ i ∈ Finset.range (2 * m), (i ! : R)) * ((2 * m)! : R)) =
        (((2 * m)! : R) ^ m) * (m ! : R) := by
  classical
  let q : Fin (2 * m + 1) := ⟨m, by omega⟩
  have hprod :
      (∏ i ∈ Finset.range (2 * m), (i ! : R)) * ((2 * m)! : R) =
        (∏ i : Fin (2 * m + 1), ((i : ℕ)! : R)) := by
    rw [← Finset.prod_range_succ, Fin.prod_univ_eq_prod_range (fun i ↦ (i ! : R))]
  rw [hprod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ q), paired_product, ← mul_assoc]
  simp only [Fin.val_rev]
  rw [Fin.prod_univ_eq_prod_range
    (fun i : ℕ ↦ (i ! : R) * ((2 * m + 1 - (i + 1))! : R)), ← Finset.prod_mul_distrib]
  change (∏ i ∈ Finset.range m,
    ((2 * m).choose i : R) * ((i ! : R) * ((2 * m + 1 - (i + 1))! : R))) * (m ! : R) = _
  congr 1
  have hconst : (∏ _i ∈ Finset.range m, (((2 * m)! : R))) = (((2 * m)! : R) ^ m) := by
    simp
  rw [← hconst]
  apply Finset.prod_congr rfl
  intro i hi
  have hle : i ≤ 2 * m := by have := Finset.mem_range.mp hi; omega
  rw [show 2 * m + 1 - (i + 1) = 2 * m - i by omega, ← Nat.cast_mul, ← Nat.cast_mul,
    ← Nat.mul_assoc, Nat.choose_mul_factorial_mul_factorial hle]

theorem two_character (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) :
    quadraticChar (ZMod p) 2 = (-1) ^ (half p / 2) := by
  rw [show (2 : ZMod p) = ((2 : ℤ) : ZMod p) by norm_num]
  change legendreSym p 2 = _
  rw [legendreSym.at_two (by omega), ZMod.χ₈_nat_eq_if_mod_eight]
  have hs : p % 8 = 1 ∨ p % 8 = 5 := by omega
  rcases hs with h | h
  · have he : Even (half p / 2) := Nat.even_iff.mpr (by unfold half; omega)
    rw [he.neg_one_pow]
    simp [show p % 2 ≠ 0 by omega, h]
  · have ho : Odd (half p / 2) := Nat.odd_iff.mpr (by unfold half; omega)
    rw [ho.neg_one_pow]
    simp [show p % 2 ≠ 0 by omega, h]

theorem half_factorial_character (p : ℕ) [hprime : Fact p.Prime] (hp : p % 4 = 1) :
    quadraticChar (ZMod p) ((half p)! : ZMod p) = (-1) ^ (half p / 2) := by
  let a : ℤ := ((half p)! : ℕ)
  have := hprime.out.two_le
  rw [show ((half p)! : ZMod p) = (a : ZMod p) by simp [a]]
  change legendreSym p a = _
  have ho : Odd p := Nat.odd_iff.mpr (by omega)
  have hsq : (a : ZMod p) ^ 2 = -1 := by
    simpa [a, half] using ZMod.half_factorial_sq_eq_neg_one (by omega : p % 4 ≠ 3)
  have hcast : (legendreSym p a : ZMod p) = (-1 : ZMod p) ^ (half p / 2) := by
    calc
      _ = (a : ZMod p) ^ (2 * (half p / 2)) := by
        rw [legendreSym.eq_pow, ← half_eq_div p ho]
        congr 1
        unfold half
        omega
      _ = _ := by rw [pow_mul, hsq]
  have ha : (a : ZMod p) ≠ 0 := by
    intro h
    simp [h] at hsq
  rcases legendreSym.eq_one_or_neg_one p ha with hl | hl
  · rcases Nat.even_or_odd (half p / 2) with h | h
    · rw [hl, h.neg_one_pow]
    · rw [hl, Int.cast_one, h.neg_one_pow, eq_comm, ZMod.neg_one_eq_one_iff] at hcast
      rcases hcast with hcast | hcast <;> omega
  · rcases Nat.even_or_odd (half p / 2) with h | h
    · rw [hl, Int.cast_neg, Int.cast_one, h.neg_one_pow, ZMod.neg_one_eq_one_iff] at hcast
      rcases hcast with hcast | hcast <;> omega
    · rw [hl, h.neg_one_pow]

theorem binomialProduct_character (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) :
    quadraticChar (ZMod p) (binomialProduct p) = 1 := by
  let m := half p / 2
  let χ := quadraticChar (ZMod p)
  let oddFactors := ∏ i ∈ Finset.range m, χ ((2 * i + 1 : ℕ) : ZMod p)
  have hh : half p = 2 * m := by unfold m half; omega
  have hlt : 2 * m < p := hh ▸ index_lt_prime p le_rfl
  have hB : binomialProduct p = ∏ i ∈ Finset.range m, ((2 * m).choose i : ZMod p) := by
    unfold binomialProduct
    congr 1
    funext i
    rw [hh]
  have hF : χ ((2 * m)! : ZMod p) = χ 2 := by
    rw [← hh]
    exact (half_factorial_character p hp).trans (two_character p hp).symm
  have h1 := congrArg χ (binomial_factorial_product (R := ZMod p) m)
  change χ ((∏ i ∈ Finset.range m, ((2 * m).choose i : ZMod p)) * _) = _ at h1
  rw [← hB, map_mul, map_mul, map_mul, map_pow, map_prod,
    factorial_product_character p m hlt] at h1
  change χ (binomialProduct p) * (oddFactors * χ ((2 * m)! : ZMod p)) =
    χ ((2 * m)! : ZMod p) ^ m * χ (m ! : ZMod p) at h1
  have h2 := factorial_character_twice p m χ
  change χ ((2 * m)! : ZMod p) = χ 2 ^ m * χ (m ! : ZMod p) * oddFactors at h2
  rw [hF] at h1
  rw [hF] at h2
  have hTwo : χ 2 ≠ 0 := by
    rw [show χ 2 = (-1 : ℤ) ^ m from two_character p hp]
    exact pow_ne_zero _ (by decide)
  have hMid : χ (m ! : ZMod p) ≠ 0 := fun hz ↦
    factorial_mod_ne_zero p (show m < p by omega) (quadraticChar_eq_zero_iff.mp hz)
  have h3 : χ (binomialProduct p) * oddFactors ^ 2 = 1 := by
    apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero m hTwo) hMid)
    linear_combination h1 - (χ (binomialProduct p) * oddFactors) * h2
  have hOdd : oddFactors ^ 2 = 1 := by
    dsimp [oddFactors, χ]
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hne : ((2 * i + 1 : ℕ) : ZMod p) ≠ 0 := by
      intro h
      have hv := ZMod.val_natCast_of_lt (show 2 * i + 1 < p by omega)
      rw [h, ZMod.val_zero] at hv
      omega
    exact quadraticChar_sq_one hne
  rw [hOdd, mul_one] at h3
  exact h3

end ChenSun
```

## ChenSunEvenResult.lean

```lean
import ChenSunCharacter

open Matrix BigOperators

namespace ChenSun

theorem cp_legendre_even (p c : ℕ) [Fact p.Prime] (hp : p % 4 = 1) (hc : IsCp p c) :
    legendreSym p (c : ℤ) = 1 := by
  let m := half p / 2
  let U := 2 * binomialProduct p * (Matrix.vandermonde (point p)).det
  have hU : quadraticChar (ZMod p) U = 1 := by
    unfold U
    rw [map_mul, map_mul, binomialProduct_character p hp, mul_one,
      vandermonde_eq_half_factorial p hp, two_character p hp, half_factorial_character p hp,
      ← mul_pow]
    simp
  have h19 : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have hUpow : U ^ half p = 1 := by
    have hpow := quadraticChar_eq_pow_of_char_ne_two' h19 U
    rw [hU, Int.cast_one, ZMod.card, ← half_eq_div p hc.1] at hpow
    exact hpow.symm
  have hh : 2 * m = half p := by unfold m half; omega
  have hs : (c : ZMod p) ^ 2 = (-1) ^ (m + 1) * U ^ 2 :=
    cp_square_mod_even p c hp hc
  have hsign : ((-1 : ZMod p) ^ (m + 1)) ^ m = 1 := by
    rcases Nat.even_or_odd m with h | h
    · rw [← pow_mul]
      exact (h.mul_left (m + 1)).neg_one_pow
    · have he : Even (m + 1) := Nat.even_iff.mpr (by rw [Nat.odd_iff] at h; omega)
      rw [he.neg_one_pow, one_pow]
  have hcpow : (c : ZMod p) ^ half p = 1 := by
    rw [← hh, pow_mul, hs, mul_pow, hsign, one_mul, ← pow_mul, hh, hUpow]
  have hcnz : (c : ZMod p) ≠ 0 := by
    intro hz
    rw [hz, zero_pow (half_pos p hc.1).ne'] at hcpow
    exact zero_ne_one hcpow
  apply (legendreSym.eq_one_iff' p hcnz).2
  apply (ZMod.euler_criterion p hcnz).2
  rwa [← half_eq_div p hc.1]

/-- Chen and Sun's conjecture for a specified positive odd root when `p ≡ 1 mod 4`. -/
theorem chen_sun_one_mod_four (p c : ℕ) [Fact p.Prime] (hp : p % 4 = 1) (hc : IsCp p c) :
    jacobiSym (p : ℤ) c = 1 :=
  legendre_one_to_jacobi p c hp hc.2.2.1 (cp_legendre_even p c hp hc)

end ChenSun
```

## ChenSunRows.lean

```lean
import ChenSunReduction
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Intervals

open Matrix BigOperators

namespace ChenSun

private theorem sum_residues (p : ℕ) [hprime : Fact p.Prime] {R : Type*} [AddCommMonoid R]
    (f : ZMod p → R) :
    (∑ x : ZMod p, f x) = ∑ j ∈ Finset.range p, f (j : ZMod p) := by
  classical
  refine Finset.sum_bij (fun x _ ↦ x.val) ?_ ?_ ?_ ?_
  · intro x _
    exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro x _ y _ h
    exact ZMod.val_injective p h
  · intro j hj
    exact ⟨(j : ZMod p), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.mp hj)⟩
  · intro x _
    rw [ZMod.natCast_zmod_val]

private theorem half_symmetric_sum (p : ℕ) [hprime : Fact p.Prime] (hp : Odd p)
    {R : Type*} [AddCommMonoid R] (f : ZMod p → R) (hf : ∀ x, f (-x) = f x) :
    (∑ x : ZMod p, f x) =
      f 0 + (∑ j ∈ Finset.range (half p), f ((j + 1 : ℕ) : ZMod p)) +
        ∑ j ∈ Finset.range (half p), f ((j + 1 : ℕ) : ZMod p) := by
  have hp' : p = (half p + half p) + 1 := by
    have := twice_half p hp
    have := hprime.out.pos
    omega
  have hsplit : (∑ j ∈ Finset.range p, f (j : ZMod p)) =
      f 0 + ((∑ j ∈ Finset.range (half p), f ((j + 1 : ℕ) : ZMod p)) +
        ∑ j ∈ Finset.range (half p), f ((half p + j + 1 : ℕ) : ZMod p)) := by
    have heq : Finset.range p = Finset.range (half p + half p + 1) := congrArg Finset.range hp'
    rw [heq, Finset.sum_range_succ']
    rw [Finset.sum_range_add]
    simp only [add_comm, Nat.cast_zero]
  rw [sum_residues, hsplit, ← add_assoc]
  congr 1
  rw [← Finset.sum_range_reflect (fun j : ℕ ↦ f ((half p + j + 1 : ℕ) : ZMod p))]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have h : half p + (half p - 1 - i) + 1 + (i + 1) = p := by omega
  have hz : ((half p + (half p - 1 - i) + 1 : ℕ) : ZMod p) =
      -((i + 1 : ℕ) : ZMod p) := by
    apply eq_neg_of_add_eq_zero_left
    rw [← Nat.cast_add, h, ZMod.natCast_self]
  rw [hz, hf]

theorem full_quadratic_power_sum (p : ℕ) [hprime : Fact p.Prime] (hp : Odd p) (a : ZMod p) :
    (∑ x : ZMod p, (a - x ^ 2) ^ half p) = -((-1 : ZMod p) ^ half p) := by
  classical
  have hpow (x : ZMod p) (i : ℕ) : (-(x ^ 2)) ^ i = (-1) ^ i * x ^ (2 * i) := by
    rw [pow_mul, ← mul_pow]
    congr 1
    ring
  simp_rw [sub_eq_add_neg, add_comm a, add_pow, hpow]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
  have hl : (∑ x : ZMod p, x ^ (2 * half p)) = -1 := by
    let S : Finset (ZMod p) := Finset.univ.erase 0
    have hS : S.card = p - 1 := by simp [S, ZMod.card]
    have hh := twice_half p hp
    have hn := half_pos p hp
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p)), zero_pow (by omega), add_zero]
    change (∑ x ∈ S, x ^ (2 * half p)) = -1
    calc
      _ = ∑ _x ∈ S, (1 : ZMod p) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hh, ZMod.pow_card_sub_one_eq_one ((Finset.mem_erase.mp hx).1)]
      _ = -1 := by
        simp [hS, Nat.cast_sub hprime.out.pos]
  rw [Finset.sum_eq_single (half p)]
  · rw [hl]
    simp
  · intro i hi hneq
    have hlt : i < half p := by have := Finset.mem_range.mp hi; omega
    have hz : ∑ x : ZMod p, x ^ (2 * i) = 0 := by
      apply FiniteField.sum_pow_lt_card_sub_one
      rw [ZMod.card, ← twice_half p hp]
      omega
    rw [hz]
    simp
  · simp

theorem row_sum_mod (p : ℕ) [Fact p.Prime] (hp : Odd p) {j : ℕ}
    (hj₀ : 0 < j) (hj : j ≤ half p) :
    (2 : ZMod p) * (∑ i ∈ Finset.range (half p),
      (((j : ZMod p) ^ 2 - ((i + 1 : ℕ) : ZMod p) ^ 2) ^ half p)) =
      -((-1 : ZMod p) ^ half p) - 1 := by
  let a : ZMod p := (j : ZMod p) ^ 2
  have hh := full_quadratic_power_sum p hp a
  have hf (x : ZMod p) : (a - (-x) ^ 2) ^ half p = (a - x ^ 2) ^ half p := by simp
  rw [half_symmetric_sum p hp _ hf] at hh
  have ha : (a - (0 : ZMod p) ^ 2) ^ half p = 1 := by
    simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, a, ← pow_mul, twice_half p hp]
    exact ZMod.pow_card_sub_one_eq_one (index_ne_zero_mod p hj₀ hj)
  rw [ha] at hh
  linear_combination hh


private theorem field_two_ne_zero (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hp2 := (Fact.out (p := p.Prime)).two_le
  have hlt : 2 < p := by rw [Nat.odd_iff] at hp; omega
  have hz := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
  exact (not_le_of_gt hlt) (Nat.le_of_dvd (by decide) hz)

/-- The unperturbed matrix on the positive half of the residues. -/
def positiveMatrix (p : ℕ) [Fact p.Prime] : Matrix (Fin (half p)) (Fin (half p)) ℤ :=
  fun j k ↦ legendreSym p (((j : ℕ) + 1 : ℤ) ^ 2 - ((k : ℕ) + 1 : ℤ) ^ 2)

theorem positiveMatrix_row_sum (p : ℕ) [hprime : Fact p.Prime] (hp : Odd p)
    (j : Fin (half p)) :
    (∑ k : Fin (half p), positiveMatrix p j k) = if p % 4 = 1 then -1 else 0 := by
  let S := ∑ i ∈ Finset.range (half p),
    legendreSym p ((((j : ℕ) + 1 : ℕ) : ℤ) ^ 2 - ((i + 1 : ℕ) : ℤ) ^ 2)
  let v : ℤ := if p % 4 = 1 then -1 else 0
  have hS : (∑ k : Fin (half p), positiveMatrix p j k) = S := by
    simpa only [S, positiveMatrix, Nat.cast_add, Nat.cast_one] using
      (Fin.sum_univ_eq_sum_range
        (fun k : ℕ ↦ legendreSym p ((((j : ℕ) + 1 : ℕ) : ℤ) ^ 2 - ((k + 1 : ℕ) : ℤ) ^ 2))
        (half p))
  rw [hS]
  change S = v
  have hmod : (S : ZMod p) = (v : ZMod p) := by
    have hm := row_sum_mod p hp (j := (j : ℕ) + 1) (by omega) (by omega)
    have hcast : (S : ZMod p) = ∑ i ∈ Finset.range (half p),
        (((((j : ℕ) + 1 : ℕ) : ZMod p) ^ 2 - ((i + 1 : ℕ) : ZMod p) ^ 2) ^ half p) := by
      simp [S, legendreSym.eq_pow, half_eq_div p hp]
    rw [← hcast] at hm
    apply mul_left_cancel₀ (field_two_ne_zero p hp)
    rcases odd_mod_four p hp with h | h
    · have he : Even (half p) := Nat.even_iff.mpr (by unfold half; omega)
      rw [hm, he.neg_one_pow]
      simp [v, h]
      ring
    · have ho : Odd (half p) := Nat.odd_iff.mpr (by unfold half; omega)
      rw [hm, ho.neg_one_pow]
      simp [v, show p % 4 ≠ 1 by omega]
  have hbound (k : ℕ) : -1 ≤ legendreSym p
      ((((j : ℕ) + 1 : ℕ) : ℤ) ^ 2 - ((k + 1 : ℕ) : ℤ) ^ 2) ∧
      legendreSym p ((((j : ℕ) + 1 : ℕ) : ℤ) ^ 2 - ((k + 1 : ℕ) : ℤ) ^ 2) ≤ 1 := by
    let a : ZMod p := (((((j : ℕ) + 1 : ℕ) : ℤ) ^ 2 - ((k + 1 : ℕ) : ℤ) ^ 2) : ℤ)
    change -1 ≤ quadraticChar (ZMod p) a ∧ quadraticChar (ZMod p) a ≤ 1
    rcases quadraticChar_isQuadratic (F := ZMod p) a with h | h | h <;> rw [h] <;> norm_num
  have hlo : -(half p : ℤ) ≤ S := by
    have h := Finset.sum_le_sum (s := Finset.range (half p)) (fun i _ ↦ (hbound i).1)
    simpa [S] using h
  have hhi : S ≤ (half p : ℤ) := by
    have h := Finset.sum_le_sum (s := Finset.range (half p)) (fun i _ ↦ (hbound i).2)
    simpa [S] using h
  have hv : -(half p : ℤ) ≤ v ∧ v ≤ (half p : ℤ) := by
    have := half_pos p hp
    unfold v
    split <;> omega
  have hcast : ((S + half p : ℤ) : ZMod p) = ((v + half p : ℤ) : ZMod p) := by
    push_cast
    rw [hmod]
  have hh := twice_half p hp
  have hpos := hprime.out.pos
  have heq := (ZMod.intCast_eq_intCast_iff' _ _ _).mp hcast
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at heq
  omega

theorem positiveMatrix_skew (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    (positiveMatrix p)ᵀ = -positiveMatrix p := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.neg_apply, positiveMatrix, positiveMatrix,
    show ((j : ℕ) + 1 : ℤ) ^ 2 - ((i : ℕ) + 1 : ℤ) ^ 2 =
      -(((i : ℕ) + 1 : ℤ) ^ 2 - ((j : ℕ) + 1 : ℤ) ^ 2) by ring,
    legendreSym.at_neg (p := p) (by omega), ZMod.χ₄_nat_eq_if_mod_four]
  simp [hp, show p % 2 ≠ 0 by omega]

end ChenSun
```

## ChenSunRankOne.lean

```lean
import ChenSunField
import Mathlib.Tactic.FieldSimp

open Matrix BigOperators

namespace ChenSun

section Field

variable {F : Type*} [Field F] {n : ℕ}

/-- A matrix with zero row and column sums under a rank-one perturbation.
The factor from the minor comes from summing the first row and first column. -/
theorem det_rank_one_zero_sums (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (u v : Fin (n + 1) → F) (w : F)
    (hrows : ∀ i, ∑ j, A i j = 0) (hcols : ∀ j, ∑ i, A i j = 0)
    (hu : (∑ i, u i) ≠ 0) :
    (A + w • Matrix.vecMulVec u v).det =
      w * (∑ i, u i) * (∑ i, v i) * (A.submatrix Fin.succ Fin.succ).det := by
  classical
  let B := A + w • Matrix.vecMulVec u v
  let B' := B.updateRow 0 (fun j ↦ ∑ i, B i j)
  let C := A.updateRow 0 (fun j ↦ w * (∑ i, u i) * v j)
  let C' := C.updateCol 0 (fun i ↦ ∑ j, C i j)
  have hB : B'.det = B.det := by
    have hs : (fun j ↦ ∑ i, B i j) = ∑ i, B i := by
      funext j
      change (∑ i, B i j) = (∑ i, (fun k ↦ B i k)) j
      exact (Finset.sum_apply j Finset.univ (fun i k ↦ B i k)).symm
    simpa only [B', hs, one_smul] using (Matrix.det_updateRow_sum B 0 (fun _ ↦ (1 : F)))
  have hB0 (j : Fin (n + 1)) : B' 0 j = w * (∑ i, u i) * v j := by
    simp only [B', Matrix.updateRow_self, B, Matrix.add_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, Finset.sum_add_distrib, hcols, zero_add]
    simp_rw [mul_left_comm w, ← mul_assoc]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring
  have hC : B'.det = C.det := by
    refine Matrix.det_eq_of_forall_row_eq_smul_add_const
      (fun i ↦ if i = 0 then 0 else u i / (∑ i, u i)) 0 (by simp) ?_
    intro i j
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · simp [hB0, C]
    · simp [B', B, C, Matrix.vecMulVec_apply]
      field_simp
  have hC' : C'.det = C.det := by
    simpa only [C', one_smul] using (Matrix.det_updateCol_sum C 0 (fun _ ↦ (1 : F)))
  have hC'0 : C' 0 0 = w * (∑ i, u i) * (∑ i, v i) := by
    simp [C', C, Finset.mul_sum]
  have hC's (i : Fin n) : C' i.succ 0 = 0 := by
    simp [C', C, hrows]
  have hminor : C'.submatrix Fin.succ Fin.succ = A.submatrix Fin.succ Fin.succ := by
    ext i j
    simp [C', C, Matrix.submatrix_apply]
  change B.det = _
  rw [← hB, hC, ← hC', Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  rw [hC'0]
  simp [hC's, hminor]

end Field

def skipFirst (n : ℕ) (i : Fin (n - 1)) : Fin n := ⟨(i : ℕ) + 1, by omega⟩

theorem det_rank_one_zero_sums_int {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (u v : Fin n → ℤ) (w : ℤ)
    (hrows : ∀ i, ∑ j, A i j = 0) (hcols : ∀ j, ∑ i, A i j = 0)
    (hu : (∑ i, u i) ≠ 0) :
    (A + w • Matrix.vecMulVec u v).det =
      w * (∑ i, u i) * (∑ i, v i) * (A.submatrix (skipFirst n) (skipFirst n)).det := by
  cases n with
  | zero => simp at hu
  | succ n =>
    let f := Int.castRingHom ℚ
    let B := A.map f
    let u' (i : Fin (n + 1)) : ℚ := u i
    let v' (i : Fin (n + 1)) : ℚ := v i
    have hr' (i) : ∑ j, B i j = 0 := by
      change (∑ j, (A i j : ℚ)) = 0
      exact_mod_cast hrows i
    have hc' (j) : ∑ i, B i j = 0 := by
      change (∑ i, (A i j : ℚ)) = 0
      exact_mod_cast hcols j
    have hu' : ∑ i, u' i ≠ 0 := by
      unfold u'
      exact_mod_cast hu
    have hB : (A + w • Matrix.vecMulVec u v).map f = B + (w : ℚ) • Matrix.vecMulVec u' v' := by
      ext i j
      change ((A i j + w * (u i * v j) : ℤ) : ℚ) =
        (A i j : ℚ) + (w : ℚ) * ((u i : ℚ) * (v j : ℚ))
      push_cast
      rfl
    have hM : (A.submatrix (skipFirst (n + 1)) (skipFirst (n + 1))).map f =
        B.submatrix Fin.succ Fin.succ := by
      ext i j
      rfl
    apply (Int.cast_injective (α := ℚ))
    push_cast
    change ((A + w • Matrix.vecMulVec u v).map f).det =
      (w : ℚ) * (∑ i, u' i) * (∑ i, v' i) *
        ((A.submatrix (skipFirst (n + 1)) (skipFirst (n + 1))).map f).det
    rw [hB, hM]
    exact det_rank_one_zero_sums B u' v' w hr' hc' hu'

end ChenSun
```

## ChenSunSkew.lean

```lean
import ChenSunRows
import ChenSunRankOne

open Matrix BigOperators

namespace ChenSun

def positiveVector (p : ℕ) [Fact p.Prime] : Fin (half p) → ℤ :=
  fun i ↦ legendreSym p ((i : ℕ) + 1 : ℤ)

def positiveMinor (p : ℕ) [Fact p.Prime] :
    Matrix (Fin (half p - 1)) (Fin (half p - 1)) ℤ :=
  (positiveMatrix p).submatrix (skipFirst (half p)) (skipFirst (half p))

theorem positiveVector_sum (p : ℕ) [Fact p.Prime] : (∑ i, positiveVector p i) = halfSum p := by
  unfold halfSum
  refine Finset.sum_bij (fun i _ ↦ (i : ℕ) + 1) ?_ ?_ ?_ ?_
  · intro i _
    apply Finset.mem_Icc.mpr
    exact ⟨by omega, by omega⟩
  · intro i _ j _ h
    apply Fin.ext
    omega
  · intro j hj
    obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp hj
    exact ⟨⟨j - 1, by omega⟩, Finset.mem_univ _, by change j - 1 + 1 = j; omega⟩
  · intro i _
    simp [positiveVector]

theorem entryMatrix_positive (p : ℕ) [Fact p.Prime] (w : ℤ) :
    (entryMatrix p 1 w : Matrix (Fin (half p)) (Fin (half p)) ℤ) =
      positiveMatrix p + w • Matrix.vecMulVec (positiveVector p) (positiveVector p) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
    entryMatrix, positiveMatrix, positiveVector, Nat.cast_one, legendreSym.mul]
  ring

theorem positiveMatrix_det_zero_three (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    (positiveMatrix p).det = 0 := by
  have ho : Odd p := Nat.odd_iff.mpr (by omega)
  have hs (i : Fin (half p)) : ∑ j, positiveMatrix p i j = 0 := by
    rw [positiveMatrix_row_sum p ho, ite_eq_right (by omega : p % 4 ≠ 1)]
  let i : Fin (half p) := ⟨0, half_pos p ho⟩
  let M := (positiveMatrix p).updateCol i (fun j ↦ ∑ k, positiveMatrix p j k)
  have hM : M.det = (positiveMatrix p).det := by
    simpa only [M, one_smul] using (Matrix.det_updateCol_sum (positiveMatrix p) i (fun _ ↦ 1))
  rw [← hM]
  rw [← Matrix.det_transpose]
  apply Matrix.det_eq_zero_of_row_eq_zero i
  intro j
  simp [M, hs]

/-- The integral defining coefficient in the (3 mod 4) class is a minor determinant
times the square of the half-range character sum. -/
theorem D_odd_minor (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) (w : ℤ) :
    D p 1 w = w * (halfSum p) ^ 2 * (positiveMinor p).det := by
  have ho : Odd p := Nat.odd_iff.mpr (by omega)
  have hs (i : Fin (half p)) : ∑ j, positiveMatrix p i j = 0 := by
    rw [positiveMatrix_row_sum p ho, ite_eq_right (by omega : p % 4 ≠ 1)]
  have ht (j : Fin (half p)) : ∑ i, positiveMatrix p i j = 0 := by
    have h (i : Fin (half p)) : positiveMatrix p i j = -positiveMatrix p j i :=
      congrFun (congrFun (positiveMatrix_skew p hp) j) i
    simp_rw [h, Finset.sum_neg_distrib, hs j, neg_zero]
  have hne : (∑ i, positiveVector p i) ≠ 0 := by
    rw [positiveVector_sum]
    exact halfSum_ne_zero p hp
  have h := det_rank_one_zero_sums_int (positiveMatrix p) (positiveVector p) (positiveVector p)
    w hs ht hne
  rw [positiveVector_sum] at h
  unfold D
  rw [entryMatrix_positive, entryMatrix_positive, zero_smul, add_zero,
    positiveMatrix_det_zero_three p hp, sub_zero, h, positiveMinor, pow_two]
  ring

theorem cp_square_eq_minor (p c : ℕ) [Fact p.Prime] (hp : p % 4 = 3) (hc : IsCp p c) :
    (c : ℤ) ^ 2 = (positiveMinor p).det := by
  have h := hc.2.2.2.2 hp 1
  rw [D_odd_minor p hp, one_mul, one_mul, mul_pow] at h
  apply mul_right_cancel₀ (pow_ne_zero _ (halfSum_ne_zero p hp))
  rw [mul_comm ((positiveMinor p).det)]
  exact h.symm

end ChenSun
```

## ChenSunSigned.lean

```lean
import ChenSunSkew

namespace ChenSun

theorem signed_character_iff (p c : ℕ) [Fact p.Prime] (hp : p % 4 = 3)
    (hc : Odd c) (f : ℤ) (hf : f ^ 2 = (c : ℤ) ^ 2) :
    jacobiSym (p : ℤ) c = 1 ↔ legendreSym p f = ZMod.χ₄ (f : ZMod 4) := by
  have ho : Odd p := Nat.odd_iff.mpr (by omega)
  have hrec := jacobiSym.quadratic_reciprocity ho hc
  rw [← jacobiSym.legendreSym.to_jacobiSym p (c : ℤ), pow_mul,
    ZMod.neg_one_pow_div_two_of_three_mod_four hp] at hrec
  have h4c : ZMod.χ₄ (c : ZMod 4) = (-1 : ℤ) ^ (c / 2) :=
    ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hc)
  have h4sq : ZMod.χ₄ (c : ZMod 4) ^ 2 = 1 := by
    rw [h4c, ← pow_mul, mul_comm (c / 2), pow_mul, neg_one_sq, one_pow]
  have hrec' : jacobiSym (p : ℤ) c = ZMod.χ₄ (c : ZMod 4) * legendreSym p (c : ℤ) := by
    rw [hrec, h4c]
  have hiff : jacobiSym (p : ℤ) c = 1 ↔ legendreSym p (c : ℤ) = ZMod.χ₄ (c : ZMod 4) := by
    rw [hrec']
    constructor
    · intro h
      linear_combination ZMod.χ₄ (c : ZMod 4) * h - legendreSym p (c : ℤ) * h4sq
    · intro h
      rw [h, ← pow_two, h4sq]
  have hfor : (f - (c : ℤ)) * (f + (c : ℤ)) = 0 := by linear_combination hf
  rcases mul_eq_zero.mp hfor with h | h
  · rw [sub_eq_zero.mp h]
    simpa only [Int.cast_natCast] using hiff
  · rw [eq_neg_of_add_eq_zero_left h]
    have h4p : ZMod.χ₄ (p : ZMod 4) = -1 := by
      rw [ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp ho),
        ZMod.neg_one_pow_div_two_of_three_mod_four hp]
    rw [legendreSym.at_neg (p := p) (by omega), h4p, Int.cast_neg, Int.cast_natCast]
    have hneg : ZMod.χ₄ (-(c : ZMod 4)) = -ZMod.χ₄ (c : ZMod 4) := by
      rw [← neg_one_mul, map_mul, show ZMod.χ₄ (-1 : ZMod 4) = -1 by decide, neg_one_mul]
    rw [hneg, neg_one_mul, neg_inj]
    exact hiff

theorem odd_jacobi_iff_minor_root (p c : ℕ) [Fact p.Prime] (hp : p % 4 = 3)
    (hc : IsCp p c) (f : ℤ) (hf : f ^ 2 = (positiveMinor p).det) :
    jacobiSym (p : ℤ) c = 1 ↔ legendreSym p f = ZMod.χ₄ (f : ZMod 4) :=
  signed_character_iff p c hp hc.2.2.1 f (hf.trans (cp_square_eq_minor p c hp hc).symm)

end ChenSun
```

## ChenSunAlternating.lean

```lean
import ChenSunSkew
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Rat.Lemmas

open Matrix BigOperators

namespace ChenSun

private theorem skew_diag_zero {F : Type*} [Field F] [CharZero F]
    {ι : Type*} {A : Matrix ι ι F} (h : Aᵀ = -A) (i : ι) : A i i = 0 := by
  have he : A i i = -A i i := congrFun (congrFun h i) i
  linear_combination (1 / 2 : F) * he

private theorem skew_block_square {F : Type*} [Field F] [CharZero F]
    {n : ℕ} (A : Matrix (Fin (2 * n + 2)) (Fin (2 * n + 2)) F) (hA : Aᵀ = -A)
    (h01 : A 0 1 ≠ 0)
    (ih : ∀ B : Matrix (Fin (2 * n)) (Fin (2 * n)) F, Bᵀ = -B → IsSquare B.det) :
    IsSquare A.det := by
  classical
  let e : Fin 2 ⊕ Fin (2 * n) ≃ Fin (2 * n + 2) :=
    finSumFinEquiv.trans (finCongr (by omega))
  let T := A.submatrix e e
  let J : Matrix (Fin 2) (Fin 2) F := T.submatrix Sum.inl Sum.inl
  let B : Matrix (Fin 2) (Fin (2 * n)) F := T.submatrix Sum.inl Sum.inr
  let C : Matrix (Fin (2 * n)) (Fin 2) F := T.submatrix Sum.inr Sum.inl
  let D : Matrix (Fin (2 * n)) (Fin (2 * n)) F := T.submatrix Sum.inr Sum.inr
  have hT (i j) : T j i = -T i j := by
    exact congrFun (congrFun hA (e i)) (e j)
  have hJ : Jᵀ = -J := by
    ext i j
    exact hT (Sum.inl i) (Sum.inl j)
  have hD : Dᵀ = -D := by
    ext i j
    exact hT (Sum.inr i) (Sum.inr j)
  have hC : C = -Bᵀ := by
    ext i j
    exact hT (Sum.inl j) (Sum.inr i)
  have hB : Bᵀ = -C := by rw [hC, neg_neg]
  have ha : J 0 1 ≠ 0 := by
    change A (e (Sum.inl 0)) (e (Sum.inl 1)) ≠ 0
    have h0 : e (Sum.inl 0) = 0 := Fin.ext rfl
    have h1 : e (Sum.inl 1) = 1 := Fin.ext rfl
    simpa only [h0, h1] using h01
  let a := J 0 1
  have h10 : J 1 0 = -a := congrFun (congrFun hJ 0) 1
  have hdet : J.det = a ^ 2 := by
    rw [Matrix.det_fin_two, skew_diag_zero hJ, skew_diag_zero hJ, h10]
    change 0 * 0 - a * -a = a ^ 2
    ring
  let : Invertible J := Matrix.invertibleOfIsUnitDet J
    (isUnit_iff_ne_zero.mpr (by rw [hdet]; exact pow_ne_zero _ ha))
  let K : Matrix (Fin 2) (Fin 2) F := !![0, -a⁻¹; a⁻¹, 0]
  have hK : ⅟J = K := by
    apply invOf_eq_right_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, K, h10, skew_diag_zero hJ,
        show a ≠ 0 from ha, a]
  have hKt : Kᵀ = -K := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [K]
  have hS : (D - C * K * B)ᵀ = -(D - C * K * B) := by
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      hD, hB, hKt, hC]
    simp [Matrix.mul_assoc, sub_eq_add_neg, add_comm]
  have heq : Matrix.fromBlocks J B C D = T := by
    ext i j
    cases i <;> cases j <;> rfl
  have hdetT : T.det = A.det := Matrix.det_submatrix_equiv_self e A
  rw [← hdetT, ← heq, Matrix.det_fromBlocks₁₁, hdet, hK]
  exact (show IsSquare (a ^ 2) from ⟨a, pow_two a⟩).mul (ih _ hS)

/-- A skew-symmetric matrix of even size over a characteristic-zero field has square determinant. -/
theorem skew_det_isSquare {F : Type*} [Field F] [CharZero F] (n : ℕ)
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) F) (hA : Aᵀ = -A) :
    IsSquare A.det := by
  classical
  induction n with
  | zero =>
    simp
  | succ n ih =>
    change Matrix (Fin (2 * n + 2)) (Fin (2 * n + 2)) F at A
    by_cases h : ∀ j, A 0 j = 0
    · rw [Matrix.det_eq_zero_of_row_eq_zero 0 h]
      exact IsSquare.zero
    push Not at h
    obtain ⟨j, hj⟩ := h
    have hn : j ≠ 0 := by rintro rfl; exact hj (skew_diag_zero hA 0)
    let σ := Equiv.swap (1 : Fin (2 * n + 2)) j
    let A' := A.submatrix σ σ
    have hσzero : σ 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by simp) hn.symm
    have hσone : σ 1 = j := Equiv.swap_apply_left _ _
    have h01 : A' 0 1 ≠ 0 := by simpa only [A', Matrix.submatrix_apply, hσzero, hσone] using hj
    have hA' : A'ᵀ = -A' := by
      ext i k
      exact congrFun (congrFun hA (σ i)) (σ k)
    rw [← Matrix.det_submatrix_equiv_self σ A]
    exact skew_block_square A' hA' h01 ih

end ChenSun
```

## ChenSunOddExistence.lean

```lean
import ChenSunAlternating

open Matrix BigOperators

namespace ChenSun

private theorem positiveMinor_skew (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    (positiveMinor p)ᵀ = -positiveMinor p := by
  ext i j
  exact congrFun (congrFun (positiveMatrix_skew p hp) (skipFirst (half p) i))
    (skipFirst (half p) j)

theorem positiveMinor_offdiag_sign (p : ℕ) [Fact p.Prime] (hp : Odd p)
    {i j : Fin (half p - 1)} (h : i ≠ j) :
    positiveMinor p i j = 1 ∨ positiveMinor p i j = -1 := by
  have hi : (i : ℕ) + 2 ≤ half p := by omega
  have hj : (j : ℕ) + 2 ≤ half p := by omega
  let i' : Fin (half p + 1) := ⟨(i : ℕ) + 2, by omega⟩
  let j' : Fin (half p + 1) := ⟨(j : ℕ) + 2, by omega⟩
  have hij : i' ≠ j' := by
    intro he
    apply h
    apply Fin.ext
    have h' := congrArg (Fin.val : Fin (half p + 1) → ℕ) he
    change (i : ℕ) + 2 = (j : ℕ) + 2 at h'
    omega
  have hz : point p i' - point p j' ≠ 0 :=
    sub_ne_zero.mpr ((point_injective p hp).ne hij)
  have hcast : (((((i : ℕ) + 1 + 1 : ℤ) ^ 2 -
      ((j : ℕ) + 1 + 1 : ℤ) ^ 2) : ℤ) : ZMod p) ≠ 0 := by
    simpa [point, i', j', Nat.cast_add, Nat.cast_one, add_assoc] using hz
  exact legendreSym.eq_one_or_neg_one p hcast

private theorem positiveMinor_cast_two (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    (positiveMinor p).map (Int.castRingHom (ZMod 2)) =
      (1 : Matrix (Fin (half p - 1)) (Fin (half p - 1)) (ZMod 2)) +
        Matrix.of (fun _ _ ↦ 1) := by
  classical
  ext i j
  change ((positiveMinor p i j : ℤ) : ZMod 2) = _
  by_cases h : i = j
  · subst j
    simp [positiveMinor, positiveMatrix]
    decide
  · rcases positiveMinor_offdiag_sign p hp h with h' | h' <;> simp [h, h']

theorem positiveMinor_det_odd (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    Odd (positiveMinor p).det := by
  classical
  let n := half p - 1
  let J : Matrix (Fin n) (Fin n) (ZMod 2) := Matrix.of (fun _ _ ↦ 1)
  let M : Matrix (Fin n) (Fin n) (ZMod 2) := 1 + J
  have he : Even n := Nat.even_iff.mpr (by unfold n half; omega)
  have hJ : J * J = 0 := by
    ext i j
    simp [Matrix.mul_apply, J, he.natCast_zmod_two]
  have hM : M * M = 1 := by
    unfold M
    rw [Matrix.add_mul, Matrix.mul_add J, Matrix.one_mul, Matrix.mul_one, hJ, add_zero]
    rw [add_assoc]
    have hz : J + J = 0 := by
      ext i j
      simp [J]
      decide
    rw [hz, add_zero]
  have hd : M.det = 1 := by
    have h := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact (show ∀ z : ZMod 2, z * z = 1 → z = 1 by decide) _ h
  have hmap : ((positiveMinor p).det : ZMod 2) =
      ((positiveMinor p).map (Int.castRingHom (ZMod 2))).det :=
    (Int.castRingHom (ZMod 2)).map_det _
  rw [positiveMinor_cast_two p (Nat.odd_iff.mpr (by omega))] at hmap
  exact ZMod.intCast_eq_one_iff_odd.mp (hmap.trans hd)

theorem skew_det_isSquare_int {n : ℕ} (he : Even n)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : Aᵀ = -A) :
    IsSquare A.det := by
  obtain ⟨m, hm⟩ := he
  obtain rfl : n = 2 * m := by omega
  let B := A.map (Int.castRingHom ℚ)
  have hB : Bᵀ = -B := by
    ext i j
    change (A j i : ℚ) = -(A i j : ℚ)
    exact_mod_cast congrFun (congrFun hA i) j
  apply Rat.isSquare_intCast_iff.mp
  have hmap : (A.det : ℚ) = B.det := (Int.castRingHom ℚ).map_det _
  rw [hmap]
  exact skew_det_isSquare m B hB

theorem cp_exists_three_mod_four (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    ∃! c : ℕ, IsCp p c := by
  have he : Even (half p - 1) := Nat.even_iff.mpr (by unfold half; omega)
  obtain ⟨f, hf⟩ :=
    skew_det_isSquare_int he (positiveMinor p) (positiveMinor_skew p hp)
  have hc : ((f.natAbs : ℤ) ^ 2) = (positiveMinor p).det := by
    rw [pow_two, ← Int.natCast_mul, Int.natAbs_mul_self, hf]
  have hodd : Odd f.natAbs := by
    have hd := ZMod.intCast_eq_one_iff_odd.mpr (positiveMinor_det_odd p hp)
    rw [← hc, Int.cast_pow, Int.cast_natCast] at hd
    apply ZMod.natCast_eq_one_iff_odd.mp
    exact (show ∀ z : ZMod 2, z ^ 2 = 1 → z = 1 by decide) _ hd
  have hspec : IsCp p f.natAbs := by
    refine ⟨Nat.odd_iff.mpr (by omega), ?_, hodd, fun h ↦ by omega, ?_⟩
    · have := Nat.odd_iff.mp hodd
      omega
    · intro _ w
      rw [D_odd_minor p hp, ← hc, mul_pow]
      ring
  exact ⟨f.natAbs, hspec, fun c hc ↦ cp_unique p hc hspec⟩

theorem cp_spec_three_mod_four (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) (ho : Odd p) :
    IsCp p (cp p ho) := by
  obtain ⟨c, hc, _⟩ := cp_exists_three_mod_four p hp
  rw [cp_eq_of_spec p c ho hc]
  exact hc

end ChenSun
```

## ChenSunOddField.lean

```lean
import ChenSunOddExistence

open Matrix BigOperators

namespace ChenSun

private theorem trim_power_sum {R : Type*} [CommRing R] (n : ℕ) (hn : Odd (n + 2))
    (x y : R) (hx : x ^ (n + 2) = 1) (hy : y ^ (n + 2) = 1) :
    x * y * (∑ i : Fin (n + 1),
      x ^ (i.rev : ℕ) * (-1) ^ ((i : ℕ) + 1) * ((n + 2).choose ((i : ℕ) + 1) : R) *
        y ^ (i : ℕ)) = (x - y) ^ (n + 2) := by
  classical
  conv_rhs =>
    rw [← binomial_sum x y (n + 2), Fin.sum_univ_succ]
    arg 2
    rw [Fin.sum_univ_castSucc]
  have hzero : x ^ ((0 : Fin (n + 3)).rev : ℕ) * binomialWeight (n + 2) 0 *
      y ^ ((0 : Fin (n + 3)) : ℕ) = 1 := by
    simp [binomialWeight, hx]
  rw [hzero]
  have hlast : x ^ ((Fin.last (n + 1)).succ.rev : ℕ) *
      binomialWeight (n + 2) (Fin.last (n + 1)).succ * y ^ ((Fin.last (n + 1)).succ : ℕ) = -1 := by
    simp [binomialWeight, hn.neg_one_pow, hy]
  rw [hlast]
  have hstep (i : Fin (n + 1)) :
      ((i.castSucc.succ.rev : Fin (n + 3)) : ℕ) = (i.rev : ℕ) + 1 := by
    simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
    omega
  rw [add_comm (1 : R), add_assoc, neg_add_cancel, add_zero]
  simp only [Finset.mul_sum, hstep, Fin.val_succ, Fin.val_castSucc, binomialWeight]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ, pow_succ y]
  ring

/-- Vandermonde column weights in the (3 mod4) case after the two end terms cancel. -/
def trimWeights (p n : ℕ) (i : Fin (n + 1)) : ZMod p :=
  (-1) ^ ((i : ℕ) + 1) * ((n + 2).choose ((i : ℕ) + 1) : ZMod p)

theorem odd_minor_mod_factorization (p n : ℕ) [Fact p.Prime]
    (hp : p % 4 = 3) (hh : half p = n + 2) :
    let e : Fin (n + 1) ≃ Fin (half p - 1) := finCongr (by omega)
    let x : Fin (n + 1) → ZMod p := fun i ↦ (((i : ℕ) + 2 : ℕ) : ZMod p) ^ 2
    let V := Matrix.vandermonde x
    let X := Matrix.diagonal x
    ((positiveMinor p).map (Int.castRingHom (ZMod p))).submatrix e e =
      X * (V * reversedDiagonal (trimWeights p n) * Vᵀ) * X := by
  classical
  dsimp only
  let x : Fin (n + 1) → ZMod p := fun i ↦ (((i : ℕ) + 2 : ℕ) : ZMod p) ^ 2
  let V := Matrix.vandermonde x
  let X := Matrix.diagonal x
  have ho : Odd p := Nat.odd_iff.mpr (by omega)
  have hno : Odd (n + 2) := Nat.odd_iff.mpr (by
    have h := hh
    unfold half at h
    omega)
  have hx (i) : x i ^ (n + 2) = 1 := by
    change ((((i : ℕ) + 2 : ℕ) : ZMod p) ^ 2) ^ (n + 2) = 1
    rw [← pow_mul, ← hh, twice_half p ho]
    exact ZMod.pow_card_sub_one_eq_one (index_ne_zero_mod p (by omega) (by omega))
  ext i j
  change ((legendreSym p (((i : ℕ) + 1 + 1 : ℤ) ^ 2 -
      ((j : ℕ) + 1 + 1 : ℤ) ^ 2)) : ZMod p) =
    (X * (V * reversedDiagonal (trimWeights p n) * Vᵀ) * X) i j
  rw [legendreSym.eq_pow, ← half_eq_div p ho, hh]
  have hcast (i : Fin (n + 1)) : ((((i : ℕ) + 1 + 1 : ℤ) ^ 2 : ℤ) : ZMod p) = x i := by
    simp [x, Nat.cast_add, add_assoc]
  rw [Int.cast_sub, hcast, hcast]
  unfold X
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, vandermonde_reversedDiagonal]
  rw [← trim_power_sum n hno (x i) (x j) (hx i) (hx j)]
  have hprod (k : Fin (n + 1)) :
      x i ^ (k.rev : ℕ) * trimWeights p n k * x j ^ (k : ℕ) =
      x i ^ (k.rev : ℕ) * (-1) ^ ((k : ℕ) + 1) *
        ((n + 2).choose ((k : ℕ) + 1) : ZMod p) * x j ^ (k : ℕ) := by
    unfold trimWeights
    ring
  simp_rw [hprod]
  ring

end ChenSun
```

## ChenSunPfaffian.lean

```lean
import ChenSunField
import Mathlib.Algebra.BigOperators.Intervals

open Matrix BigOperators

namespace ChenSun

/-- Delete the index zero and the positive index `i.succ` in increasing order. -/
def skipPair (m : ℕ) (i : Fin (2 * m + 1)) (j : Fin (2 * m)) : Fin (2 * (m + 1)) :=
  (i.succAbove j).succ

theorem skipPair_strictMono (m : ℕ) (i : Fin (2 * m + 1)) :
    StrictMono (skipPair m i) := by
  intro a b h
  unfold skipPair
  rw [Fin.succ_lt_succ_iff]
  exact Fin.strictMono_succAbove i h

/-- Recursive first-row expansion on matrices of even size. Its convention is
that the pair with smaller index first contributes the upper-triangular entry. -/
def pfaffian {R : Type*} [CommRing R] (m : ℕ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) R → R :=
  match m with
  | 0 => fun _ ↦ 1
  | m + 1 => fun A ↦ ∑ i : Fin (2 * m + 1),
    (-1) ^ (i : ℕ) * A 0 i.succ * pfaffian m (A.submatrix (skipPair m i) (skipPair m i))

theorem pfaffian_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (m : ℕ) (A : Matrix (Fin (2 * m)) (Fin (2 * m)) R) :
    f (pfaffian m A) = pfaffian m (A.map f) := by
  induction m with
  | zero => simp [pfaffian]
  | succ m ih =>
    rw [pfaffian, pfaffian, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, map_mul, map_pow, map_neg, map_one, ih]
    rfl

theorem pfaffian_congr_upper {R : Type*} [CommRing R] (m : ℕ)
    (A B : Matrix (Fin (2 * m)) (Fin (2 * m)) R)
    (h : ∀ i j, i < j → A i j = B i j) :
    pfaffian m A = pfaffian m B := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [pfaffian]
    apply Finset.sum_congr rfl
    intro i _
    rw [h 0 i.succ (Fin.succ_pos i)]
    congr 1
    apply ih
    intro a b hab
    exact h _ _ (skipPair_strictMono m i hab)

private theorem alternating_odd_sum {R : Type*} [CommRing R] (m : ℕ) :
    (∑ i : Fin (2 * m + 1), (-1 : R) ^ (i : ℕ)) = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ (-1 : R) ^ i)]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, pow_succ (-1 : R) (2 * m + 1)]
    ring

theorem pfaffian_of_upper_one {R : Type*} [CommRing R] (m : ℕ)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) R) (h : ∀ i j, i < j → A i j = 1) :
    pfaffian m A = 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pfaffian]
    have hpf (i : Fin (2 * m + 1)) :
        pfaffian m (A.submatrix (skipPair m i) (skipPair m i)) = 1 :=
      ih _ (fun a b hab ↦ h _ _ (skipPair_strictMono m i hab))
    simp_rw [hpf, h 0 _ (Fin.succ_pos _), mul_one]
    exact alternating_odd_sum m

theorem pfaffian_odd_of_upper_signs (m : ℕ)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℤ)
    (h : ∀ i j, i < j → A i j = 1 ∨ A i j = -1) :
    Odd (pfaffian m A) := by
  apply ZMod.intCast_eq_one_iff_odd.mp
  show Int.castRingHom (ZMod 2) (pfaffian m A) = _
  rw [pfaffian_map]
  apply pfaffian_of_upper_one
  intro i j hij
  rcases h i j hij with he | he <;> simp [he]

end ChenSun
```

## ChenSunPfaffianModFour.lean

```lean
import ChenSunPfaffian

open Matrix BigOperators

namespace ChenSun

private def reductionTwo : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)

private theorem twice_odd_mod_four (x : ZMod 4) (hx : reductionTwo x = 1) : 2 * x = 2 :=
  (show ∀ x, reductionTwo x = 1 → 2 * x = 2 by decide) x hx

private theorem pfaffian_reductionTwo (m : ℕ) (A : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 4))
    (h : ∀ i j, i < j → reductionTwo (A i j) = 1) :
    reductionTwo (pfaffian m A) = 1 := by
  rw [pfaffian_map]
  exact pfaffian_of_upper_one m _ h

set_option backward.isDefEq.respectTransparency false in
private theorem pfaffian_flip (m : ℕ) (A B : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 4))
    (hA : ∀ i j, i < j → reductionTwo (A i j) = 1)
    (a b : Fin (2 * m)) (hab : a < b)
    (hB : ∀ i j, i < j → B i j = A i j + if i = a ∧ j = b then 2 else 0) :
    pfaffian m B - pfaffian m A = 2 := by
  classical
  induction m with
  | zero => exact Fin.elim0 a
  | succ m ih =>
    let U (T : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) (ZMod 4))
        (i : Fin (2 * m + 1)) := T.submatrix (skipPair m i) (skipPair m i)
    have hu (i : Fin (2 * m + 1)) : ∀ j k, j < k → reductionTwo (U A i j k) = 1 :=
      fun j k hjk ↦ hA _ _ (skipPair_strictMono m i hjk)
    have htwo (i : Fin (2 * m + 1)) : (2 : ZMod 4) * pfaffian m (U A i) = 2 :=
      twice_odd_mod_four _ (pfaffian_reductionTwo m _ (hu i))
    have hsign (i : Fin (2 * m + 1)) : (2 : ZMod 4) * (-1) ^ (i : ℕ) = 2 := by
      apply twice_odd_mod_four
      simp [reductionTwo, show (-1 : ZMod 2) = 1 by decide]
    simp only [pfaffian, ← Finset.sum_sub_distrib]
    change (∑ i : Fin (2 * m + 1),
      ((-1) ^ (i : ℕ) * B 0 i.succ * pfaffian m (U B i) -
        (-1) ^ (i : ℕ) * A 0 i.succ * pfaffian m (U A i))) = 2
    refine Fin.cases ?_ (fun ia ↦ ?_) a hab hB
    · intro hab hB
      obtain ⟨ib, rfl⟩ := Fin.exists_succ_eq.mpr (ne_of_gt hab)
      have he (i : Fin (2 * m + 1)) : pfaffian m (U B i) = pfaffian m (U A i) := by
        apply pfaffian_congr_upper
        intro j k hjk
        change B (skipPair m i j) (skipPair m i k) = _
        rw [hB _ _ (skipPair_strictMono m i hjk)]
        simp [skipPair, U]
      simp only [he]
      let g (i : Fin (2 * m + 1)) : ZMod 4 :=
        (-1) ^ (i : ℕ) * B 0 i.succ * pfaffian m (U A i) -
          (-1) ^ (i : ℕ) * A 0 i.succ * pfaffian m (U A i)
      change (∑ i, g i) = 2
      rw [Finset.sum_eq_single (f := g) ib]
      · unfold g
        rw [hB _ _ (Fin.succ_pos ib)]
        simp only [and_self, ite_true]
        calc
          _ = ((-1 : ZMod 4) ^ (ib : ℕ)) * (2 * pfaffian m (U A ib)) := by ring
          _ = 2 := by rw [htwo, mul_comm, hsign]
      · intro i _ hne
        unfold g
        rw [hB _ _ (Fin.succ_pos i)]
        simp [hne]
      · simp
    · intro hab hB
      obtain ⟨ib, rfl⟩ := Fin.exists_succ_eq.mpr (ne_of_gt ((Fin.succ_pos ia).trans hab))
      have hne : ia ≠ ib := fun h ↦ hab.ne (congrArg Fin.succ h)
      have hb0 (i : Fin (2 * m + 1)) : B 0 i.succ = A 0 i.succ := by
        rw [hB _ _ (Fin.succ_pos i)]
        simp [ne_of_lt (Fin.succ_pos ia)]
      simp only [hb0, ← mul_sub]
      have hdiff (i : Fin (2 * m + 1)) :
          pfaffian m (U B i) - pfaffian m (U A i) =
            if ia = i ∨ ib = i then 0 else 2 := by
        by_cases hi : ia = i ∨ ib = i
        · rw [ite_eq_left hi, sub_eq_zero]
          apply pfaffian_congr_upper
          intro j k hjk
          change B (skipPair m i j) (skipPair m i k) = _
          rw [hB _ _ (skipPair_strictMono m i hjk)]
          have hn (l : Fin (2 * m)) : skipPair m i l ≠ i.succ :=
            fun h ↦ Fin.succAbove_ne i l (Fin.succ_injective _ h)
          rcases hi with rfl | rfl
          · simp [hn j, U]
          · simp [hn k, U]
        · rw [ite_eq_right hi]
          obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (fun h ↦ hi (Or.inl h))
          obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (fun h ↦ hi (Or.inr h))
          have hjs : skipPair m i j = ia.succ := congrArg Fin.succ hj
          have hks : skipPair m i k = ib.succ := congrArg Fin.succ hk
          have hjk : j < k := (skipPair_strictMono m i).lt_iff_lt.mp (by rwa [hjs, hks])
          apply ih (U A i) (U B i) (hu i) j k hjk
          intro s t hst
          change B (skipPair m i s) (skipPair m i t) = _
          rw [hB _ _ (skipPair_strictMono m i hst), ← hjs, ← hks]
          simp only [(skipPair_strictMono m i).injective.eq_iff, U, Matrix.submatrix_apply]
      simp_rw [hdiff, mul_ite, mul_zero]
      have hmul (i : Fin (2 * m + 1)) :
          ((-1 : ZMod 4) ^ (i : ℕ) * A 0 i.succ) * 2 = 2 := by
        rw [mul_comm]
        apply twice_odd_mod_four
        simp only [map_mul, map_pow, map_neg, map_one, show (-1 : ZMod 2) = 1 by decide,
          one_pow, one_mul]; exact hA 0 i.succ (Fin.succ_pos i)
      simp_rw [hmul]
      let S : Finset (Fin (2 * m + 1)) := (Finset.univ.erase ia).erase ib
      have hS : S = Finset.univ.filter (fun i ↦ ¬ (ia = i ∨ ib = i)) := by
        ext i
        simp [S, eq_comm, and_comm]
      have hcard : S.card + 2 = 2 * m + 1 := by
        have ha := Finset.card_erase_add_one (Finset.mem_univ ia)
        have hb := Finset.card_erase_add_one
          (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ ib⟩)
        change S.card + 1 = (Finset.univ.erase ia).card at hb
        change (Finset.univ.erase ia).card + 1 = Fintype.card (Fin (2 * m + 1)) at ha
        rw [Fintype.card_fin] at ha
        omega
      classical
      rw [show (∑ i : Fin (2 * m + 1), if ia = i ∨ ib = i then (0 : ZMod 4) else 2) =
          ∑ i ∈ S, (2 : ZMod 4) by
            rw [hS]
            have hsum := Finset.sum_filter (s := (Finset.univ : Finset (Fin (2 * m + 1))))
              (fun i ↦ ¬ (ia = i ∨ ib = i)) (fun _ ↦ (2 : ZMod 4))
            refine Eq.trans ?_ hsum.symm
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : ia = i ∨ ib = i <;> simp [hi]]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hz := congrArg (fun n : ℕ ↦ (n : ZMod 4)) hcard
      push_cast at hz
      have hz4 : (4 : ZMod 4) = 0 := by decide
      linear_combination 2 * hz + ((m : ZMod 4) - 1) * hz4


def negativeUpperEntries {R : Type*} [Ring R] [DecidableEq R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun ij ↦ ij.1 < ij.2 ∧ A ij.1 ij.2 = -1)

theorem pfaffian_mod_four (m : ℕ) (A : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 4))
    (hA : ∀ i j, i < j → A i j = 1 ∨ A i j = -1) :
    pfaffian m A = (-1) ^ (negativeUpperEntries A).card := by
  classical
  generalize hn : (negativeUpperEntries A).card = n
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
    by_cases hzero : n = 0
    · rw [hzero, pow_zero]
      apply pfaffian_of_upper_one
      intro i j hij
      rcases hA i j hij with h | h
      · exact h
      · have hm : (i, j) ∈ negativeUpperEntries A := by simp [negativeUpperEntries, hij, h]
        exact False.elim (Finset.card_ne_zero_of_mem hm (hn.trans hzero))
    · obtain ⟨⟨a, b⟩, hab⟩ := Finset.card_pos.mp
        (show 0 < (negativeUpperEntries A).card by omega)
      have hs := (Finset.mem_filter.mp hab).2
      have hlt : a < b := hs.1
      have hneg : A a b = -1 := hs.2
      let B : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 4) :=
        fun i j ↦ A i j + if i = a ∧ j = b then 2 else 0
      have hB (i j) (hij : i < j) : B i j = 1 ∨ B i j = -1 := by
        by_cases h : i = a ∧ j = b
        · obtain ⟨rfl, rfl⟩ := h
          left
          change A i j + (if i = i ∧ j = j then 2 else 0) = 1
          rw [hneg]
          simp only [and_self, ite_true]
          decide
        · simpa [B, h] using hA i j hij
      have hred (T : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 4))
          (h : ∀ i j, i < j → T i j = 1 ∨ T i j = -1) :
          ∀ i j, i < j → reductionTwo (T i j) = 1 := by
        intro i j hij
        rcases h i j hij with he | he
        · rw [he, map_one]
        · rw [he]
          decide
      have hdiff := pfaffian_flip m A B (hred A hA) a b hlt (fun _ _ _ ↦ rfl)
      have hnegative : negativeUpperEntries B = (negativeUpperEntries A).erase (a, b) := by
        ext ij
        obtain ⟨i, j⟩ := ij
        by_cases h : i = a ∧ j = b
        · obtain ⟨rfl, rfl⟩ := h
          have hBab : B i j = 1 := by
            change A i j + (if i = i ∧ j = j then 2 else 0) = 1
            rw [hneg]
            simp only [and_self, ite_true]
            decide
          simp [negativeUpperEntries, hBab, show (1 : ZMod 4) ≠ -1 by decide]
        · have hne : (i, j) ≠ (a, b) := by simpa using h
          simp [negativeUpperEntries, B, h, hne]
      have hcard : (negativeUpperEntries B).card + 1 = n := by
        rw [hnegative, Finset.card_erase_add_one hab, hn]
      have hpf := ih (negativeUpperEntries B).card (by omega) B hB rfl
      have htwo := twice_odd_mod_four _ (pfaffian_reductionTwo m B (hred B hB))
      rw [← hcard, pow_succ, ← hpf]
      linear_combination -hdiff + htwo

theorem int_pfaffian_mod_four (m : ℕ) (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℤ)
    (hA : ∀ i j, i < j → A i j = 1 ∨ A i j = -1) :
    ((pfaffian m A : ℤ) : ZMod 4) = (-1) ^ (negativeUpperEntries A).card := by
  let f := Int.castRingHom (ZMod 4)
  change f (pfaffian m A) = _
  rw [pfaffian_map, pfaffian_mod_four]
  · congr 2
    ext ij
    obtain ⟨i, j⟩ := ij
    simp only [negativeUpperEntries, Finset.mem_filter, Finset.mem_univ, true_and,
      Matrix.map_apply]
    have hcast (h : i < j) :
        f (A i j) = -1 ↔ A i j = -1 := by
      rcases hA i j h with he | he
      · rw [he, map_one]
        decide
      · simp [he]
    constructor
    · intro h
      have hi := (Finset.mem_filter.mp h).2
      exact ⟨hi.1, (hcast hi.1).mp hi.2⟩
    · intro h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1, (hcast h.1).mpr h.2⟩
  · intro i j hij
    rcases hA i j hij with h | h <;> simp [h, f]

end ChenSun
```

## ChenSunPfaffianAntidiagonal.lean

```lean
import ChenSunPfaffian

open Matrix BigOperators

namespace ChenSun

def antidiagonal {R : Type*} [Zero R] (m : ℕ) (a : ℕ → R) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) R :=
  fun i j ↦ if (i : ℕ) + (j : ℕ) + 1 = 2 * m then a i else 0

/-- Only the reversal matching contributes. Its sign is positive in the first-row convention. -/
theorem pfaffian_antidiagonal {R : Type*} [CommRing R] (m : ℕ) (a : ℕ → R) :
    pfaffian m (antidiagonal m a) = ∏ i ∈ Finset.range m, a i := by
  classical
  induction m generalizing a with
  | zero => simp [pfaffian]
  | succ m ih =>
    rw [pfaffian, Finset.prod_range_succ']
    let l : Fin (2 * m + 1) := Fin.last (2 * m)
    let g (i : Fin (2 * m + 1)) : R :=
      (-1) ^ (i : ℕ) * antidiagonal (m + 1) a 0 i.succ *
        pfaffian m ((antidiagonal (m + 1) a).submatrix (skipPair m i) (skipPair m i))
    change (∑ i, g i) = _
    rw [Finset.sum_eq_single (f := g) l]
    · have hsign : (-1 : R) ^ (l : ℕ) = 1 := by
        change (-1 : R) ^ (2 * m) = 1
        rw [pow_mul, neg_one_sq, one_pow]
      have hentry : antidiagonal (R := R) (m + 1) a 0 l.succ = a 0 := by
        simp [antidiagonal, l]
        omega
      have hskip (j : Fin (2 * m)) : (skipPair m l j : ℕ) = (j : ℕ) + 1 := by
        unfold skipPair l
        rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_last j)]
        rfl
      have hsub : (antidiagonal (m + 1) a).submatrix (skipPair m l) (skipPair m l) =
          antidiagonal m (fun i ↦ a (i + 1)) := by
        ext i j
        change (if (skipPair m l i : ℕ) + (skipPair m l j : ℕ) + 1 = 2 * (m + 1)
          then a (skipPair m l i : ℕ) else 0) =
          (if (i : ℕ) + (j : ℕ) + 1 = 2 * m then a ((i : ℕ) + 1) else 0)
        simp only [hskip]
        split_ifs <;> first | rfl | omega
      unfold g
      rw [hsign, hentry, hsub, ih, one_mul, mul_comm]
    · intro i _ hi
      have h : (i : ℕ) + 1 + 1 ≠ 2 * (m + 1) := by
        intro hz
        apply hi
        apply Fin.ext
        change (i : ℕ) = 2 * m
        omega
      simp [g, antidiagonal, h]
    · simp

end ChenSun
```

## ChenSunOddPfaffian.lean

```lean
import ChenSunOddField
import ChenSunPfaffianModFour
import ChenSunPfaffianAntidiagonal

open Matrix BigOperators

namespace ChenSun

/-- The source's minor indexed by an explicitly even finite type. -/
def evenMinor (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    Matrix (Fin (2 * (half p / 2))) (Fin (2 * (half p / 2))) ℤ :=
  let e : Fin (2 * (half p / 2)) ≃ Fin (half p - 1) := finCongr (by unfold half; omega)
  (positiveMinor p).submatrix e e

theorem evenMinor_det (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    (evenMinor p hp).det = (positiveMinor p).det := by
  unfold evenMinor
  exact Matrix.det_submatrix_equiv_self _ _

theorem evenMinor_skew (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    (evenMinor p hp)ᵀ = -evenMinor p hp := by
  ext i j
  let e : Fin (2 * (half p / 2)) ≃ Fin (half p - 1) := finCongr (by unfold half; omega)
  exact congrFun (congrFun (positiveMatrix_skew p hp) (skipFirst (half p) (e i)))
    (skipFirst (half p) (e j))

theorem evenMinor_offdiag_sign (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3)
    {i j : Fin (2 * (half p / 2))} (h : i ≠ j) :
    evenMinor p hp i j = 1 ∨ evenMinor p hp i j = -1 := by
  unfold evenMinor
  exact positiveMinor_offdiag_sign p (Nat.odd_iff.mpr (by omega)) (Equiv.injective _ |>.ne h)

def sourcePfaffian (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) : ℤ :=
  pfaffian (half p / 2) (evenMinor p hp)

theorem sourcePfaffian_mod_four (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    (sourcePfaffian p hp : ZMod 4) = (-1) ^ (negativeUpperEntries (evenMinor p hp)).card :=
  int_pfaffian_mod_four _ _ (fun _ _ hij ↦ evenMinor_offdiag_sign p hp hij.ne)


theorem sourcePfaffian_character_four (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    ZMod.χ₄ (sourcePfaffian p hp : ZMod 4) =
      (-1) ^ (negativeUpperEntries (evenMinor p hp)).card := by
  rw [sourcePfaffian_mod_four, map_pow, show ZMod.χ₄ (-1 : ZMod 4) = -1 by decide]

end ChenSun
```

## ChenSunAudit.lean

```lean
import ChenSunEvenResult
import ChenSunOddPfaffian
import ChenSunSigned

namespace ChenSun

/-- The conjecture with the determinant-defined root certified by its source specification. -/
def ConjectureWithRoot : Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime, ∀ ho : Odd p,
    letI : Fact p.Prime := ⟨hp⟩
    IsCp p (cp p ho) ∧ jacobiSym (p : ℤ) (cp p ho) = 1

/-- The outstanding signed character assertion after the determinant and reciprocity reductions. -/
def OddSignedRoot : Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime, 3 < p → p % 4 = 3 →
    letI : Fact p.Prime := ⟨hp⟩
    ∃ f : ℤ, f ^ 2 = (positiveMinor p).det ∧ legendreSym p f = ZMod.χ₄ (f : ZMod 4)

theorem conjecture_iff_odd_signed_root : Conjecture ↔ OddSignedRoot := by
  constructor
  · intro H p hp _ h3
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨c, hc, _⟩ := cp_exists_three_mod_four p h3
    refine ⟨(c : ℤ), cp_square_eq_minor p c h3 hc, ?_⟩
    exact (signed_character_iff p c h3 hc.2.2.1 (c : ℤ) rfl).mp (H p hp c hc)
  · intro H p hp c hc
    let : Fact p.Prime := ⟨hp⟩
    rcases odd_mod_four p hc.1 with h1 | h3
    · exact chen_sun_one_mod_four p c h1 hc
    · by_cases h : p = 3
      · subst p
        have hc' : c = 1 := cp_unique 3 hc cp_three_spec
        rw [hc', jacobiSym.one_right]
      · have hgt : 3 < p := by omega
        obtain ⟨f, hf, hchar⟩ := H p hp hgt h3
        exact (odd_jacobi_iff_minor_root p c h3 hc f hf).mpr hchar

/-- The outstanding existence assertion for primes congruent to one modulo four. -/
def EvenRootExists : Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime, p % 4 = 1 →
    letI : Fact p.Prime := ⟨hp⟩
    ∃! c : ℕ, IsCp p c

theorem conjecture_with_root_iff : ConjectureWithRoot ↔ EvenRootExists ∧ OddSignedRoot := by
  constructor
  · intro H
    refine ⟨?_, conjecture_iff_odd_signed_root.mp ?_⟩
    · intro p hp h1
      let : Fact p.Prime := ⟨hp⟩
      have ho : Odd p := Nat.odd_iff.mpr (by omega)
      have hc := (H p hp ho).1
      exact ⟨cp p ho, hc, fun _ hd ↦ cp_unique p hd hc⟩
    · intro p hp c hc
      let : Fact p.Prime := ⟨hp⟩
      have h := (H p hp hc.1).2
      rwa [cp_eq_of_spec p c hc.1 hc] at h
  · rintro ⟨H1, H3⟩ p hp ho
    let : Fact p.Prime := ⟨hp⟩
    have hex : ∃! c : ℕ, IsCp p c := by
      rcases odd_mod_four p ho with h | h
      · exact H1 p hp h
      · exact cp_exists_three_mod_four p h
    obtain ⟨c, hc, _⟩ := hex
    have h := conjecture_iff_odd_signed_root.mpr H3 p hp c hc
    rw [cp_eq_of_spec p c ho hc]
    exact ⟨hc, h⟩

end ChenSun

#check ChenSun.entryMatrix
#check ChenSun.D
#check ChenSun.halfSum
#check ChenSun.IsCp
#check ChenSun.cp
#check ChenSun.Conjecture
#check ChenSun.ConjectureWithRoot
#check ChenSun.OddSignedRoot
#check ChenSun.EvenRootExists
#check ChenSun.cp_eq_of_spec
#check ChenSun.cp_unique
#check ChenSun.cp_three_spec
#check ChenSun.chen_sun_three
#check ChenSun.chen_sun_one_mod_four
#check ChenSun.positiveMatrix_row_sum
#check ChenSun.D_odd_minor
#check ChenSun.cp_exists_three_mod_four
#check ChenSun.cp_spec_three_mod_four
#check ChenSun.cp_square_eq_minor
#check ChenSun.odd_jacobi_iff_minor_root
#check ChenSun.odd_minor_mod_factorization
#check ChenSun.pfaffian_map
#check ChenSun.pfaffian_odd_of_upper_signs
#check ChenSun.sourcePfaffian_mod_four
#check ChenSun.sourcePfaffian_character_four
#check ChenSun.pfaffian_antidiagonal
#check ChenSun.conjecture_iff_odd_signed_root
#check ChenSun.conjecture_with_root_iff

#print axioms ChenSun.entryMatrix
#print axioms ChenSun.D
#print axioms ChenSun.halfSum
#print axioms ChenSun.IsCp
#print axioms ChenSun.cp
#print axioms ChenSun.Conjecture
#print axioms ChenSun.ConjectureWithRoot
#print axioms ChenSun.OddSignedRoot
#print axioms ChenSun.EvenRootExists
#print axioms ChenSun.cp_eq_of_spec
#print axioms ChenSun.cp_unique
#print axioms ChenSun.cp_three_spec
#print axioms ChenSun.chen_sun_three
#print axioms ChenSun.chen_sun_one_mod_four
#print axioms ChenSun.positiveMatrix_row_sum
#print axioms ChenSun.D_odd_minor
#print axioms ChenSun.cp_exists_three_mod_four
#print axioms ChenSun.cp_spec_three_mod_four
#print axioms ChenSun.cp_square_eq_minor
#print axioms ChenSun.odd_jacobi_iff_minor_root
#print axioms ChenSun.odd_minor_mod_factorization
#print axioms ChenSun.pfaffian_map
#print axioms ChenSun.pfaffian_odd_of_upper_signs
#print axioms ChenSun.sourcePfaffian_mod_four
#print axioms ChenSun.sourcePfaffian_character_four
#print axioms ChenSun.pfaffian_antidiagonal
#print axioms ChenSun.conjecture_iff_odd_signed_root
#print axioms ChenSun.conjecture_with_root_iff
```

## ChenSunEvenBlock.lean

```lean
import ChenSunOddExistence

open Matrix BigOperators

namespace ChenSun

section Block

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two parity rows and their action on a bordered rank-one perturbation. -/
theorem even_block_coefficient
    (A S : Matrix (ι ⊕ Fin 2) (ι ⊕ Fin 2) ℤ)
    (L : Matrix (Fin 2) (ι ⊕ Fin 2) ℤ) (u : ι ⊕ Fin 2 → ℤ)
    (m : ℤ)
    (hs : (S.submatrix Sum.inl Sum.inl).det = 1)
    (hc : A * S = S * A) (hL : L * S = 0)
    (hu : (fun i ↦ ∑ k, u k * S k i) = 0)
    (hLr : L.submatrix id Sum.inr = 1)
    (hLu : ∀ i, ∑ k, L i k * u k = ![m, -m] i)
    (hL1 : ∀ i, ∑ k, L i k = m)
    (hur : u ∘ Sum.inr = ![1, -1])
    (hS1 : ∀ j, ∑ k, S k j = 0) :
    let N := (A * S).submatrix Sum.inl Sum.inl
    N.det ∣ A.det ∧
      ∀ w : ℤ,
        (fromBlocks (A + w • vecMulVec u u) (of fun _ (_ : Fin 1) ↦ 1)
          (of fun _ _ ↦ 1) (0 : Matrix (Fin 1) (Fin 1) ℤ)).det -
        (fromBlocks A (of fun _ (_ : Fin 1) ↦ 1)
          (of fun _ _ ↦ 1) (0 : Matrix (Fin 1) (Fin 1) ℤ)).det =
          -w * (2 * m) ^ 2 * N.det := by
  let N := (A * S).submatrix Sum.inl Sum.inl
  let C := fromBlocks (S.submatrix Sum.inl Sum.inl) 0
    (S.submatrix Sum.inr Sum.inl) (1 : Matrix (Fin 2) (Fin 2) ℤ)
  let R := fromBlocks (1 : Matrix ι ι ℤ) 0 (L.submatrix id Sum.inl)
    (1 : Matrix (Fin 2) (Fin 2) ℤ)
  let P (w : ℤ) := A + w • vecMulVec u u
  let K (w : ℤ) := (L * P w).submatrix id Sum.inr
  have hdC : C.det = 1 := by simp [C, hs]
  have hdR : R.det = 1 := by simp [R]
  have hR (j k) : R (Sum.inr j) k = L j k := by
    cases k with
    | inl k => rfl
    | inr k => exact (congrFun (congrFun hLr j) k).symm
  have hC (k j) : C k (Sum.inr j) = if k = Sum.inr j then 1 else 0 := by
    cases k <;> simp [C, Matrix.one_apply]
  have hPS (w : ℤ) : P w * S = A * S := by
    ext i j
    simp only [P, add_mul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_apply,
      vecMulVec_apply, mul_assoc, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, congrFun hu j]
    simp
  have hblock (w : ℤ) :
      R * P w * C = fromBlocks N ((P w).submatrix Sum.inl Sum.inr) 0 (K w) := by
    ext i j
    cases i with
    | inl i =>
      have hh (k) : (R * P w) (Sum.inl i) k = P w (Sum.inl i) k := by
        simp [mul_apply, Fintype.sum_sum_type, R, Matrix.one_apply]
      cases j with
      | inl j =>
        change (R * P w * C) (Sum.inl i) (Sum.inl j) = (A * S) (Sum.inl i) (Sum.inl j)
        calc
          _ = (P w * S) (Sum.inl i) (Sum.inl j) := by
            simp only [Matrix.mul_apply (M := (R * P w)), Matrix.mul_apply (M := (P w)), hh]
            congr 1
            funext k
            cases k <;> rfl
          _ = _ := by rw [hPS]
      | inr j => simp only [Matrix.mul_apply (M := (R * P w)), hh, hC]; simp
    | inr i =>
      have hh (k) : (R * P w) (Sum.inr i) k = (L * P w) i k := by simp [mul_apply, hR]
      cases j with
      | inl j =>
        have hz : L * P w * S = 0 := by
          rw [Matrix.mul_assoc, hPS, hc, ← Matrix.mul_assoc, hL, Matrix.zero_mul]
        rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
        calc
          _ = (L * P w * S) i (Sum.inl j) := by
            simp only [Matrix.mul_apply (M := (R * P w)), Matrix.mul_apply (M := (L * P w)), hh]
            congr 1
            funext k
            cases k <;> rfl
          _ = _ := by rw [hz]; rfl
      | inr j => simp only [Matrix.mul_apply (M := (R * P w)), hh, hC]; simp [K]
  have dK : A.det = N.det * (K 0).det := by
    have he := congrArg Matrix.det (hblock 0)
    simpa [P, hdC, hdR, det_fromBlocks_zero₂₁] using he
  refine ⟨⟨(K 0).det, dK⟩, ?_⟩
  let col : Matrix (ι ⊕ Fin 2) (Fin 1) ℤ := of fun _ _ ↦ 1
  let row : Matrix (Fin 1) (ι ⊕ Fin 2) ℤ := of fun _ _ ↦ 1
  let B (w : ℤ) := fromBlocks (P w) col row (0 : Matrix (Fin 1) (Fin 1) ℤ)
  let K' (w : ℤ) := fromBlocks (K w)
    (of fun _ (_ : Fin 1) ↦ m) (of fun _ _ ↦ 1) (0 : Matrix (Fin 1) (Fin 1) ℤ)
  have hcol (i : Fin 2) (j : Fin 1) : (R * col) (Sum.inr i) j = m := by
    simp [mul_apply, col, hR, hL1]
  have hrow₁ (i : Fin 1) (j : ι) : (row * C) i (Sum.inl j) = 0 := by
    simpa [mul_apply, row, C] using hS1 (Sum.inl j)
  have hrow₂ (i : Fin 1) (j : Fin 2) : (row * C) i (Sum.inr j) = 1 := by
    simp [mul_apply, row, hC]
  let e : ((ι ⊕ Fin 2) ⊕ Fin 1) ≃ ι ⊕ (Fin 2 ⊕ Fin 1) := Equiv.sumAssoc _ _ _
  have hB (w : ℤ) : (B w).det = N.det * (K' w).det := by
    let R' := fromBlocks R 0 0 (1 : Matrix (Fin 1) (Fin 1) ℤ)
    let C' := fromBlocks C 0 0 (1 : Matrix (Fin 1) (Fin 1) ℤ)
    have he (i j) : ((R' * B w * C').submatrix e.symm e.symm) i j =
        (fromBlocks N (fun i j ↦ (R' * B w * C') (Sum.inl (Sum.inl i)) (e.symm (Sum.inr j)))
          0 (K' w)) i j := by
      have hm : R' * B w * C' = fromBlocks (R * P w * C) (R * col) (row * C) 0 := by
        simp [R', B, C', fromBlocks_multiply]
      have hp (a b) : (R * P w * C) a b =
          (fromBlocks N ((P w).submatrix Sum.inl Sum.inr) 0 (K w)) a b := by
        rw [hblock]
      rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
        simp [e, hm, hp, hcol, hrow₁, hrow₂, K', Matrix.fromBlocks_apply₁₁,
          Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] <;> first | rfl | exact (congrFun (congrFun (hblock w) (Sum.inl i)) (Sum.inr j)).symm
    have h := congrArg Matrix.det (Matrix.ext he)
    rw [det_submatrix_equiv_self, det_mul, det_mul] at h
    change (B w).det = _
    have hdR' : R'.det = 1 := by simp [R', hdR]
    have hdC' : C'.det = 1 := by simp [C', hdC]
    rw [hdR', hdC', one_mul, mul_one] at h
    exact h.trans (det_fromBlocks_zero₂₁ N _ (K' w))
  have hK (w : ℤ) (i j : Fin 2) : K w i j =
      K 0 i j + w * ![m, -m] i * ![1, -1] j := by
    have huv : u (Sum.inr j) = ![1, -1] j := congrFun hur j
    simp only [K, submatrix_apply, id_eq, P, Matrix.mul_add, zero_smul, Matrix.mul_zero, Matrix.add_apply]
    simp only [mul_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, huv]
    simp_rw [show ∀ a b c d : ℤ, a * (b * (c * d)) = b * ((a * c) * d) by
      intros; ring]
    rw [← Finset.mul_sum, ← Finset.sum_mul, hLu]
    simp only [Matrix.zero_apply, add_zero]
    ring
  have hsmall (w : ℤ) : (K' w).det - (K' 0).det = -w * (2 * m) ^ 2 := by
    let t : Fin 2 ⊕ Fin 1 ≃ Fin 3 := finSumFinEquiv
    have he (v : ℤ) : (K' v).submatrix t.symm t.symm =
        !![K v 0 0, K v 0 1, m; K v 1 0, K v 1 1, m; 1, 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [← det_submatrix_equiv_self t.symm (K' w), ← det_submatrix_equiv_self t.symm (K' 0),
      he w, he 0, det_fin_three, det_fin_three]
    simp [hK w]
    ring
  intro w
  have h0 : B 0 = fromBlocks A col row (0 : Matrix (Fin 1) (Fin 1) ℤ) := by
    simp [B, P]
  change (B w).det - (fromBlocks A col row (0 : Matrix (Fin 1) (Fin 1) ℤ)).det = _
  rw [← h0, hB, hB, ← mul_sub, hsmall]
  ring

end Block
end ChenSun
```

## ChenSunCyclicDifference.lean

```lean
import ChenSunSource
import Mathlib.LinearAlgebra.Matrix.Circulant

open Matrix BigOperators

namespace ChenSun

/-- The alternating signs of the cyclic order and its two parity rows. -/
def cyclicSign {n : ℕ} (i : Fin n) : ℤ :=
  if (i : ℕ) % 2 = 0 then 1 else -1

def parityRows (n : ℕ) : Matrix (Fin 2) (Fin n) ℤ :=
  fun a i ↦ if (i : ℕ) % 2 = a then 1 else 0

def cyclicDifference (n : ℕ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ :=
  circulant (fun t ↦ (if t = -1 then 1 else 0) - (if t = 1 then 1 else 0))

theorem cyclicDifference_apply {n : ℕ} (i j : Fin (n + 2)) :
    cyclicDifference n i j = (if i = j - 1 then 1 else 0) - (if i = j + 1 then 1 else 0) := by
  have h₁ : i - j = -1 ↔ i = j - 1 := by
    rw [sub_eq_iff_eq_add, sub_eq_add_neg, add_comm j]
  have h₂ : i - j = 1 ↔ i = j + 1 := by rw [sub_eq_iff_eq_add, add_comm j]
  simp [cyclicDifference, h₁, h₂]

theorem cyclicDifference_skew (n : ℕ) : (cyclicDifference n)ᵀ = -cyclicDifference n := by
  ext i j
  have h₁ : j - i = -1 ↔ i - j = 1 := by rw [← neg_sub, neg_eq_iff_eq_neg, neg_neg]
  have h₂ : j - i = 1 ↔ i - j = -1 := by rw [← neg_sub, neg_eq_iff_eq_neg]
  simp [cyclicDifference, h₁, h₂, neg_sub]

theorem sum_cyclicDifference {n : ℕ} (f : Fin (n + 2) → ℤ) (j : Fin (n + 2)) :
    (∑ i, f i * cyclicDifference n i j) = f (j - 1) - f (j + 1) := by
  simp only [cyclicDifference_apply, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem cyclicDifference_parity {n : ℕ} (hn : Even n) (j : Fin (n + 2)) :
    ((j - 1 : Fin (n + 2)) : ℕ) % 2 = ((j + 1 : Fin (n + 2)) : ℕ) % 2 := by
  have hn' := Nat.even_iff.mp hn
  have hd : 2 ∣ n + 2 := by omega
  simp only [Fin.val_sub, Fin.val_one, Fin.val_add, Nat.mod_mod_of_dvd _ hd]
  omega

theorem sum_parityRows (m : ℕ) (a : Fin 2) :
    (∑ i : Fin (2 * m), parityRows (2 * m) a i) = (m : ℤ) := by
  have h (k : ℕ) : (∑ i ∈ Finset.range (2 * k),
      (if i % 2 = (a : ℕ) then 1 else 0 : ℤ)) = (k : ℤ) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, Finset.sum_range_succ,
        Finset.sum_range_succ, ih]
      have h₀ : (2 * k) % 2 = 0 := by omega
      have h₁ : (2 * k + 1) % 2 = 1 := by omega
      fin_cases a <;> simp [h₀, h₁]
  exact (Fin.sum_univ_eq_sum_range _ _).trans (h m)

private def pathDifference (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j ↦ (if (i : ℕ) + 1 = (j : ℕ) then 1 else 0) -
    (if (j : ℕ) + 1 = (i : ℕ) then 1 else 0)

private theorem det_pathDifference (m : ℕ) : (pathDifference (2 * m)).det = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    change (pathDifference (2 * m + 2)).det = _
    let A := pathDifference (2 * m + 2)
    have hA₀ (j : Fin (2 * m + 2)) : A 0 j = if j = 1 then 1 else 0 := by
      have h : 1 = (j : ℕ) ↔ j = 1 := by rw [Fin.ext_iff, eq_comm]; rfl
      simp [A, pathDifference, h]
    have hB₀ (i : Fin (2 * m + 1)) : (A.submatrix Fin.succ (Fin.succAbove 1)) i 0 =
        if i = 0 then -1 else 0 := by
      have h : (i : ℕ) = 0 ↔ i = 0 := by rw [Fin.ext_iff]; rfl
      simp [A, pathDifference, show (1 : Fin (2 * m + 2)).succAbove 0 = 0 by
        apply Fin.ext; rfl, h, apply_ite Neg.neg]
    have hB (i j : Fin (2 * m)) :
        (A.submatrix Fin.succ (Fin.succAbove 1)).submatrix (Fin.succAbove 0) Fin.succ i j =
          pathDifference (2 * m) i j := by
      have h : (1 : Fin (2 * m + 2)).succAbove j.succ = j.succ.succ := by
        exact Fin.succAbove_of_le_castSucc _ _ (by change 1 ≤ (j : ℕ) + 1; omega)
      simp [A, pathDifference, h, Fin.succAbove_zero]
    change A.det = _
    rw [Matrix.det_succ_row_zero]
    simp only [hA₀]
    rw [Finset.sum_eq_single 1]
    · simp
      rw [Matrix.det_succ_column_zero]
      simp only [hB₀]
      rw [Finset.sum_eq_single 0]
      · simp only [ite_true, Fin.val_zero, pow_zero, one_mul]
        rw [Matrix.ext hB, ih]
        norm_num
      · intro i _ hi
        simp [hi]
      · simp
    · intro j _ hj
      simp [hj]
    · simp

theorem det_cyclicDifference_castAdd {n : ℕ} (hn : Even n) :
    ((cyclicDifference n).submatrix (Fin.castAdd 2) (Fin.castAdd 2)).det = 1 := by
  have hA : (cyclicDifference n).submatrix (Fin.castAdd 2) (Fin.castAdd 2) =
      pathDifference n := by
    ext i j
    have hi := i.isLt
    have hj := j.isLt
    have h (a b : Fin n) :
        Fin.castAdd 2 a = Fin.castAdd 2 b + 1 ↔ (a : ℕ) = (b : ℕ) + 1 := by
      have hb := b.isLt
      rw [Fin.ext_iff, Fin.val_add, Fin.val_castAdd, Fin.val_castAdd,
        show ((1 : Fin (n + 2)) : ℕ) = 1 by rfl, Nat.mod_eq_of_lt (by omega)]
    have h' : Fin.castAdd 2 i = Fin.castAdd 2 j - 1 ↔ (j : ℕ) = (i : ℕ) + 1 := by
      rw [eq_sub_iff_add_eq, eq_comm, h j i]
    simp only [submatrix_apply, cyclicDifference_apply, h', h i j]
    simp [pathDifference, eq_comm]
  obtain ⟨m, hm⟩ := hn
  rw [hA, show n = 2 * m by omega, det_pathDifference]

end ChenSun
```

## ChenSunSquareOrder.lean

```lean
import ChenSunSkew
import ChenSunCyclicDifference

open Matrix

namespace ChenSun

theorem positive_rep (p : ℕ) [Fact p.Prime] (ho : Odd p)
    (x : ZMod p) (hx : x ≠ 0) :
    ∃ i : Fin (half p), (((i : ℕ) + 1 : ℕ) : ZMod p) = x ∨
      (((i : ℕ) + 1 : ℕ) : ZMod p) = -x := by
  have hv : 0 < x.val := by
    by_contra! h
    apply hx
    simpa [Nat.eq_zero_of_le_zero h] using (ZMod.natCast_zmod_val x).symm
  have hlt := ZMod.val_lt x
  have hh := twice_half p ho
  by_cases h : x.val ≤ half p
  · refine ⟨⟨x.val - 1, by omega⟩, Or.inl ?_⟩
    change ((x.val - 1 + 1 : ℕ) : ZMod p) = x
    rw [show x.val - 1 + 1 = x.val by omega, ZMod.natCast_zmod_val]
  · refine ⟨⟨p - x.val - 1, by omega⟩, Or.inr ?_⟩
    change ((p - x.val - 1 + 1 : ℕ) : ZMod p) = -x
    rw [show p - x.val - 1 + 1 = p - x.val by omega, Nat.cast_sub (by omega),
      ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]

private theorem cyclic_pow_mul {G : Type*} [Group G] {n : ℕ} (q : G)
    (hq : orderOf q = n + 2) (i j : Fin (n + 2)) :
    q ^ ((i + j : Fin (n + 2)) : ℕ) = q ^ (i : ℕ) * q ^ (j : ℕ) := by
  have h := pow_mod_orderOf q ((i : ℕ) + (j : ℕ))
  rw [hq, pow_add] at h
  exact h

/-- The order induced by a generator of the squares makes the positive matrix circulant. -/
theorem square_circulant_order (p n : ℕ) [Fact p.Prime] (hp : p % 4 = 1)
    (hn : half p = n + 2) :
    ∃ (e : Fin (n + 2) ≃ Fin (half p)) (v : Fin (n + 2) → ℤ),
      (positiveMatrix p).submatrix e e = circulant v ∧
      positiveVector p ∘ e = cyclicSign := by
  classical
  have ho : Odd p := Nat.odd_iff.mpr (by omega)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ZMod.card, ← twice_half p ho, hn] at hg
  let q := g ^ 2
  have hq : orderOf q = n + 2 := by
    dsimp only [q]
    rw [orderOf_pow, hg, Nat.gcd_eq_right (dvd_mul_right 2 (n + 2))]
    omega
  let χ := quadraticChar (ZMod p)
  have hχneg : χ (-1) = 1 := by
    have h := legendreSym.at_neg_one (p := p) (by omega)
    rw [ZMod.χ₄_nat_eq_if_mod_four] at h
    have h' : legendreSym p (-1) = 1 := by
      simpa [hp, show p % 2 ≠ 0 by omega] using h
    simpa [χ, legendreSym] using h'
  have hχg : χ (g : ZMod p) = -1 := by
    apply quadraticChar_neg_one_iff_not_isSquare.mpr
    rintro ⟨a, ha⟩
    have ha₀ : a ≠ 0 := by rintro rfl; simp at ha
    have hh : g ^ (n + 2) = 1 := by
      apply Units.ext
      change (g : ZMod p) ^ (n + 2) = 1
      rw [ha, ← sq, ← pow_mul, ← hn, twice_half p ho]
      exact ZMod.pow_card_sub_one_eq_one ha₀
    have := orderOf_le_of_pow_eq_one (by omega : 0 < n + 2) hh
    omega
  have hrep (i : Fin (n + 2)) := positive_rep p ho ((g ^ (i : ℕ) : (ZMod p)ˣ) : ZMod p)
    (Units.ne_zero _)
  choose e he using hrep
  have heχ (i : Fin (n + 2)) :
      positiveVector p (e i) = (-1 : ℤ) ^ (i : ℕ) := by
    have hcast : ((((e i : Fin _) : ℕ) + 1 : ℤ) : ZMod p) =
        ((((e i : Fin _) : ℕ) + 1 : ℕ) : ZMod p) := by push_cast; rfl
    change χ ((((e i : Fin _) : ℕ) + 1 : ℤ) : ZMod p) = _
    rw [hcast]
    rcases he i with h | h
    · rw [h, Units.val_pow_eq_pow_val, map_pow, hχg]
    · rw [h, neg_eq_neg_one_mul, map_mul, hχneg, one_mul, Units.val_pow_eq_pow_val,
        map_pow, hχg]
  have hesq (i : Fin (n + 2)) :
      ((((e i : Fin _) : ℕ) + 1 : ℕ) : ZMod p) ^ 2 = (q ^ (i : ℕ) : (ZMod p)ˣ) := by
    rcases he i with h | h <;> rw [h] <;>
      simp [q, mul_comm (2 : ℕ), ← pow_mul]
  have hei : Function.Injective e := by
    intro i j h
    have hpow : q ^ (i : ℕ) = q ^ (j : ℕ) := by
      apply Units.ext
      rw [← hesq i, ← hesq j, h]
    have hmod := pow_inj_mod.mp hpow
    rw [hq, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hmod
    exact Fin.ext hmod
  let E := Equiv.ofBijective e ((Fintype.bijective_iff_injective_and_card e).mpr
    ⟨hei, by simp [hn]⟩)
  refine ⟨E, (fun i ↦ χ (((q ^ (i : ℕ) : (ZMod p)ˣ) : ZMod p) - 1)), ?_, ?_⟩
  · apply Matrix.ext
    intro i j
    have hx : q ^ (i : ℕ) = q ^ ((i - j : Fin (n + 2)) : ℕ) * q ^ (j : ℕ) := by
      rw [← cyclic_pow_mul q hq, sub_add_cancel]
    have hj : χ ((q ^ (j : ℕ) : (ZMod p)ˣ) : ZMod p) = 1 := by
      change χ (((g ^ 2) ^ (j : ℕ) : (ZMod p)ˣ) : ZMod p) = 1
      rw [pow_right_comm g 2, Units.val_pow_eq_pow_val, quadraticChar_sq_one' (Units.ne_zero _)]
    have hcast (k : Fin (n + 2)) : ((((e k : Fin _) : ℕ) + 1 : ℤ) : ZMod p) =
        ((((e k : Fin _) : ℕ) + 1 : ℕ) : ZMod p) := by push_cast; rfl
    change χ ((((((e i : Fin _) : ℕ) + 1 : ℤ) ^ 2 -
      (((e j : Fin _) : ℕ) + 1 : ℤ) ^ 2 : ℤ) : ZMod p)) =
      χ (((q ^ ((i - j : Fin (n + 2)) : ℕ) : (ZMod p)ˣ) : ZMod p) - 1)
    simp only [Int.cast_sub, Int.cast_pow, hcast]
    rw [hesq i, hesq j, hx, Units.val_mul, ← sub_one_mul, map_mul, hj, mul_one]
  · funext i
    change positiveVector p (e i) = cyclicSign i
    rw [heχ, cyclicSign]
    split
    · exact (Nat.even_iff.mpr (by assumption) : Even (i : ℕ)).neg_one_pow
    · exact (Nat.odd_iff.mpr (by omega) : Odd (i : ℕ)).neg_one_pow

end ChenSun
```

## ChenSunEvenCyclic.lean

```lean
import ChenSunEvenBlock
import ChenSunCyclicDifference

open Matrix BigOperators

namespace ChenSun

/-- Passage from a symmetric circulant to the skew determinant giving its
bordered perturbation coefficient. -/
theorem even_circulant_coefficient (n m : ℕ) (hm : n + 2 = 2 * m)
    (v : Fin (n + 2) → ℤ) (ha : (circulant v)ᵀ = circulant v) :
    ∃ N : Matrix (Fin n) (Fin n) ℤ,
      Nᵀ = -N ∧ N.det ∣ (circulant v).det ∧ ∀ w : ℤ,
      (fromBlocks (circulant v + w • vecMulVec cyclicSign cyclicSign)
        (of fun _ (_ : Fin 1) ↦ 1) (of fun _ _ ↦ 1) (0 : Matrix (Fin 1) (Fin 1) ℤ)).det -
      (fromBlocks (circulant v)
        (of fun _ (_ : Fin 1) ↦ 1) (of fun _ _ ↦ 1) (0 : Matrix (Fin 1) (Fin 1) ℤ)).det =
        -w * ((n + 2 : ℕ) : ℤ) ^ 2 * N.det := by
  let e : Fin n ⊕ Fin 2 ≃ Fin (n + 2) := finSumFinEquiv
  let C := circulant v
  let T := cyclicDifference n
  let Y := parityRows (n + 2)
  let A := C.submatrix e e
  let S := T.submatrix e e
  let L := Y.submatrix id e
  let u := cyclicSign ∘ e
  have he : Even n := Nat.even_iff.mpr (by omega)
  have hT : C * T = T * C := Fin.circulant_mul_comm _ _
  have ha' : Aᵀ = A := by
    apply Matrix.ext
    intro i j
    exact congrFun (congrFun ha (e i)) (e j)
  have hs' : Sᵀ = -S := by
    apply Matrix.ext
    intro i j
    exact congrFun (congrFun (cyclicDifference_skew n) (e i)) (e j)
  have hs : (S.submatrix Sum.inl Sum.inl).det = 1 :=
    det_cyclicDifference_castAdd he
  have hc : A * S = S * A := by
    change C.submatrix e e * T.submatrix e e = T.submatrix e e * C.submatrix e e
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hT]
  have hL : L * S = 0 := by
    change Y.submatrix id e * T.submatrix e e = 0
    rw [Matrix.submatrix_mul_equiv]
    apply Matrix.ext
    intro i j
    change (∑ k, Y i k * T k (e j)) = 0
    rw [sum_cyclicDifference]
    simp [Y, parityRows, cyclicDifference_parity he (e j)]
  have hu : (fun i ↦ ∑ k, u k * S k i) = 0 := by
    funext i
    change (∑ k, cyclicSign (e k) * T (e k) (e i)) = 0
    rw [Fintype.sum_equiv e (fun k ↦ cyclicSign (e k) * T (e k) (e i))
      (fun k ↦ cyclicSign k * T k (e i)) (fun _ ↦ rfl)]
    rw [sum_cyclicDifference]
    simp [cyclicSign, cyclicDifference_parity he (e i)]
  have heR (j : Fin 2) : (e (Sum.inr j) : ℕ) % 2 = (j : ℕ) := by
    change (n + (j : ℕ)) % 2 = (j : ℕ)
    have := j.isLt
    omega
  have hLr : L.submatrix id Sum.inr = 1 := by
    apply Matrix.ext
    intro i j
    change (if (e (Sum.inr j) : ℕ) % 2 = (i : ℕ) then 1 else 0) = _
    simp [heR, Matrix.one_apply, Fin.ext_iff, eq_comm]
  have hL1 (i : Fin 2) : (∑ k, L i k) = (m : ℤ) := by
    change (∑ k, Y i (e k)) = _
    rw [Fintype.sum_equiv e _ _ (fun _ ↦ rfl)]
    have hh (q : ℕ) (hq : q = 2 * m) :
        (∑ k, parityRows q i k) = (m : ℤ) := by
      subst q
      exact sum_parityRows m i
    exact hh (n + 2) hm
  have hur : u ∘ Sum.inr = ![1, -1] := by
    funext j
    change (if (e (Sum.inr j) : ℕ) % 2 = 0 then 1 else -1) = _
    rw [heR]
    fin_cases j <;> rfl
  have hLu (i : Fin 2) : (∑ k, L i k * u k) = ![(m : ℤ), -m] i := by
    have hx (j) : L i j * u j = L i j * (if (i : ℕ) = 0 then 1 else -1) := by
      change (if (e j : ℕ) % 2 = (i : ℕ) then 1 else 0) * cyclicSign (e j) = _
      by_cases h : (e j : ℕ) % 2 = (i : ℕ) <;> simp [L, Y, parityRows, cyclicSign, h]
    simp_rw [hx, ← Finset.sum_mul, hL1]
    fin_cases i <;> simp
  have hS1 (j : Fin n ⊕ Fin 2) : ∑ k, S k j = 0 := by
    change (∑ k, T (e k) (e j)) = 0
    rw [Fintype.sum_equiv e (fun k ↦ T (e k) (e j)) (fun k ↦ T k (e j)) (fun _ ↦ rfl)]
    simpa using sum_cyclicDifference (fun _ : Fin (n + 2) ↦ 1) (e j)
  obtain ⟨hd, hcoef⟩ := even_block_coefficient A S L u (m : ℤ) hs hc hL hu hLr hLu hL1 hur hS1
  let N := (A * S).submatrix Sum.inl Sum.inl
  have hAS : (A * S)ᵀ = -(A * S) := by
    rw [transpose_mul, hs', ha', neg_mul, hc]
  refine ⟨N, ?_, ?_, ?_⟩
  · apply Matrix.ext
    intro i j
    exact congrFun (congrFun hAS (Sum.inl i)) (Sum.inl j)
  · rwa [show A.det = C.det from det_submatrix_equiv_self e C] at hd
  · intro w
    let E := Equiv.sumCongr e (Equiv.refl (Fin 1))
    let B (z : ℤ) := fromBlocks (circulant v + z • vecMulVec cyclicSign cyclicSign)
      (of fun _ (_ : Fin 1) ↦ 1) (of fun _ _ ↦ 1) (0 : Matrix (Fin 1) (Fin 1) ℤ)
    have hB (z : ℤ) : (B z).submatrix E E =
        fromBlocks (A + z • vecMulVec u u) (of fun _ (_ : Fin 1) ↦ 1)
          (of fun _ _ ↦ 1) (0 : Matrix (Fin 1) (Fin 1) ℤ) := by
      apply Matrix.ext
      intro i j
      cases i <;> cases j <;> rfl
    have hB0 : B 0 = fromBlocks (circulant v) (of fun _ (_ : Fin 1) ↦ 1)
        (of fun _ _ ↦ 1) (0 : Matrix (Fin 1) (Fin 1) ℤ) := by simp [B]
    have h (z) : (B z).det = ((B z).submatrix E E).det :=
      (det_submatrix_equiv_self E (B z)).symm
    have hc' := hcoef w
    rw [← hB w, det_submatrix_equiv_self] at hc'
    have hz := h 0
    rw [hB 0, zero_smul, add_zero] at hz
    rw [← hz, hB0] at hc'
    simpa only [hm, Nat.cast_mul, Nat.cast_ofNat] using hc'

end ChenSun
```

## ChenSunEvenExistence.lean

```lean
import ChenSunAudit
import ChenSunEvenCyclic
import ChenSunSquareOrder

open Matrix BigOperators

namespace ChenSun

private theorem positiveMatrix_symm (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) :
    (positiveMatrix p)ᵀ = positiveMatrix p := by
  have hneg (a : ℤ) : legendreSym p (-a) = legendreSym p a := by
    rw [legendreSym.at_neg (by omega), ZMod.χ₄_nat_eq_if_mod_four]
    simp [hp, show p % 2 ≠ 0 by omega]
  apply Matrix.ext
  intro i j
  change legendreSym p (((j : ℕ) + 1 : ℤ) ^ 2 - ((i : ℕ) + 1 : ℤ) ^ 2) = _
  rw [show ((j : ℕ) + 1 : ℤ) ^ 2 - ((i : ℕ) + 1 : ℤ) ^ 2 =
      -(((i : ℕ) + 1 : ℤ) ^ 2 - ((j : ℕ) + 1 : ℤ) ^ 2) by ring, hneg]
  rfl

private theorem positiveMatrix_det_odd_even_class (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) :
    Odd (positiveMatrix p).det := by
  classical
  have ho : Odd p := Nat.odd_iff.mpr (by omega)
  let J : Matrix (Fin (half p)) (Fin (half p)) (ZMod 2) := of (fun _ _ ↦ 1)
  let M : Matrix (Fin (half p)) (Fin (half p)) (ZMod 2) := 1 + J
  have he : Even (half p) := Nat.even_iff.mpr (by unfold half; omega)
  have hmap : (positiveMatrix p).map (Int.castRingHom (ZMod 2)) = M := by
    apply Matrix.ext
    intro i j
    change (positiveMatrix p i j : ZMod 2) = M i j
    by_cases h : i = j
    · subst j
      simpa [positiveMatrix, M, J] using (show (0 : ZMod 2) = 1 + 1 by decide)
    · have hz : point p i.succ - point p j.succ ≠ 0 :=
        sub_ne_zero.mpr ((point_injective p ho).ne (Fin.succ_injective _ |>.ne h))
      have hz' : (((((i : ℕ) + 1 : ℤ) ^ 2 - ((j : ℕ) + 1 : ℤ) ^ 2 : ℤ) : ZMod p)) ≠ 0 := by
        simpa [point] using hz
      rcases legendreSym.eq_one_or_neg_one p hz' with e | e
      · simp [M, J, h, positiveMatrix, e]
      · simp [M, J, h, positiveMatrix, e]
  have hJ : J * J = 0 := by
    apply Matrix.ext
    intro i j
    simp [Matrix.mul_apply, J, he.natCast_zmod_two]
  have h2J : J + J = 0 := by
    apply Matrix.ext
    intro i j
    exact (show (1 : ZMod 2) + 1 = 0 by decide)
  have hM : M * M = 1 := by
    unfold M
    rw [Matrix.add_mul, Matrix.mul_add J, Matrix.one_mul, Matrix.mul_one, hJ, add_zero,
      add_assoc, h2J, add_zero]
  have hd := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_one] at hd
  have hd' := (show ∀ z : ZMod 2, z * z = 1 → z = 1 by decide) _ hd
  apply ZMod.intCast_eq_one_iff_odd.mp
  change (Int.castRingHom (ZMod 2)) (positiveMatrix p).det = 1
  rw [RingHom.map_det]
  change ((positiveMatrix p).map (Int.castRingHom (ZMod 2))).det = 1
  rw [hmap, hd']

private theorem det_entry_zero_border (p n : ℕ) [Fact p.Prime] (hp : p % 4 = 1)
    (e : Fin (n + 2) ≃ Fin (half p)) (v : Fin (n + 2) → ℤ)
    (he : (positiveMatrix p).submatrix e e = circulant v)
    (hu : positiveVector p ∘ e = cyclicSign) (w : ℤ) :
    (entryMatrix p 0 w).det =
      (fromBlocks (circulant v + w • vecMulVec cyclicSign cyclicSign)
        (of fun _ (_ : Fin 1) ↦ 1) (of fun _ _ ↦ 1) (0 : Matrix (Fin 1) (Fin 1) ℤ)).det := by
  let E : Fin (n + 2) ⊕ Fin 1 ≃ Fin (half p + 1 - 0) :=
    (Equiv.sumCongr e (Equiv.refl _)).trans ((Equiv.sumComm _ _).trans
      (finSumFinEquiv.trans (finCongr (by omega))))
  have hE (i : Fin (n + 2)) : (E (Sum.inl i) : ℕ) = (e i : ℕ) + 1 := by
    change 1 + (e i : ℕ) = (e i : ℕ) + 1
    omega
  have hE0 (i : Fin 1) : (E (Sum.inr i) : ℕ) = 0 := by
    change (i : ℕ) = 0
    omega
  have hχ (i : Fin (n + 2)) :
      legendreSym p (((e i : Fin _) : ℕ) + 1 : ℤ) = cyclicSign i := congrFun hu i
  have hs (i : Fin (n + 2)) :
      legendreSym p ((((e i : Fin _) : ℕ) + 1 : ℤ) ^ 2) = 1 := by
    apply legendreSym.sq_one'
    exact_mod_cast index_ne_zero_mod p (by omega : 0 < (e i : ℕ) + 1) (by omega)
  have hneg (a : ℤ) : legendreSym p (-a) = legendreSym p a := by
    rw [legendreSym.at_neg (by omega), ZMod.χ₄_nat_eq_if_mod_four]
    simp [hp, show p % 2 ≠ 0 by omega]
  rw [← det_submatrix_equiv_self E (entryMatrix p 0 w)]
  congr 1
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · have h := congrFun (congrFun he i) j
    change positiveMatrix p (e i) (e j) = circulant v i j at h
    simp only [submatrix_apply, entryMatrix, hE, Nat.cast_add, Nat.cast_one, Nat.cast_zero,
      add_zero, legendreSym.mul, hχ, fromBlocks_apply₁₁, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, vecMulVec_apply, ← h, positiveMatrix]
    ring
  · simp [entryMatrix, hE, hE0, hs]
  · simp only [submatrix_apply, entryMatrix, hE, hE0, Nat.cast_add, Nat.cast_one, Nat.cast_zero,
      add_zero, zero_pow (by decide : 2 ≠ 0), zero_sub, hneg, hs, zero_mul, add_zero,
      fromBlocks_apply₂₁, of_apply]
    simp
  · simp [entryMatrix, hE0]

theorem cp_exists_one_mod_four (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) :
    ∃! c : ℕ, IsCp p c := by
  have ho : Odd p := Nat.odd_iff.mpr (by omega)
  let h := half p
  let n := h - 2
  let m := h / 2
  have hprime := (Fact.out (p := p.Prime)).two_le
  have hn : half p = n + 2 := by unfold n h half; omega
  have hm : n + 2 = 2 * m := by unfold n m h half; omega
  have hne : Even n := Nat.even_iff.mpr (by omega)
  obtain ⟨e, v, he, hu⟩ := square_circulant_order p n hp hn
  have hv : (circulant v)ᵀ = circulant v := by
    rw [← he]
    apply Matrix.ext
    intro i j
    exact congrFun (congrFun (positiveMatrix_symm p hp) (e i)) (e j)
  obtain ⟨N, hN, hdvd, hcoef⟩ := even_circulant_coefficient n m hm v hv
  have hd : Odd (circulant v).det := by
    rw [← he, det_submatrix_equiv_self]
    exact positiveMatrix_det_odd_even_class p hp
  obtain ⟨k, hk⟩ := hdvd
  have hoddN : Odd N.det := by
    have hz := ZMod.intCast_eq_one_iff_odd.mpr hd
    rw [hk, Int.cast_mul] at hz
    apply ZMod.intCast_eq_one_iff_odd.mp
    exact (show ∀ x y : ZMod 2, x * y = 1 → x = 1 by decide) _ _ hz
  obtain ⟨f, hf⟩ := skew_det_isSquare_int hne N hN
  have hf' : ((f.natAbs : ℤ) ^ 2) = N.det := by
    rw [pow_two, ← Int.natCast_mul, Int.natAbs_mul_self, hf]
  have hodd : Odd f.natAbs := by
    have hz := ZMod.intCast_eq_one_iff_odd.mpr hoddN
    rw [← hf', Int.cast_pow, Int.cast_natCast] at hz
    apply ZMod.natCast_eq_one_iff_odd.mp
    exact (show ∀ z : ZMod 2, z ^ 2 = 1 → z = 1 by decide) _ hz
  have hspec : IsCp p f.natAbs := by
    refine ⟨ho, ?_, hodd, ?_, fun h3 ↦ by omega⟩
    · have := Nat.odd_iff.mp hodd
      omega
    · intro _ w
      have h0 := det_entry_zero_border p n hp e v he hu 0
      simp only [zero_smul, add_zero] at h0
      unfold D
      rw [det_entry_zero_border p n hp e v he hu w, h0, hcoef, ← hn, ← hf', mul_pow]
      ring
  exact ⟨f.natAbs, hspec, fun c hc ↦ cp_unique p hc hspec⟩

theorem even_root_exists : EvenRootExists := by
  intro p hp h
  let : Fact p.Prime := ⟨hp⟩
  exact cp_exists_one_mod_four p h

end ChenSun

#check ChenSun.cp_exists_one_mod_four
#check ChenSun.even_root_exists
#print axioms ChenSun.cp_exists_one_mod_four
#print axioms ChenSun.even_root_exists
```

## ChenSunDoubling.lean

```lean
import ChenSunCharacter

open BigOperators

namespace ChenSun

theorem char_nat_sign (p : ℕ) [Fact p.Prime] {a : ℕ} (ha : 0 < a) (hb : a < p) :
    quadraticChar (ZMod p) (a : ZMod p) = 1 ∨ quadraticChar (ZMod p) (a : ZMod p) = -1 := by
  apply quadraticChar_dichotomy
  intro h
  have hval := ZMod.val_natCast_of_lt hb
  rw [h, ZMod.val_zero] at hval
  omega

theorem odd_char_neg_one (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    quadraticChar (ZMod p) (-1) = -1 := by
  have h : legendreSym p (-1) = -1 := by
    rw [legendreSym.at_neg_one (by omega), ZMod.χ₄_nat_eq_if_mod_four]
    simp [hp, show p % 2 ≠ 0 by omega]
  simpa [legendreSym] using h

theorem odd_char_two (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    quadraticChar (ZMod p) 2 = if p % 8 = 3 then -1 else 1 := by
  rw [show (2 : ZMod p) = ((2 : ℤ) : ZMod p) by norm_num]
  change legendreSym p 2 = _
  rw [legendreSym.at_two (by omega), ZMod.χ₈_nat_eq_if_mod_eight]
  rcases (show p % 8 = 3 ∨ p % 8 = 7 by omega) with h | h <;>
    simp [show p % 2 ≠ 0 by omega, h]

private theorem doubling_perm_sum (p m : ℕ) [Fact p.Prime] (hp : p = 4 * m + 3) :
    let f (a : ℕ) := quadraticChar (ZMod p) (a : ZMod p)
    (∑ i ∈ Finset.range (2 * m + 1), f (i + 1)) =
      (quadraticChar (ZMod p) 2) * (∑ i ∈ Finset.range m, f (i + 1)) -
      (quadraticChar (ZMod p) 2) * (∑ i ∈ Finset.range (m + 1), f (m + i + 1)) := by
  let χ := quadraticChar (ZMod p)
  let f (a : ℕ) := χ (a : ZMod p)
  let d (a : ℕ) := if a ≤ m then 2 * a else p - 2 * a
  let E (i : Fin (2 * m + 1)) : Fin (2 * m + 1) :=
    ⟨d ((i : ℕ) + 1) - 1, by unfold d; have := i.isLt; split <;> omega⟩
  have hd (i : Fin (2 * m + 1)) : (E i : ℕ) + 1 = d ((i : ℕ) + 1) := by
    have hi := i.isLt
    change d ((i : ℕ) + 1) - 1 + 1 = d ((i : ℕ) + 1)
    unfold d
    split <;> omega
  have hinj : Function.Injective E := by
    intro i j hij
    have h := (hd i).symm.trans ((congrArg (fun k : Fin (2 * m + 1) ↦ (k : ℕ) + 1) hij).trans (hd j))
    have hi := i.isLt
    have hj := j.isLt
    apply Fin.ext
    unfold d at h
    split at h <;> split at h <;> omega
  let e := Equiv.ofBijective E ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hsum : (∑ i ∈ Finset.range (2 * m + 1), f (i + 1)) =
      ∑ i ∈ Finset.range (2 * m + 1), f (d (i + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i ↦ f (i + 1)),
      ← Fin.sum_univ_eq_sum_range (fun i ↦ f (d (i + 1)))]
    symm
    apply Fintype.sum_equiv e
    intro i
    exact congrArg f (hd i).symm
  have hlow (a : ℕ) (ha : a ≤ m) : f (d a) = χ 2 * f a := by
    simp [d, ha, f, Nat.cast_mul]
  have hhigh (a : ℕ) (ha : m < a) (ha' : a ≤ 2 * m + 1) : f (d a) = -(χ 2 * f a) := by
    have hneg := odd_char_neg_one p (by omega)
    dsimp only [f, d]
    simp only [show ¬ a ≤ m by omega, ite_false]
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub,
      neg_eq_neg_one_mul, map_mul, Nat.cast_mul, Nat.cast_two, map_mul]
    change χ (-1) * (χ 2 * f a) = _
    rw [show χ (-1) = -1 from hneg, neg_one_mul]
  change (∑ i ∈ Finset.range (2 * m + 1), f (i + 1)) = _
  rw [hsum, show 2 * m + 1 = m + (m + 1) by omega, Finset.sum_range_add]
  have hl : (∑ i ∈ Finset.range m, f (d (i + 1))) = χ 2 * (∑ i ∈ Finset.range m, f (i + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact hlow _ (Finset.mem_range.mp hi)
  have hh : (∑ i ∈ Finset.range (m + 1), f (d (m + i + 1))) =
      -(χ 2 * (∑ i ∈ Finset.range (m + 1), f (m + i + 1))) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have := Finset.mem_range.mp hi
    exact hhigh _ (by omega) (by omega)
  change (∑ i ∈ Finset.range m, f (d (i + 1))) + (∑ i ∈ Finset.range (m + 1), f (d (m + i + 1))) = _
  rw [hl, hh]
  rfl

theorem doubling_balance (p m : ℕ) [Fact p.Prime] (hp : p = 4 * m + 3) :
    let f (a : ℕ) := quadraticChar (ZMod p) (a : ZMod p)
    (Even m → (∑ i ∈ Finset.range m, f (i + 1)) = 0) ∧
    (Odd m → (∑ i ∈ Finset.range (m + 1), f (m + i + 1)) = 0) := by
  let f (a : ℕ) := quadraticChar (ZMod p) (a : ZMod p)
  have hd := doubling_perm_sum p m hp
  change (∑ i ∈ Finset.range (2 * m + 1), f (i + 1)) =
    quadraticChar (ZMod p) 2 * (∑ i ∈ Finset.range m, f (i + 1)) -
    quadraticChar (ZMod p) 2 * (∑ i ∈ Finset.range (m + 1), f (m + i + 1)) at hd
  have h : (∑ i ∈ Finset.range (2 * m + 1), f (i + 1)) =
      (∑ i ∈ Finset.range m, f (i + 1)) + (∑ i ∈ Finset.range (m + 1), f (m + i + 1)) := by
    rw [show 2 * m + 1 = m + (m + 1) by omega, Finset.sum_range_add]
  rw [h, odd_char_two p (by omega)] at hd
  constructor
  · intro hEven
    have he := Nat.even_iff.mp hEven
    simp only [show p % 8 = 3 by omega, ite_true, neg_one_mul] at hd
    change (∑ i ∈ Finset.range m, f (i + 1)) = 0
    omega
  · intro hOdd
    have ho := Nat.odd_iff.mp hOdd
    simp only [show p % 8 ≠ 3 by omega, ite_false, one_mul] at hd
    change (∑ i ∈ Finset.range (m + 1), f (m + i + 1)) = 0
    omega

theorem product_of_balanced_signs {ι : Type*} (s : Finset ι) (f : ι → ℤ) (r : ℕ)
    (hc : s.card = 2 * r) (hs : ∑ i ∈ s, f i = 0)
    (h : ∀ i ∈ s, f i = 1 ∨ f i = -1) : ∏ i ∈ s, f i = (-1) ^ r := by
  classical
  let t := s.filter (fun i ↦ f i = -1)
  let u := s.filter (fun i ↦ ¬f i = -1)
  have ht : t.card + u.card = s.card := Finset.card_filter_add_card_filter_not _
  have hua (i) (hi : i ∈ u) : f i = 1 := by
    obtain ⟨hi', hn⟩ := Finset.mem_filter.mp hi
    exact (h i hi').resolve_right hn
  have hta (i) (hi : i ∈ t) : f i = -1 := (Finset.mem_filter.mp hi).2
  have hsum := Finset.sum_filter_add_sum_filter_not s (fun i ↦ f i = -1) f
  change (∑ i ∈ t, f i) + (∑ i ∈ u, f i) = ∑ i ∈ s, f i at hsum
  rw [Finset.sum_congr rfl hta, Finset.sum_congr rfl hua, hs] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one] at hsum
  have hr : t.card = r := by omega
  have hprod := Finset.prod_filter_mul_prod_filter_not s (fun i ↦ f i = -1) f
  change (∏ i ∈ t, f i) * (∏ i ∈ u, f i) = ∏ i ∈ s, f i at hprod
  rw [Finset.prod_congr rfl hta, Finset.prod_congr rfl hua, Finset.prod_const,
    Finset.prod_const, hr, one_pow, mul_one] at hprod
  exact hprod.symm

end ChenSun
```

## ChenSunOddFactorials.lean

```lean
import ChenSunDoubling

open BigOperators
open scoped Nat

namespace ChenSun

private def evenFactorialProduct (p m : ℕ) [Fact p.Prime] : ℤ :=
  ∏ i ∈ Finset.range m, quadraticChar (ZMod p) ((2 * (i + 1))! : ZMod p)

private theorem evenFactorialProduct_step (p m : ℕ) [hprime : Fact p.Prime]
    (h : 2 * (m + 2) < p) :
    evenFactorialProduct p (m + 2) = evenFactorialProduct p m *
      (quadraticChar (ZMod p) ((2 * m + 3 : ℕ) : ZMod p) *
        quadraticChar (ZMod p) ((2 * m + 4 : ℕ) : ZMod p)) := by
  let χ := quadraticChar (ZMod p)
  have hne : ((2 * (m + 1))! : ZMod p) ≠ 0 := by
    intro hz
    exact (not_le_of_gt (by omega : 2 * (m + 1) < p))
      (hprime.out.dvd_factorial.mp ((ZMod.natCast_eq_zero_iff _ _).mp hz))
  unfold evenFactorialProduct
  rw [Finset.prod_range_succ, Finset.prod_range_succ,
    show 2 * (m + 1 + 1) = 2 * (m + 1) + 1 + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ (2 * (m + 1)),
    Nat.cast_mul, Nat.cast_mul, map_mul, map_mul]
  have hh := quadraticChar_sq_one (F := ZMod p) hne
  rw [pow_two] at hh
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by omega,
    show 2 * m + 3 + 1 = 2 * m + 4 by omega]
  linear_combination
    ((∏ i ∈ Finset.range m, χ ((2 * (i + 1))! : ZMod p)) *
      χ ((2 * m + 3 : ℕ) : ZMod p) * χ ((2 * m + 4 : ℕ) : ZMod p)) * hh

private theorem evenFactorialProduct_pairs (p r : ℕ) [Fact p.Prime]
    (b : ℕ) (h : 2 * (2 * r + b) < p) :
    evenFactorialProduct p (2 * r + b) = evenFactorialProduct p b *
      ∏ s ∈ Finset.range r, quadraticChar (ZMod p) ((4 * s + 2 * b + 3 : ℕ) : ZMod p) *
        quadraticChar (ZMod p) ((4 * s + 2 * b + 4 : ℕ) : ZMod p) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show 2 * (r + 1) + b = (2 * r + b) + 2 by omega, evenFactorialProduct_step p _ (by omega),
      ih (by omega), Finset.prod_range_succ, mul_assoc,
      show 2 * (2 * r + b) + 3 = 4 * r + 2 * b + 3 by omega,
      show 2 * (2 * r + b) + 4 = 4 * r + 2 * b + 4 by omega]

theorem even_factorial_chars_pair_even (p r : ℕ) [Fact p.Prime] (h : 4 * r < p) :
    evenFactorialProduct p (2 * r) =
      ∏ s ∈ Finset.range r, quadraticChar (ZMod p) ((4 * s + 3 : ℕ) : ZMod p) *
        quadraticChar (ZMod p) ((4 * s + 4 : ℕ) : ZMod p) := by
  simpa [evenFactorialProduct] using evenFactorialProduct_pairs p r 0 (by omega)

theorem even_factorial_chars_pair_odd (p r : ℕ) [Fact p.Prime] (h : 4 * r + 2 < p) :
    evenFactorialProduct p (2 * r + 1) =
      ∏ s ∈ Finset.range (r + 1), quadraticChar (ZMod p) ((4 * s + 1 : ℕ) : ZMod p) *
        quadraticChar (ZMod p) ((4 * s + 2 : ℕ) : ZMod p) := by
  let χ := quadraticChar (ZMod p)
  let f (s : ℕ) := χ ((4 * s + 1 : ℕ) : ZMod p) * χ ((4 * s + 2 : ℕ) : ZMod p)
  have h' := evenFactorialProduct_pairs p r 1 (by omega)
  change evenFactorialProduct p (2 * r + 1) = evenFactorialProduct p 1 *
    (∏ s ∈ Finset.range r,
      χ ((4 * s + 2 * 1 + 3 : ℕ) : ZMod p) * χ ((4 * s + 2 * 1 + 4 : ℕ) : ZMod p)) at h'
  change _ = ∏ s ∈ Finset.range (r + 1), f s
  rw [Finset.prod_range_succ' f, h', mul_comm]
  have hbase : evenFactorialProduct p 1 = f 0 := by
    simp [evenFactorialProduct, f, χ]
  rw [hbase]
  congr 1

private theorem odd_char_four (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    quadraticChar (ZMod p) 4 = 1 := by
  have h := odd_char_two p hp
  rw [show (4 : ZMod p) = 2 * 2 by norm_num, map_mul, h]
  split <;> norm_num

private theorem factorial_chars_even_case (p r : ℕ) [Fact p.Prime] (hp : p = 8 * r + 3) :
    evenFactorialProduct p (2 * r) = 1 := by
  let χ := quadraticChar (ZMod p)
  let f (a : ℕ) := χ (a : ZMod p)
  have h4 : χ 4 = 1 := odd_char_four p (by omega)
  have hn : χ (-1) = -1 := odd_char_neg_one p (by omega)
  have hx (s : ℕ) : f (4 * s) = f s := by
    simp only [f, Nat.cast_mul, Nat.cast_ofNat, map_mul, h4, one_mul]
  have hy (s : ℕ) (hs : s < r) : f (4 * s + 3) = -f (2 * r - s) := by
    have hh : (4 * s + 3 : ℕ) + 4 * (2 * r - s) = p := by omega
    have hz : (((4 * s + 3 : ℕ) : ZMod p)) =
        -(((4 * (2 * r - s) : ℕ) : ZMod p)) := by
      apply eq_neg_of_add_eq_zero_left
      rw [← Nat.cast_add, hh, ZMod.natCast_self]
    change χ (((4 * s + 3 : ℕ) : ZMod p)) = _
    rw [hz, neg_eq_neg_one_mul, map_mul, hn, neg_one_mul]
    exact congrArg Neg.neg (hx (2 * r - s))
  have hbal := (doubling_balance p (2 * r) (by omega)).1
    (Nat.even_iff.mpr (by omega))
  have hf : (∏ i ∈ Finset.range (2 * r), f (i + 1)) = (-1) ^ r := by
    refine product_of_balanced_signs _ _ r (by simp) hbal ?_
    intro i hi
    have := Finset.mem_range.mp hi
    exact char_nat_sign p (by omega) (by omega)
  rw [even_factorial_chars_pair_even p r (by omega)]
  have hh : (∏ s ∈ Finset.range r, f (4 * s + 3) * f (4 * s + 4)) =
      (-1) ^ r * ((∏ s ∈ Finset.range r, f (s + 1)) *
        ∏ s ∈ Finset.range r, f (r + s + 1)) := by
    calc
      _ = ∏ s ∈ Finset.range r, (-1) * (f (s + 1) * f (2 * r - s)) := by
        apply Finset.prod_congr rfl
        intro s hs
        rw [hy s (Finset.mem_range.mp hs), show 4 * s + 4 = 4 * (s + 1) by omega, hx]
        ring
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
        congr 2
        rw [← Finset.prod_range_reflect (fun s : ℕ ↦ f (2 * r - s))]
        apply Finset.prod_congr rfl
        intro s hs
        have := Finset.mem_range.mp hs
        congr 1
        omega
  change (∏ s ∈ Finset.range r, f (4 * s + 3) * f (4 * s + 4)) = _
  rw [hh, ← Finset.prod_range_add (fun i ↦ f (i + 1)), ← two_mul, hf, ← pow_two, ← pow_mul]
  exact (Nat.even_iff.mpr (by omega) : Even (r * 2)).neg_one_pow

private theorem pair_positive_prod (f : ℕ → ℤ) (m : ℕ) :
    (∏ i ∈ Finset.range (2 * m), f (i + 1)) =
      ∏ i ∈ Finset.range m, f (2 * i + 1) * f (2 * (i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, Finset.prod_range_succ,
      Finset.prod_range_succ, ih, Finset.prod_range_succ, mul_assoc]
    congr 2

private theorem factorial_chars_odd_case (p r : ℕ) [Fact p.Prime] (hp : p = 8 * r + 7) :
    evenFactorialProduct p (2 * r + 1) = 1 := by
  let m := 2 * r + 1
  let χ := quadraticChar (ZMod p)
  let f (a : ℕ) := χ (a : ZMod p)
  have hm : p = 4 * m + 3 := by omega
  have h2 : χ 2 = 1 := by simpa [χ, show p % 8 ≠ 3 by omega] using odd_char_two p (by omega)
  have h4 : χ 4 = 1 := odd_char_four p (by omega)
  have hn : χ (-1) = -1 := odd_char_neg_one p (by omega)
  have htwice (a : ℕ) : f (2 * a) = f a := by
    simp only [f, Nat.cast_mul, Nat.cast_ofNat, map_mul, h2, one_mul]
  have hfour (a : ℕ) : f (4 * a) = f a := by
    simp only [f, Nat.cast_mul, Nat.cast_ofNat, map_mul, h4, one_mul]
  have h1 (s : ℕ) : f (4 * s + 1) = f (m + s + 1) := by
    have hx : (((4 * s + 1 : ℕ) : ZMod p)) = ((4 * (m + s + 1) : ℕ) : ZMod p) := by
      rw [show 4 * (m + s + 1) = 4 * s + 1 + p by omega,
        Nat.cast_add (4 * s + 1) p, ZMod.natCast_self, add_zero]
    change χ (((4 * s + 1 : ℕ) : ZMod p)) = _
    rw [hx]
    exact hfour (m + s + 1)
  have h2s (s : ℕ) : f (4 * s + 2) = f (2 * s + 1) := by
    rw [show 4 * s + 2 = 2 * (2 * s + 1) by omega, htwice]
  have hbal := (doubling_balance p m hm).2 (Nat.odd_iff.mpr (by omega))
  have hupper : (∏ s ∈ Finset.range (m + 1), f (m + s + 1)) = (-1) ^ (r + 1) := by
    refine product_of_balanced_signs _ _ (r + 1) (by simp [m]; omega) hbal ?_
    intro i hi
    have := Finset.mem_range.mp hi
    exact char_nat_sign p (by omega) (by omega)
  have huv (s : ℕ) (hs : s < r + 1) : f (m + s + 1) = -f (2 * (m - s) + 1) := by
    have hh : 2 * (m + s + 1) + (2 * (m - s) + 1) = p := by omega
    have hz : (((2 * (m + s + 1) : ℕ) : ZMod p)) =
        -(((2 * (m - s) + 1 : ℕ) : ZMod p)) := by
      apply eq_neg_of_add_eq_zero_left
      rw [← Nat.cast_add, hh, ZMod.natCast_self]
    rw [← htwice (m + s + 1)]
    change χ (((2 * (m + s + 1) : ℕ) : ZMod p)) = _
    rw [hz, neg_eq_neg_one_mul, map_mul, hn, neg_one_mul]
  let O := ∏ s ∈ Finset.range (m + 1), f (2 * s + 1)
  have hratio : O = (-1) ^ (r + 1) := by
    let P := ∏ s ∈ Finset.range m, f (s + 1)
    have hP : P ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro s hs
      have := Finset.mem_range.mp hs
      change quadraticChar (ZMod p) ((s + 1 : ℕ) : ZMod p) ≠ 0
      rcases char_nat_sign p (a := s + 1) (by omega) (by omega) with h | h <;> rw [h] <;> decide
    apply mul_right_cancel₀ hP
    have hprod : (∏ i ∈ Finset.range (2 * m + 1), f (i + 1)) = O * P := by
      rw [Finset.prod_range_succ, pair_positive_prod]
      simp_rw [htwice]
      rw [Finset.prod_mul_distrib]
      unfold O P
      rw [Finset.prod_range_succ (fun s ↦ f (2 * s + 1)) m]
      ring
    rw [← hprod, show 2 * m + 1 = m + (m + 1) by omega, Finset.prod_range_add, hupper]
    exact mul_comm _ _
  have hpair : (∏ s ∈ Finset.range (r + 1), f (m + s + 1) * f (2 * s + 1)) =
      (-1) ^ (r + 1) * O := by
    calc
      _ = ∏ s ∈ Finset.range (r + 1), (-1) * (f (2 * s + 1) * f (2 * (m - s) + 1)) := by
        apply Finset.prod_congr rfl
        intro s hs
        rw [huv s (Finset.mem_range.mp hs)]
        ring
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, Finset.prod_mul_distrib]
        congr 1
        unfold O
        rw [show m + 1 = (r + 1) + (r + 1) by omega,
          Finset.prod_range_add (fun s ↦ f (2 * s + 1)) (r + 1) (r + 1)]
        congr 1
        rw [← Finset.prod_range_reflect (fun s : ℕ ↦ f (2 * (m - s) + 1))]
        apply Finset.prod_congr rfl
        intro s hs
        have := Finset.mem_range.mp hs
        congr 1
        omega
  rw [even_factorial_chars_pair_odd p r (by omega)]
  change (∏ s ∈ Finset.range (r + 1), f (4 * s + 1) * f (4 * s + 2)) = _
  simp_rw [h1, h2s]
  rw [hpair, hratio, ← pow_two, ← pow_mul]
  exact (Nat.even_iff.mpr (by omega) : Even ((r + 1) * 2)).neg_one_pow

/-- The product of even factorials in the odd-class character calculation is a residue. -/
theorem even_factorial_product_character (p m : ℕ) [Fact p.Prime] (hp : p = 4 * m + 3) :
    quadraticChar (ZMod p) (∏ i ∈ Finset.range m, ((2 * (i + 1))! : ZMod p)) = 1 := by
  rw [map_prod]
  change evenFactorialProduct p m = 1
  rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
  · rw [show m = 2 * r by omega]
    exact factorial_chars_even_case p r (by omega)
  · rw [show m = 2 * r + 1 by omega]
    exact factorial_chars_odd_case p r (by omega)

end ChenSun

#check ChenSun.even_factorial_product_character
#print axioms ChenSun.even_factorial_product_character
```

## ChenSunPfaffianPermutation.lean

```lean
import ChenSunPfaffian
import Mathlib.GroupTheory.Perm.Fin

open Matrix BigOperators Equiv Equiv.Perm

namespace ChenSun

/-- The two consecutive slots of each pair in a permutation term. -/
def pairSlots (m : ℕ) : Fin m × Fin 2 ≃ Fin (2 * m) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))

@[simp] theorem pairSlots_val (m : ℕ) (k : Fin m) (b : Fin 2) :
    (pairSlots m (k, b) : ℕ) = (b : ℕ) + 2 * (k : ℕ) := rfl

theorem pairSlots_succ (m : ℕ) (k : Fin m) (b : Fin 2) :
    pairSlots (m + 1) (k.succ, b) = (pairSlots m (k, b)).succ.succ := by
  apply Fin.ext
  simp only [pairSlots_val, Fin.val_succ]
  omega

@[simp] theorem pairSlots_zero (m : ℕ) : pairSlots (m + 1) (0, 0) = 0 :=
  Fin.ext rfl

@[simp] theorem pairSlots_one (m : ℕ) : pairSlots (m + 1) (0, 1) = 1 :=
  Fin.ext rfl

def pfTerm {R : Type*} [CommRing R] (m : ℕ)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) R) (σ : Perm (Fin (2 * m))) : R :=
  (↑↑σ.sign : R) * ∏ k : Fin m, A (σ (pairSlots m (k, 0))) (σ (pairSlots m (k, 1)))

noncomputable def pfPermutation {R : Type*} [CommRing R] (m : ℕ)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) R) : R :=
  ∑ σ, pfTerm m A σ

section Invariance

variable {R : Type*} [CommRing R] {m : ℕ}

private theorem pfTerm_pair_swap (A : Matrix (Fin (2 * m)) (Fin (2 * m)) R)
    (σ : Perm (Fin (2 * m))) (τ : Perm (Fin m)) :
    pfTerm m A (σ * (pairSlots m).permCongr (Equiv.prodCongrLeft (fun _ ↦ τ))) = pfTerm m A σ := by
  have hsign : sign (Equiv.prodCongrLeft (fun _ : Fin 2 ↦ τ) : Perm (Fin m × Fin 2)) = 1 := by
    rw [sign_prodCongrLeft, Fin.prod_univ_two]
    exact Int.units_mul_self τ.sign
  have hpair (k : Fin m) (b : Fin 2) :
      (pairSlots m).permCongr (Equiv.prodCongrLeft (fun _ ↦ τ)) (pairSlots m (k, b)) =
        pairSlots m (τ k, b) := by simp [Equiv.permCongr_apply]
  simp only [pfTerm, map_mul, sign_permCongr, hsign, mul_one, Equiv.Perm.mul_apply, hpair]
  congr 1
  exact Fintype.prod_equiv τ _ _ (fun _ ↦ rfl)

private theorem pfTerm_pair_flip (A : Matrix (Fin (2 * m)) (Fin (2 * m)) R)
    (hA : Aᵀ = -A) (σ : Perm (Fin (2 * m))) (j : Fin m) :
    pfTerm m A (σ * (pairSlots m).permCongr (Equiv.Perm.prodExtendRight j (Equiv.swap 0 1))) =
      pfTerm m A σ := by
  let τ := (pairSlots m).permCongr (Equiv.Perm.prodExtendRight j (Equiv.swap 0 1))
  have ht : τ.sign = -1 := by
    simp [τ, sign_swap (by decide : (0 : Fin 2) ≠ 1)]
  have hpair₁ (b : Fin 2) : τ (pairSlots m (j, b)) = pairSlots m (j, Equiv.swap 0 1 b) := by
    simp [τ, Equiv.permCongr_apply]
  have hpair₂ (k : Fin m) (h : k ≠ j) (b : Fin 2) :
      τ (pairSlots m (k, b)) = pairSlots m (k, b) := by
    simp [τ, Equiv.permCongr_apply, Equiv.Perm.prodExtendRight_apply_ne _ h]
  change pfTerm m A (σ * τ) = pfTerm m A σ
  simp only [pfTerm, map_mul, ht, Units.val_neg,
    Int.cast_neg, mul_neg, mul_one, Equiv.Perm.mul_apply]
  have hj : j ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
  rw [← Finset.prod_erase_mul _ _ hj, ← Finset.prod_erase_mul _ _ hj]
  simp only [hpair₁, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have he : (∏ k ∈ Finset.univ.erase j, A (σ (τ (pairSlots m (k, 0)))) (σ (τ (pairSlots m (k, 1))))) =
      ∏ k ∈ Finset.univ.erase j, A (σ (pairSlots m (k, 0))) (σ (pairSlots m (k, 1))) := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [hpair₂ k (Finset.ne_of_mem_erase hk), hpair₂ k (Finset.ne_of_mem_erase hk)]
  rw [he]
  have hsk : A (σ (pairSlots m (j, 1))) (σ (pairSlots m (j, 0))) =
      -A (σ (pairSlots m (j, 0))) (σ (pairSlots m (j, 1))) :=
    congrFun (congrFun hA _) _
  rw [hsk]
  ring

private theorem pfTerm_move_zero
    (A : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) R) (ha : Aᵀ = -A)
    (i : Fin (2 * (m + 1))) :
    ∃ ρ : Perm (Fin (2 * (m + 1))), ρ 0 = i ∧ ∀ σ, pfTerm (m + 1) A (σ * ρ) = pfTerm (m + 1) A σ := by
  obtain ⟨⟨k, b⟩, rfl⟩ := (pairSlots (m + 1)).surjective i
  let τ := (pairSlots (m + 1)).permCongr (Equiv.prodCongrLeft (fun _ : Fin 2 ↦ Equiv.swap 0 k))
  have ht (c : Fin 2) : τ (pairSlots (m + 1) (0, c)) = pairSlots (m + 1) (k, c) := by
    simp [τ, Equiv.permCongr_apply]
  fin_cases b
  · refine ⟨τ, ?_, fun σ ↦ pfTerm_pair_swap A σ _⟩
    simpa using ht 0
  · let f := (pairSlots (m + 1)).permCongr (Equiv.Perm.prodExtendRight (0 : Fin (m + 1)) (Equiv.swap 0 1))
    have hf : f 0 = 1 := by
      calc
        f 0 = f (pairSlots (m + 1) (0, 0)) := by rw [pairSlots_zero]
        _ = 1 := by
          change (pairSlots (m + 1)) (prodExtendRight 0 (swap 0 1)
            ((pairSlots (m + 1)).symm (pairSlots (m + 1) (0, 0)))) = 1
          rw [Equiv.symm_apply_apply, prodExtendRight_apply_eq, Equiv.swap_apply_left, pairSlots_one]
    refine ⟨τ * f, ?_, ?_⟩
    · simpa [Equiv.Perm.mul_apply, hf] using ht 1
    · intro σ
      rw [← mul_assoc, pfTerm_pair_flip A ha, pfTerm_pair_swap A]

private theorem pfPermutation_split_zero
    (A : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) R) (ha : Aᵀ = -A) :
    pfPermutation (m + 1) A = (2 * (m + 1) : ℕ) *
      ∑ σ : Perm (Fin (2 * (m + 1))), if σ 0 = 0 then pfTerm (m + 1) A σ else 0 := by
  classical
  let G := Perm (Fin (2 * (m + 1)))
  let f (i : Fin (2 * (m + 1))) (σ : G) := if σ i = 0 then pfTerm (m + 1) A σ else 0
  have h (i : Fin (2 * (m + 1))) : (∑ σ, f i σ) = ∑ σ, f 0 σ := by
    obtain ⟨ρ, hρ, hinv⟩ := pfTerm_move_zero A ha i
    apply Fintype.sum_equiv (Equiv.mulRight ρ)
    intro σ
    change f i σ = f 0 (σ * ρ)
    have hh : (σ * ρ) 0 = σ i := congrArg σ hρ
    simp only [f, hh, hinv]
  have hsum (σ : G) : (∑ i, f i σ) = pfTerm (m + 1) A σ := by
    simp [f, show ∀ i, σ i = 0 ↔ i = σ.symm 0 from fun i ↦ σ.eq_symm_apply.symm]
  change (∑ σ : G, pfTerm (m + 1) A σ) = (2 * (m + 1) : ℕ) * ∑ σ, f 0 σ
  simp_rw [← hsum]
  rw [Finset.sum_comm]
  simp_rw [h]
  simp [nsmul_eq_mul]

private theorem pfPermutation_zero (A : Matrix (Fin (2 * 0)) (Fin (2 * 0)) R) :
    pfPermutation 0 A = 1 := by
  simp [pfPermutation, pfTerm]

private theorem pfPermutation_one (A : Matrix (Fin (2 * 1)) (Fin (2 * 1)) R)
    (ha : Aᵀ = -A) : pfPermutation 1 A = 2 * pfaffian 1 A := by
  classical
  have h := pfPermutation_split_zero (m := 0) A ha
  have hzero : (∑ σ : Perm (Fin 2), if σ 0 = 0 then pfTerm 1 A σ else 0) = A 0 1 := by
    have hperm (σ : Perm (Fin 2)) : σ 0 = 0 ↔ σ = 1 := by
      constructor
      · intro hs
        apply Equiv.ext
        intro i
        fin_cases i
        · exact hs
        · have hn : σ 1 ≠ 0 := fun he ↦ (by decide : (1 : Fin 2) ≠ 0) (σ.injective (he.trans hs.symm))
          exact (show ∀ j : Fin 2, j ≠ 0 → j = 1 by decide) _ hn
      · rintro rfl
        rfl
    simp [hperm, pfTerm, pairSlots_zero 0, pairSlots_one 0]
  rw [h, hzero]
  simp [pfaffian]

private theorem pfTerm_expansion
    (k : ℕ) (A : Matrix (Fin (2 * (k + 1 + 1))) (Fin (2 * (k + 1 + 1))) R)
    (i : Fin (2 * (k + 1) + 1)) (τ : Perm (Fin (2 * (k + 1)))) :
    pfTerm (k + 1 + 1) A (decomposeFin'Symm 0 (decomposeFin'Symm i τ)) =
      (-1) ^ (i : ℕ) * A 0 i.succ *
        pfTerm (k + 1) (A.submatrix (skipPair (k + 1) i) (skipPair (k + 1) i)) τ := by
  simp only [pfTerm, sign_decomposeFin'Symm, Fin.val_zero, pow_zero, one_mul,
    Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Fin.prod_univ_succ, pairSlots_zero, pairSlots_one,
    decomposeFin'Symm_zero]
  have hA : decomposeFin'Symm 0 (decomposeFin'Symm i τ) 1 = i.succ := by
    rw [← Fin.succ_zero_eq_one, decomposeFin'Symm_succ, decomposeFin'Symm_zero, Fin.succAbove_zero]
  simp only [hA, pairSlots_succ, decomposeFin'Symm_succ, Fin.succAbove_zero, skipPair, submatrix_apply]
  simp only [pairSlots_zero, pairSlots_one]
  ring

private theorem pfPermutation_expand (k : ℕ)
    (A : Matrix (Fin (2 * (k + 1 + 1))) (Fin (2 * (k + 1 + 1))) R)
    (ha : Aᵀ = -A) :
    pfPermutation (k + 1 + 1) A = ((2 * (k + 1 + 1) : ℕ) : R) *
      ∑ i : Fin (2 * (k + 1) + 1), (-1) ^ (i : ℕ) * A 0 i.succ *
        pfPermutation (k + 1) (A.submatrix (skipPair (k + 1) i) (skipPair (k + 1) i)) := by
  classical
  rw [pfPermutation_split_zero A ha]
  congr 1
  let f (σ : Perm (Fin (2 * (k + 1 + 1)))) := if σ 0 = 0 then pfTerm _ A σ else 0
  change (∑ σ, f σ) = _
  let e := decomposeFin' (n := 2 * (k + 1))
  let e' := decomposeFin' (n := 2 * k + 1)
  let g (σ : Perm (Fin (2 * (k + 1) + 1))) := pfTerm _ A (decomposeFin'Symm 0 σ)
  calc
    _ = ∑ z, f (e.symm z) := Fintype.sum_equiv e _ _ (fun σ ↦ by simp)
    _ = ∑ σ, g σ := by
      rw [Fintype.sum_prod_type]
      simp only [e, f, g, decomposeFin'_symm, decomposeFin'Symm_zero,
        Fin.sum_univ_succ, Fin.succ_ne_zero, ite_false, ite_true,
        Finset.sum_const_zero, add_zero]
    _ = ∑ z, g (e'.symm z) := Fintype.sum_equiv e' _ _ (fun σ ↦ by simp)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [e', g, decomposeFin'_symm, pfTerm_expansion, ← Finset.mul_sum, pfPermutation]
      rfl

/-- The permutation sum equals the recursive Pfaffian multiplied by the
number of arrangements of each matching into oriented, ordered pairs. -/
theorem pfPermutation_eq (m : ℕ) (A : Matrix (Fin (2 * m)) (Fin (2 * m)) R)
    (ha : Aᵀ = -A) : pfPermutation m A = (2 : R) ^ m * (m.factorial : R) * pfaffian m A := by
  induction m with
  | zero => simp [pfPermutation_zero, pfaffian]
  | succ m ih =>
    cases m with
    | zero => simpa using pfPermutation_one A ha
    | succ k =>
      rw [pfPermutation_expand k A ha, pfaffian]
      have hm (i : Fin (2 * (k + 1) + 1)) :
          (A.submatrix (skipPair (k + 1) i) (skipPair (k + 1) i))ᵀ =
            -(A.submatrix (skipPair (k + 1) i) (skipPair (k + 1) i)) := by
        apply Matrix.ext
        intro a b
        exact congrFun (congrFun ha (skipPair (k + 1) i a)) (skipPair (k + 1) i b)
      simp_rw [fun i ↦ ih _ (hm i)]
      have hsum : (∑ i : Fin (2 * (k + 1) + 1), (-1 : R) ^ (i : ℕ) * A 0 i.succ *
          ((2 : R) ^ (k + 1) * ((k + 1).factorial : R) *
            pfaffian (k + 1) (A.submatrix (skipPair _ i) (skipPair _ i)))) =
          ((2 : R) ^ (k + 1) * ((k + 1).factorial : R)) *
          (∑ i : Fin (2 * (k + 1) + 1), (-1 : R) ^ (i : ℕ) * A 0 i.succ *
            pfaffian (k + 1) (A.submatrix (skipPair _ i) (skipPair _ i))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsum, pow_succ (2 : R) (k + 1), Nat.factorial_succ (k + 1), Nat.cast_mul]
      push_cast
      ring

end Invariance

end ChenSun
```

## ChenSunPfaffianCongruence.lean

```lean
import ChenSunPfaffianPermutation
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Multilinear.TensorProduct
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Algebra.Algebra.Bilinear

open Matrix BigOperators

namespace ChenSun

section Multilinear

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

private def bilinAsMultilinear (b : M →ₗ[R] M →ₗ[R] R) :
    MultilinearMap R (fun _ : Fin 2 ↦ M) R :=
  (((MultilinearMap.ofSubsingletonₗ R R M R (0 : Fin 1)).toLinearMap).comp b).uncurryLeft

private theorem bilinAsMultilinear_apply (b : M →ₗ[R] M →ₗ[R] R) (v : Fin 2 → M) :
    bilinAsMultilinear b v = b (v 0) (v 1) := rfl

private def pairMultilinear (b : M →ₗ[R] M →ₗ[R] R) (m : ℕ) :
    MultilinearMap R (fun _ : Fin (2 * m) ↦ M) R :=
  match m with
  | 0 => MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 ↦ M) 1
  | m + 1 =>
    let e : Fin 2 ⊕ Fin (2 * m) ≃ Fin (2 * (m + 1)) := finSumFinEquiv.trans (finCongr (by omega))
    ((LinearMap.mul' R R).compMultilinearMap
      ((bilinAsMultilinear b).domCoprod (pairMultilinear b m))).domDomCongr e

private theorem pairMultilinear_apply (b : M →ₗ[R] M →ₗ[R] R) (m : ℕ)
    (v : Fin (2 * m) → M) :
    pairMultilinear b m v = ∏ k : Fin m, b (v (pairSlots m (k, 0))) (v (pairSlots m (k, 1))) := by
  induction m with
  | zero => simp [pairMultilinear]
  | succ m ih =>
    let e : Fin 2 ⊕ Fin (2 * m) ≃ Fin (2 * (m + 1)) := finSumFinEquiv.trans (finCongr (by omega))
    have hL (i : Fin 2) : e (Sum.inl i) = pairSlots (m + 1) (0, i) := by
      apply Fin.ext
      rfl
    have hR (k : Fin m) (i : Fin 2) :
        e (Sum.inr (pairSlots m (k, i))) = pairSlots (m + 1) (k.succ, i) := by
      apply Fin.ext
      change 2 + ((i : ℕ) + 2 * (k : ℕ)) = (i : ℕ) + 2 * ((k : ℕ) + 1)
      omega
    rw [pairMultilinear]
    change ((LinearMap.mul' R R).compMultilinearMap
      ((bilinAsMultilinear b).domCoprod (pairMultilinear b m))).domDomCongr e v = _
    simp only [MultilinearMap.domDomCongr_apply, LinearMap.compMultilinearMap_apply,
      MultilinearMap.domCoprod_apply, LinearMap.mul'_apply, bilinAsMultilinear_apply,
      ih, hL, hR, Fin.prod_univ_succ]

private theorem pfPermutation_alternatization {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (m : ℕ) (B : Matrix (Fin (2 * m)) (Fin n) R) :
    (pairMultilinear A.toBilin' m).alternatization B = pfPermutation m (B * A * Bᵀ) := by
  classical
  have hb (i j) : A.toBilin' (B i) (B j) = (B * A * Bᵀ) i j := by
    rw [Matrix.toBilin'_apply, Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  calc
    _ = ∑ σ : Equiv.Perm (Fin (2 * m)),
        σ.sign • (pairMultilinear A.toBilin' m).domDomCongr σ B :=
      MultilinearMap.alternatization_apply _ (B : Fin (2 * m) → Fin n → R)
    _ = _ := by
      simp only [pfPermutation, pfTerm, Units.smul_def, ← Int.cast_smul_eq_zsmul R, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro σ _
      congr 1
      change pairMultilinear A.toBilin' m (fun i ↦ B (σ i)) = _
      simp only [pairMultilinear_apply, hb]

/-- The sum over permutations is an alternating multilinear form in the rows
of the congruence matrix. -/
theorem pfPermutation_congruence (m : ℕ)
    (A B : Matrix (Fin (2 * m)) (Fin (2 * m)) R) :
    pfPermutation m (B * A * Bᵀ) = B.det * pfPermutation m A := by
  classical
  let f := (pairMultilinear A.toBilin' m).alternatization
  let e := Pi.basisFun R (Fin (2 * m))
  have h := congrFun (congrArg DFunLike.coe (f.eq_smul_basis_det e)) B
  have he : (e : Fin (2 * m) → Fin (2 * m) → R) = (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) R) := by
    funext i j
    simp [e, Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, eq_comm]
  change f B = f e * e.det B at h
  have hb : e.det B = B.det := Pi.basisFun_det_apply (B : Fin (2 * m) → Fin (2 * m) → R)
  rw [he, hb] at h
  have h₁ : f (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) R) = pfPermutation m A := by
    have hh := pfPermutation_alternatization A m 1
    simpa [f] using hh
  rw [h₁] at h
  exact (pfPermutation_alternatization A m B).symm.trans
    (h.trans (mul_comm (pfPermutation m A) B.det))

theorem pfaffian_congruence {F : Type*} [Field F] (m : ℕ)
    (A B : Matrix (Fin (2 * m)) (Fin (2 * m)) F) (hA : Aᵀ = -A)
    (h : (2 : F) ^ m * (m.factorial : F) ≠ 0) :
    pfaffian m (B * A * Bᵀ) = B.det * pfaffian m A := by
  have hBA : (B * A * Bᵀ)ᵀ = -(B * A * Bᵀ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hA,
      Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have hh := pfPermutation_congruence m A B
  rw [pfPermutation_eq m _ hBA, pfPermutation_eq m _ hA] at hh
  apply mul_left_cancel₀ h
  linear_combination hh

end Multilinear

end ChenSun
```

## ChenSunPfaffianSquare.lean

```lean
import ChenSunOddPfaffian
import ChenSunPfaffianCongruence
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Rat.Lemmas

open Matrix BigOperators

namespace ChenSun

private theorem skew_diag_zero {F : Type*} [Field F] [CharZero F]
    {ι : Type*} {A : Matrix ι ι F} (h : Aᵀ = -A) (i : ι) : A i i = 0 := by
  have he : A i i = -A i i := congrFun (congrFun h i) i
  linear_combination (1 / 2 : F) * he

private theorem pfaffian_congruence_rat (n : ℕ)
    (A B : Matrix (Fin (2 * n)) (Fin (2 * n)) ℚ) (h : Aᵀ = -A) :
    pfaffian n (B * A * Bᵀ) = B.det * pfaffian n A :=
  pfaffian_congruence n A B h
    (mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)))

private theorem pfaffian_single_pivot {R : Type*} [CommRing R] (n : ℕ)
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) R)
    (h : ∀ i : Fin (2 * n + 1), i ≠ 0 → A 0 i.succ = 0) :
    pfaffian (n + 1) A = A 0 1 * pfaffian n (A.submatrix (fun i ↦ i.succ.succ) (fun i ↦ i.succ.succ)) := by
  classical
  let f (i : Fin (2 * n + 1)) := (-1 : R) ^ (i : ℕ) * A 0 i.succ *
    pfaffian n (A.submatrix (skipPair n i) (skipPair n i))
  change (∑ i, f i) = _
  rw [Finset.sum_eq_single (f := f) 0]
  · have hskip : skipPair n 0 = fun i ↦ i.succ.succ := by
      funext i
      simp [skipPair]
    simp [f, hskip, Fin.succ_zero_eq_one]
  · intro i _ hi
    simp [f, h i hi]
  · simp

set_option maxHeartbeats 800000 in
private theorem skew_block_pfaffian_square {n : ℕ}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) ℚ) (hA : Aᵀ = -A)
    (h01 : A 0 1 ≠ 0)
    (ih : ∀ B : Matrix (Fin (2 * n)) (Fin (2 * n)) ℚ, Bᵀ = -B → pfaffian n B ^ 2 = B.det) :
    pfaffian (n + 1) A ^ 2 = A.det := by
  classical
  let e : Fin 2 ⊕ Fin (2 * n) ≃ Fin (2 * n + 2) :=
    finSumFinEquiv.trans (finCongr (by omega))
  let T := A.submatrix e e
  let J : Matrix (Fin 2) (Fin 2) ℚ := T.submatrix Sum.inl Sum.inl
  let B : Matrix (Fin 2) (Fin (2 * n)) ℚ := T.submatrix Sum.inl Sum.inr
  let C : Matrix (Fin (2 * n)) (Fin 2) ℚ := T.submatrix Sum.inr Sum.inl
  let D : Matrix (Fin (2 * n)) (Fin (2 * n)) ℚ := T.submatrix Sum.inr Sum.inr
  have hT (i j) : T j i = -T i j := by
    exact congrFun (congrFun hA (e i)) (e j)
  have hJ : Jᵀ = -J := by
    ext i j
    exact hT (Sum.inl i) (Sum.inl j)
  have hD : Dᵀ = -D := by
    ext i j
    exact hT (Sum.inr i) (Sum.inr j)
  have hC : C = -Bᵀ := by
    ext i j
    exact hT (Sum.inl j) (Sum.inr i)
  have hB : Bᵀ = -C := by rw [hC, neg_neg]
  have ha : J 0 1 ≠ 0 := by
    change A (e (Sum.inl 0)) (e (Sum.inl 1)) ≠ 0
    have h0 : e (Sum.inl 0) = 0 := Fin.ext rfl
    have h1 : e (Sum.inl 1) = 1 := Fin.ext rfl
    simpa only [h0, h1] using h01
  let a := J 0 1
  have h10 : J 1 0 = -a := congrFun (congrFun hJ 0) 1
  have hdet : J.det = a ^ 2 := by
    rw [Matrix.det_fin_two, skew_diag_zero hJ, skew_diag_zero hJ, h10]
    change 0 * 0 - a * -a = a ^ 2
    ring
  let : Invertible J := Matrix.invertibleOfIsUnitDet J
    (isUnit_iff_ne_zero.mpr (by rw [hdet]; exact pow_ne_zero _ ha))
  let K : Matrix (Fin 2) (Fin 2) ℚ := !![0, -a⁻¹; a⁻¹, 0]
  have hK : ⅟J = K := by
    apply invOf_eq_right_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, K, h10, skew_diag_zero hJ,
        show a ≠ 0 from ha, a]
  have hKt : Kᵀ = -K := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [K]
  have hS : (D - C * K * B)ᵀ = -(D - C * K * B) := by
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      hD, hB, hKt, hC]
    simp [Matrix.mul_assoc, sub_eq_add_neg, add_comm]
  have heq : Matrix.fromBlocks J B C D = T := by
    ext i j
    cases i <;> cases j <;> rfl
  let E := fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℚ) 0 (-(C * K))
    (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℚ)
  let S := D - C * K * B
  have hk : K * J = 1 := by rw [← hK, invOf_mul_self']
  have hjk : J * K = 1 := by rw [← hK, mul_invOf_self']
  have hET : E * T = fromBlocks J B 0 S := by
    rw [← heq]
    have hCJ : (C * K) * J = C := by rw [Matrix.mul_assoc, hk, Matrix.mul_one]
    simp [E, S, Matrix.fromBlocks_multiply, hCJ, sub_eq_add_neg, add_comm]
  have hEt : Eᵀ = fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℚ) (K * Cᵀ) 0
      (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℚ) := by
    simp [E, Matrix.fromBlocks_transpose, Matrix.transpose_mul, hKt]
  have hE : E * T * Eᵀ = fromBlocks J 0 0 S := by
    rw [hET, hEt, Matrix.fromBlocks_multiply]
    have hCt : Cᵀ = -B := by rw [hC, Matrix.transpose_neg, Matrix.transpose_transpose]
    simp [← Matrix.mul_assoc, hjk, hCt]
  have hdE : E.det = 1 := by simp [E]
  let E' := E.submatrix e.symm e.symm
  let W := E' * A * E'ᵀ
  have hW : W = (fromBlocks J 0 0 S).submatrix e.symm e.symm := by
    change E.submatrix e.symm e.symm * A * (E.submatrix e.symm e.symm)ᵀ = _
    have hA' : A = T.submatrix e.symm e.symm := by
      simp [T, submatrix_submatrix]
    nth_rw 1 [hA']
    change E.submatrix e.symm e.symm * T.submatrix e.symm e.symm * Eᵀ.submatrix e.symm e.symm = _
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hE]
  have he' (i : Fin (2 * n)) : e.symm i.succ.succ = Sum.inr i := by
    apply e.injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    change (i : ℕ) + 1 + 1 = 2 + (i : ℕ)
    omega
  have he0 : e.symm 0 = Sum.inl 0 := by
    apply e.injective
    rw [Equiv.apply_symm_apply]
    rfl
  have he1 : e.symm 1 = Sum.inl 1 := by
    apply e.injective
    rw [Equiv.apply_symm_apply]
    rfl
  have hw01 : W 0 1 = a := by
    rw [hW, Matrix.submatrix_apply, he0, he1]
    rfl
  have hws (i : Fin (2 * n + 1)) (hi : i ≠ 0) : W 0 i.succ = 0 := by
    refine Fin.cases (fun h ↦ (h rfl).elim) (fun j _ ↦ ?_) i hi
    rw [hW, Matrix.submatrix_apply, he0, he']
    rfl
  have hwsub : W.submatrix (fun i ↦ i.succ.succ) (fun i ↦ i.succ.succ) = S := by
    rw [hW]
    apply Matrix.ext
    intro i j
    simp only [Matrix.submatrix_apply, he', Matrix.fromBlocks_apply₂₂]
  have hdE' : E'.det = 1 := (Matrix.det_submatrix_equiv_self e.symm E).trans hdE
  have hpf : pfaffian (n + 1) W = pfaffian (n + 1) A := by
    change pfaffian (n + 1) (E' * A * E'ᵀ) = _
    rw [pfaffian_congruence_rat n.succ A E' hA, hdE', one_mul]
  have hdW : W.det = A.det := by
    simp only [W, det_mul, det_transpose, hdE', one_mul, mul_one]
  rw [← hpf, ← hdW, pfaffian_single_pivot n W hws, hw01, hwsub, mul_pow, ih S hS,
    hW, det_submatrix_equiv_self]
  exact ((Matrix.det_fromBlocks_zero₂₁ J 0 S).trans (by rw [hdet])).symm

/-- The square of the signed recursive Pfaffian is the determinant over the rationals. -/
theorem pfaffian_sq_rat (n : ℕ) (A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℚ)
    (hA : Aᵀ = -A) : pfaffian n A ^ 2 = A.det := by
  classical
  induction n with
  | zero => simp [pfaffian]
  | succ n ih =>
    by_cases h : ∀ j, A 0 j = 0
    · rw [Matrix.det_eq_zero_of_row_eq_zero 0 h, pfaffian]
      simp [h]
    push Not at h
    obtain ⟨j, hj⟩ := h
    have hn : j ≠ 0 := by rintro rfl; exact hj (skew_diag_zero hA 0)
    let σ := Equiv.swap (1 : Fin (2 * n + 2)) j
    let A' := A.submatrix σ σ
    have hσzero : σ 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by simp) hn.symm
    have hσone : σ 1 = j := Equiv.swap_apply_left _ _
    have h01 : A' 0 1 ≠ 0 := by
      simpa only [A', Matrix.submatrix_apply, hσzero, hσone] using hj
    have hA' : A'ᵀ = -A' := by
      apply Matrix.ext
      intro i k
      exact congrFun (congrFun hA (σ i)) (σ k)
    have hmat : σ.permMatrix ℚ * A * (σ.permMatrix ℚ)ᵀ = A' := by
      rw [Matrix.transpose_permMatrix, Equiv.Perm.inv_def, Matrix.mul_assoc,
        PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
      rfl
    have he := pfaffian_congruence_rat n.succ A (σ.permMatrix ℚ) hA
    rw [hmat] at he
    have hd : ((σ.permMatrix ℚ).det) ^ 2 = 1 := by
      rw [Matrix.det_permutation, ← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq]
      norm_num
    have h := skew_block_pfaffian_square A' hA' h01 ih
    rw [he, mul_pow, hd, one_mul] at h
    exact h.trans (Matrix.det_submatrix_equiv_self σ A)

theorem pfaffian_sq_int (n : ℕ) (A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℤ)
    (hA : Aᵀ = -A) : pfaffian n A ^ 2 = A.det := by
  let f := Int.castRingHom ℚ
  have h : (A.map f)ᵀ = -(A.map f) := by
    apply Matrix.ext
    intro i j
    change f (A j i) = -f (A i j)
    rw [← map_neg]
    exact congrArg f (congrFun (congrFun hA i) j)
  apply (Int.cast_injective (α := ℚ))
  change f (pfaffian n A ^ 2) = f A.det
  rw [map_pow, pfaffian_map, RingHom.map_det]
  exact pfaffian_sq_rat n (A.map f) h

theorem sourcePfaffian_sq (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    sourcePfaffian p hp ^ 2 = (positiveMinor p).det := by
  rw [← evenMinor_det p hp]
  exact pfaffian_sq_int _ _ (evenMinor_skew p hp)

end ChenSun
```

## ChenSunOddBinomial.lean

```lean
import ChenSunDoubling
import Mathlib.Data.Nat.Factorial.BigOperators

open BigOperators
open scoped Nat

namespace ChenSun

/-- The half product of binomial coefficients used by the odd-class Pfaffian. -/
def oddBinomialProduct (p m : ℕ) : ZMod p :=
  ∏ i ∈ Finset.range m, ((2 * m + 1).choose (i + 1) : ZMod p)

private theorem odd_binomial_factorials (p m : ℕ) :
    oddBinomialProduct p m * ((∏ i ∈ Finset.range (2 * m), (i ! : ZMod p)) *
      ((2 * m)! : ZMod p)) = ((2 * m + 1)! : ZMod p) ^ m := by
  have hsplit :
      (∏ i ∈ Finset.range (2 * m), (i ! : ZMod p)) * ((2 * m)! : ZMod p) =
      (∏ i ∈ Finset.range m, ((i + 1)! : ZMod p)) *
      (∏ i ∈ Finset.range m, ((2 * m - i)! : ZMod p)) := by
    rw [← Finset.prod_range_succ, Finset.prod_range_succ', Nat.factorial_zero, Nat.cast_one, mul_one,
      show 2 * m = m + m by omega, Finset.prod_range_add]
    congr 1
    rw [← Finset.prod_range_reflect (fun i : ℕ ↦ ((m + m - i)! : ZMod p))]
    apply Finset.prod_congr rfl
    intro i hi
    have := Finset.mem_range.mp hi
    congr 2
    omega
  rw [hsplit, ← Finset.prod_mul_distrib, oddBinomialProduct, ← Finset.prod_mul_distrib]
  have hconst : (∏ _i ∈ Finset.range m, ((2 * m + 1)! : ZMod p)) =
      ((2 * m + 1)! : ZMod p) ^ m := by simp
  rw [← hconst]
  apply Finset.prod_congr rfl
  intro i hi
  have := Finset.mem_range.mp hi
  rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.mul_assoc,
    ← show 2 * m + 1 - (i + 1) = 2 * m - i by omega,
    Nat.choose_mul_factorial_mul_factorial (by omega)]

private theorem char_factorial_sq (p : ℕ) [hprime : Fact p.Prime] {k : ℕ} (hk : k < p) :
    (quadraticChar (ZMod p) (k ! : ZMod p)) ^ 2 = 1 := by
  apply quadraticChar_sq_one
  intro h
  exact (not_le_of_gt hk) (hprime.out.dvd_factorial.mp ((ZMod.natCast_eq_zero_iff _ _).mp h))

private theorem odd_binomial_character_identity (p m : ℕ) [Fact p.Prime] (hp : p = 4 * m + 3) :
    quadraticChar (ZMod p) (oddBinomialProduct p m) *
      quadraticChar (ZMod p) (m ! : ZMod p) =
      quadraticChar (ZMod p) ((2 * m + 1)! : ZMod p) ^ m := by
  let χ := quadraticChar (ZMod p)
  let O := ∏ i ∈ Finset.range m, χ ((2 * i + 1 : ℕ) : ZMod p)
  have hO : O ^ 2 = 1 := by
    unfold O
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro i hi
    have := Finset.mem_range.mp hi
    rcases char_nat_sign p (a := 2 * i + 1) (by omega) (by omega) with h | h <;>
      change (quadraticChar (ZMod p) ((2 * i + 1 : ℕ) : ZMod p)) ^ 2 = 1 <;>
      rw [h] <;> norm_num
  have h2 : χ 2 ^ m = 1 := by
    change (quadraticChar (ZMod p) 2) ^ m = 1
    rw [odd_char_two p (by omega)]
    split
    · exact (Nat.even_iff.mpr (by omega) : Even m).neg_one_pow
    · exact one_pow _
  have hb := congrArg χ (odd_binomial_factorials p m)
  change χ (oddBinomialProduct p m * _) = χ (_ ^ m) at hb
  rw [map_mul, map_mul, map_prod, map_pow,
    factorial_product_character p m (by omega), factorial_character_twice p m χ] at hb
  change χ (oddBinomialProduct p m) * (O * (χ 2 ^ m * χ (m ! : ZMod p) * O)) = _ at hb
  rw [h2, one_mul, show O * (χ (m ! : ZMod p) * O) = O ^ 2 * χ (m ! : ZMod p) by ring,
    hO, one_mul] at hb
  exact hb

private theorem sign_triangle_twice (m : ℕ) :
    (m + ∑ i ∈ Finset.range m, i) * 2 = m * (m + 1) := by
  rw [Nat.add_mul, Finset.sum_range_id_mul_two]
  cases m with
  | zero => simp
  | succ m => simp only [Nat.succ_sub_one]; ring

theorem odd_binomial_character (p m : ℕ) [Fact p.Prime] (hp : p = 4 * m + 3) :
    quadraticChar (ZMod p) (oddBinomialProduct p m) =
      (-1) ^ (m + ∑ i ∈ Finset.range m, i) := by
  let χ := quadraticChar (ZMod p)
  let f (a : ℕ) := χ (a : ZMod p)
  let s := m + ∑ i ∈ Finset.range m, i
  have hs := sign_triangle_twice m
  change s * 2 = m * (m + 1) at hs
  change χ (oddBinomialProduct p m) = (-1 : ℤ) ^ s
  have hb := odd_binomial_character_identity p m hp
  change χ (oddBinomialProduct p m) * χ (m ! : ZMod p) = χ ((2 * m + 1)! : ZMod p) ^ m at hb
  have hm_sq : χ (m ! : ZMod p) ^ 2 = 1 := char_factorial_sq p (by omega)
  have hh_sq : χ ((2 * m + 1)! : ZMod p) ^ 2 = 1 := char_factorial_sq p (by omega)
  have char_fac (k : ℕ) : χ (k ! : ZMod p) = ∏ i ∈ Finset.range k, f (i + 1) := by
    rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod, map_prod]
  rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hm : m = 2 * r := by omega
    have hpow : χ ((2 * m + 1)! : ZMod p) ^ m = 1 := by
      rw [show χ ((2 * m + 1)! : ZMod p) ^ m = χ ((2 * m + 1)! : ZMod p) ^ (2 * r) from congrArg (fun e ↦ _ ^ e) hm]
      rw [pow_mul, hh_sq, one_pow]
    rw [hpow] at hb
    have hS : s = 2 * (r * r) + r := by
      have he : m * (m + 1) = (2 * (r * r) + r) * 2 := by rw [hm]; ring
      omega
    have hsign : (-1 : ℤ) ^ s = (-1) ^ r := by
      rw [hS, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
    have hbal := (doubling_balance p m hp).1 ⟨r, hr⟩
    have hprod : (∏ i ∈ Finset.range m, f (i + 1)) = (-1) ^ r := by
      refine product_of_balanced_signs _ _ r (by simpa) hbal ?_
      intro i hi
      have := Finset.mem_range.mp hi
      exact char_nat_sign p (by omega) (by omega)
    rw [hsign, ← hprod, ← char_fac]
    linear_combination χ (m ! : ZMod p) * hb -
      χ (oddBinomialProduct p m) * hm_sq
  · have hm : m = 2 * r + 1 := by omega
    have hpow : χ ((2 * m + 1)! : ZMod p) ^ m = χ ((2 * m + 1)! : ZMod p) := by
      rw [show χ ((2 * m + 1)! : ZMod p) ^ m = χ ((2 * m + 1)! : ZMod p) ^ (2 * r + 1) from congrArg (fun e ↦ _ ^ e) hm]
      rw [pow_add, pow_mul, hh_sq, one_pow, one_mul, pow_one]
    rw [hpow, char_fac (2 * m + 1)] at hb
    have hsplit : (∏ i ∈ Finset.range (2 * m + 1), f (i + 1)) =
        (∏ i ∈ Finset.range m, f (i + 1)) * ∏ i ∈ Finset.range (m + 1), f (m + i + 1) := by
      rw [show 2 * m + 1 = m + (m + 1) by omega, Finset.prod_range_add]
    rw [hsplit, ← char_fac] at hb
    have hS : s = 2 * (r * (r + 1)) + (r + 1) := by
      have he : m * (m + 1) = (2 * (r * (r + 1)) + (r + 1)) * 2 := by rw [hm]; ring
      omega
    have hsign : (-1 : ℤ) ^ s = (-1) ^ (r + 1) := by
      rw [hS, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
    have hbal := (doubling_balance p m hp).2 ⟨r, hr⟩
    have hprod : (∏ i ∈ Finset.range (m + 1), f (m + i + 1)) = (-1) ^ (r + 1) := by
      refine product_of_balanced_signs _ _ (r + 1) (by simp; omega) hbal ?_
      intro i hi
      have := Finset.mem_range.mp hi
      exact char_nat_sign p (by omega) (by omega)
    rw [hsign, ← hprod]
    apply mul_right_cancel₀ (show χ (m ! : ZMod p) ≠ 0 from fun h ↦ by simp [h] at hm_sq)
    exact hb.trans (mul_comm _ _)

end ChenSun
```

## ChenSunOddWeights.lean

```lean
import ChenSunOddBinomial
import ChenSunOddPfaffian

open Matrix BigOperators

namespace ChenSun

/-- The middle coefficients in the odd-class Vandermonde factorization. -/
def oddWeights (p k : ℕ) : Matrix (Fin (2 * (k + 1))) (Fin (2 * (k + 1))) (ZMod p) :=
  reversedDiagonal (trimWeights p (2 * k + 1))

private theorem oddWeights_apply (p k : ℕ) (i j : Fin (2 * (k + 1))) :
    oddWeights p k i j = if (i : ℕ) + (j : ℕ) + 1 = 2 * (k + 1) then
      (-1) ^ ((j : ℕ) + 1) * ((2 * (k + 1) + 1).choose ((j : ℕ) + 1) : ZMod p) else 0 := by
  have h : i.rev = j ↔ (i : ℕ) + (j : ℕ) + 1 = 2 * (k + 1) := by
    rw [Fin.ext_iff, Fin.val_rev]
    have := i.isLt
    omega
  change diagonal (trimWeights p (2 * k + 1)) i.rev j = _
  by_cases hc : i.rev = j
  · have h' := h.mp hc
    rw [← hc, diagonal_apply_eq]
    simp only [← hc] at h'
    simp only [h', ite_true]
    rfl
  · have h' : ¬ ((i : ℕ) + (j : ℕ) + 1 = 2 * (k + 1)) := mt h.mpr hc
    rw [diagonal_apply_ne _ hc]
    simp only [h', ite_false]

theorem oddWeights_skew (p k : ℕ) :
    (oddWeights p k)ᵀ = -oddWeights p k := by
  apply Matrix.ext
  intro i j
  change oddWeights p k j i = -oddWeights p k i j
  simp only [oddWeights_apply]
  have hiff : (j : ℕ) + (i : ℕ) + 1 = 2 * (k + 1) ↔
      (i : ℕ) + (j : ℕ) + 1 = 2 * (k + 1) := by omega
  simp only [hiff]
  split
  · rename_i h
    have hc : (2 * (k + 1) + 1).choose ((i : ℕ) + 1) =
        (2 * (k + 1) + 1).choose ((j : ℕ) + 1) := by
      conv_lhs => rw [← Nat.choose_symm (by omega : (i : ℕ) + 1 ≤ 2 * (k + 1) + 1)]
      congr 1
      omega
    have hs : (-1 : ZMod p) ^ ((i : ℕ) + 1) = -((-1) ^ ((j : ℕ) + 1)) := by
      rcases Nat.even_or_odd ((i : ℕ) + 1) with he | ho
      · have hj : Odd ((j : ℕ) + 1) := Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)
        rw [he.neg_one_pow, hj.neg_one_pow, neg_neg]
      · have hj : Even ((j : ℕ) + 1) := Nat.even_iff.mpr (by have := Nat.odd_iff.mp ho; omega)
        rw [ho.neg_one_pow, hj.neg_one_pow]
    rw [hc, hs, neg_mul]
  · rw [neg_zero]

theorem oddWeights_pfaffian_character (p k : ℕ) [Fact p.Prime]
    (hp : p = 4 * (k + 1) + 3) :
    quadraticChar (ZMod p) (pfaffian (k + 1) (oddWeights p k)) = (-1) ^ (k + 1) := by
  let m := k + 1
  let χ := quadraticChar (ZMod p)
  let a (i : ℕ) : ZMod p := (-1) ^ (2 * m - i) * ((2 * m + 1).choose (i + 1) : ZMod p)
  have hc : oddWeights p k = antidiagonal m a := by
    apply Matrix.ext
    intro i j
    rw [oddWeights_apply]
    change _ = if (i : ℕ) + (j : ℕ) + 1 = 2 * m then a i else 0
    split
    · rename_i h
      have he : (j : ℕ) + 1 = 2 * m - (i : ℕ) := by omega
      have h' : (2 * m + 1).choose ((j : ℕ) + 1) = (2 * m + 1).choose ((i : ℕ) + 1) := by
        conv_lhs => rw [← Nat.choose_symm (by omega : (j : ℕ) + 1 ≤ 2 * m + 1)]
        congr 1
        omega
      change ((-1 : ZMod p) ^ ((j : ℕ) + 1) * ((2 * m + 1).choose ((j : ℕ) + 1) : ZMod p)) = a i
      have hPow := congrArg (fun j : ℕ ↦ (-1 : ZMod p) ^ j) he
      rw [hPow, h']
    · rfl
  change χ (pfaffian m (oddWeights p k)) = _
  rw [hc, pfaffian_antidiagonal]
  have hfac : (∏ i ∈ Finset.range m, a i) =
      (∏ i ∈ Finset.range m, (-1 : ZMod p) ^ i) * oddBinomialProduct p m := by
    rw [oddBinomialProduct, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have hlt := Finset.mem_range.mp hi
    have hh : (-1 : ZMod p) ^ (2 * m - i) = (-1) ^ i := by
      rcases Nat.even_or_odd i with he | ho
      · have h : Even (2 * m - i) := Nat.even_iff.mpr (by have := Nat.even_iff.mp he; omega)
        rw [he.neg_one_pow, h.neg_one_pow]
      · have h : Odd (2 * m - i) := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp ho; omega)
        rw [ho.neg_one_pow, h.neg_one_pow]
    simp only [a, hh]
  rw [hfac, map_mul, Finset.prod_pow_eq_pow_sum, map_pow,
    show χ (-1) = -1 from odd_char_neg_one p (by omega), odd_binomial_character p m (by omega),
    ← pow_add]
  change (-1 : ℤ) ^ ((∑ i ∈ Finset.range m, i) + (m + ∑ i ∈ Finset.range m, i)) = (-1) ^ m
  rw [show (∑ i ∈ Finset.range m, i) + (m + ∑ i ∈ Finset.range m, i) =
    m + 2 * (∑ i ∈ Finset.range m, i) by omega, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

end ChenSun
```

## ChenSunOddVandermondeSign.lean

```lean
import ChenSunOddWeights

open Matrix BigOperators

namespace ChenSun

theorem upper_sign_product {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ i j, i < j → A i j = 1 ∨ A i j = -1) :
    (∏ i, ∏ j ∈ Finset.Ioi i, A i j) = (-1) ^ (negativeUpperEntries A).card := by
  classical
  calc
    _ = ∏ i : Fin n, ∏ j : Fin n, if i < j then A i j else 1 := by
      congr with i
      have he : Finset.Ioi i = Finset.univ.filter (fun j : Fin n ↦ i < j) := by ext j; simp
      rw [he, Finset.prod_filter]
    _ = ∏ q : Fin n × Fin n, if q.1 < q.2 ∧ A q.1 q.2 = -1 then (-1 : ℤ) else 1 := by
      rw [Fintype.prod_prod_type]
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_congr rfl
      intro j _
      by_cases hij : i < j
      · rcases h i j hij with hs | hs <;> simp [hij, hs]
      · simp [hij]
    _ = _ := by
      rw [← Finset.prod_filter, Finset.prod_const]
      rfl

private theorem prod_neg_powers_even {R : Type*} [CommRing R] (m : ℕ) :
    (∏ i : Fin (2 * m), (-1 : R) ^ (i : ℕ)) = (-1) ^ m := by
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ ↦ (-1 : R) ^ i)]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, Finset.prod_range_succ,
      Finset.prod_range_succ, ih, (show Even (2 * m) from ⟨m, by omega⟩).neg_one_pow,
      (show Odd (2 * m + 1) from Nat.odd_iff.mpr (by omega)).neg_one_pow,
      mul_one, pow_succ]

private theorem det_vandermonde_neg_points {R : Type*} [CommRing R] (m : ℕ)
    (x : Fin (2 * m) → R) :
    (vandermonde (fun i ↦ -x i)).det = (vandermonde x).det * (-1) ^ m := by
  have h : vandermonde (fun i ↦ -x i) = vandermonde x *
      diagonal (fun i : Fin (2 * m) ↦ (-1 : R) ^ (i : ℕ)) := by
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_diagonal, Matrix.vandermonde_apply, Matrix.vandermonde_apply,
      neg_eq_neg_one_mul, mul_pow, mul_comm]
  rw [h, det_mul, det_diagonal, prod_neg_powers_even]

/-- The upper signs capture the character of the Vandermonde on the negated points. -/
theorem upper_sign_vandermonde (p m : ℕ) [Fact p.Prime] (hp : p % 4 = 3)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℤ) (x : Fin (2 * m) → ZMod p)
    (h : ∀ i j, i < j → A i j = 1 ∨ A i j = -1)
    (hx : ∀ i j, i < j → A i j = quadraticChar (ZMod p) (x i - x j)) :
    ZMod.χ₄ ((pfaffian m A : ℤ) : ZMod 4) =
      quadraticChar (ZMod p) (vandermonde x).det * (-1) ^ m := by
  let χ := quadraticChar (ZMod p)
  have hmod := int_pfaffian_mod_four m A h
  rw [hmod, map_pow, show ZMod.χ₄ (-1 : ZMod 4) = -1 by decide, ← upper_sign_product A h]
  have hprod : (∏ i, ∏ j ∈ Finset.Ioi i, A i j) =
      χ (vandermonde (fun i ↦ -x i)).det := by
    rw [det_vandermonde, map_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro j hj
    rw [hx i j (Finset.mem_Ioi.mp hj)]
    change χ (x i - x j) = χ (-x j - -x i)
    congr 1
    ring
  rw [hprod, det_vandermonde_neg_points, map_mul, map_pow, odd_char_neg_one p hp]

end ChenSun
```

## ChenSunFinal.lean

```lean
import ChenSunEvenExistence
import ChenSunPfaffianSquare
import ChenSunOddVandermondeSign
import ChenSunOddFactorials

open Matrix BigOperators

namespace ChenSun

private theorem odd_signed_root_at (p k : ℕ) [hprime : Fact p.Prime]
    (hp : p = 4 * (k + 1) + 3) :
    ∃ f : ℤ, f ^ 2 = (positiveMinor p).det ∧ legendreSym p f = ZMod.χ₄ (f : ZMod 4) := by
  let m := k + 1
  have hp3 : p % 4 = 3 := by omega
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hh : half p = 2 * k + 1 + 2 := by unfold half; omega
  let e : Fin (2 * m) ≃ Fin (half p - 1) := finCongr (by omega)
  let A := (positiveMinor p).submatrix e e
  let f := pfaffian m A
  let x (i : Fin (2 * m)) : ZMod p := (((i : ℕ) + 2 : ℕ) : ZMod p) ^ 2
  let V := vandermonde x
  let X := diagonal x
  let B := X * V
  let C := oddWeights p k
  let χ := quadraticChar (ZMod p)
  have hA : Aᵀ = -A := by
    apply Matrix.ext
    intro i j
    exact congrFun (congrFun (positiveMatrix_skew p hp3) (skipFirst (half p) (e i)))
      (skipFirst (half p) (e j))
  have hx (i : Fin (2 * m)) : χ (x i) = 1 := by
    apply quadraticChar_sq_one'
    exact index_ne_zero_mod p (by omega) (by omega)
  have hfac : A.map (Int.castRingHom (ZMod p)) = B * C * Bᵀ := by
    have h := odd_minor_mod_factorization p (2 * k + 1) hp3 hh
    change A.map (Int.castRingHom (ZMod p)) = X * (V * C * Vᵀ) * X at h
    rw [h]
    simp only [B, transpose_mul, X, diagonal_transpose, Matrix.mul_assoc]
  have htwo : (2 : ZMod p) ≠ 0 := by
    have ht := index_ne_zero_mod p (j := 2) (by decide) (by omega)
    exact_mod_cast ht
  have hfct : (m.factorial : ZMod p) ≠ 0 := by
    intro hz
    have hd := hprime.out.dvd_factorial.mp ((ZMod.natCast_eq_zero_iff _ _).mp hz)
    omega
  have hfcast : (f : ZMod p) = B.det * pfaffian m C := by
    change (Int.castRingHom (ZMod p)) (pfaffian m A) = _
    rw [pfaffian_map, hfac, pfaffian_congruence m C B (oddWeights_skew p k)
      (mul_ne_zero (pow_ne_zero _ htwo) hfct)]
  have hdetX : χ X.det = 1 := by
    change χ (diagonal x).det = 1
    rw [det_diagonal, map_prod]
    simp [hx]
  have hleg : legendreSym p f = χ V.det * (-1) ^ m := by
    change χ (f : ZMod p) = _
    rw [hfcast, map_mul, show B.det = X.det * V.det from det_mul _ _, map_mul, hdetX, one_mul,
      show χ (pfaffian m C) = (-1) ^ m from oddWeights_pfaffian_character p k hp]
  have hfour : ZMod.χ₄ (f : ZMod 4) = χ V.det * (-1) ^ m := by
    apply upper_sign_vandermonde p m hp3 A x
    · intro i j hij
      exact positiveMinor_offdiag_sign p hpodd (e.injective.ne hij.ne)
    · intro i j _
      change legendreSym p (((i : ℕ) + 1 + 1 : ℤ) ^ 2 -
        ((j : ℕ) + 1 + 1 : ℤ) ^ 2) = χ (x i - x j)
      simp [legendreSym, x, χ, add_assoc]
  refine ⟨f, ?_, hleg.trans hfour.symm⟩
  exact (pfaffian_sq_int m A hA).trans (det_submatrix_equiv_self e (positiveMinor p))

theorem odd_signed_root : OddSignedRoot := by
  intro p hp hlt h3
  let : Fact p.Prime := ⟨hp⟩
  let k := (p - 7) / 4
  exact odd_signed_root_at p k (by unfold k; omega)

theorem chen_sun_conjecture : Conjecture :=
  conjecture_iff_odd_signed_root.mpr odd_signed_root

theorem chen_sun_conjecture_with_root : ConjectureWithRoot :=
  conjecture_with_root_iff.mpr ⟨even_root_exists, odd_signed_root⟩

theorem jacobi_cp_eq_one (p : ℕ) [hp : Fact p.Prime] (ho : Odd p) :
    jacobiSym (p : ℤ) (cp p ho) = 1 :=
  (chen_sun_conjecture_with_root p hp.out ho).2

end ChenSun

#check ChenSun.sourcePfaffian_sq
#check ChenSun.pfaffian_congruence
#check ChenSun.odd_binomial_character
#check ChenSun.even_factorial_product_character
#check ChenSun.odd_signed_root
#check ChenSun.even_root_exists
#check ChenSun.chen_sun_conjecture
#check ChenSun.chen_sun_conjecture_with_root
#check ChenSun.jacobi_cp_eq_one
#print axioms ChenSun.sourcePfaffian_sq
#print axioms ChenSun.pfaffian_congruence
#print axioms ChenSun.odd_binomial_character
#print axioms ChenSun.even_factorial_product_character
#print axioms ChenSun.odd_signed_root
#print axioms ChenSun.even_root_exists
#print axioms ChenSun.chen_sun_conjecture
#print axioms ChenSun.chen_sun_conjecture_with_root
#print axioms ChenSun.jacobi_cp_eq_one
```

