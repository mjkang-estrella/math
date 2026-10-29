import MidpointParity
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Eval.Degree

set_option autoImplicit false
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

noncomputable section
namespace JacobiShifted.Midpoint
open Polynomial JacobiShifted.BinaryFiltration

theorem polynomial_neg_fixed_zero {p : ZPoly} (hp : -p=p) : p=0 := by
  apply Polynomial.ext
  intro k
  have hk := congrArg (fun f : ZPoly => f.coeff k) hp
  simp only [coeff_neg] at hk
  have hz : p.coeff k = 0 := by omega
  simpa using hz

theorem h_even_j_im_zero (n i j : ℕ) (hj : Even j) :
    ((h n).coeff (bidegree i j)).im = 0 := by
  have hp := congrArg QuadraticAlgebra.im (h_rho_coefficient n i j)
  rw [hj.neg_one_pow, one_mul] at hp
  exact polynomial_neg_fixed_zero hp

theorem h_odd_j_re_zero (n i j : ℕ) (hj : Odd j) :
    ((h n).coeff (bidegree i j)).re = 0 := by
  have hp := congrArg QuadraticAlgebra.re (h_rho_coefficient n i j)
  rw [hj.neg_one_pow, neg_one_mul] at hp
  exact polynomial_neg_fixed_zero hp.symm

theorem h_odd_order_coordinates (n : ℕ) (hn : Odd n) (α : Exponent) :
    flip ((h n).coeff α).re = ((h n).coeff α).re ∧
      flip ((h n).coeff α).im = -((h n).coeff α).im := by
  have he : Even (n+1) := hn.add_odd odd_one
  have hp := h_tau_coefficient n α
  rw [he.neg_one_pow, one_mul] at hp
  constructor
  · exact congrArg QuadraticAlgebra.re hp
  · have hi := congrArg QuadraticAlgebra.im hp
    simpa using congrArg Neg.neg hi

/-- The substitution formula is proved over integers, before any localization. -/
theorem flip_coeff (p : ZPoly) (k : ℕ) :
    (flip p).coeff k = p.coeff k * (-1 : ℤ)^k := by
  rw [flip_apply, show (-X : ZPoly) = Polynomial.C (-1 : ℤ)*X by simp]
  exact Polynomial.comp_C_mul_X_coeff

theorem even_coeff_odd_zero {p : ZPoly} (hp : flip p=p) (k : ℕ) (hk : Odd k) :
    p.coeff k = 0 := by
  have hc := congrArg (fun f : ZPoly => f.coeff k) hp
  rw [flip_coeff, hk.neg_one_pow, mul_neg_one] at hc
  omega

theorem odd_coeff_even_zero {p : ZPoly} (hp : flip p = -p) (k : ℕ) (hk : Even k) :
    p.coeff k = 0 := by
  have hc := congrArg (fun f : ZPoly => f.coeff k) hp
  rw [flip_coeff, hk.neg_one_pow, mul_one, coeff_neg] at hc
  omega

/-- Actual extraction by coefficients at even powers. -/
def evenExtract (p : ZPoly) : ZPoly := Polynomial.contract 2 p

/-- Actual extraction by coefficients at odd powers. -/
def oddExtract (p : ZPoly) : ZPoly := Polynomial.contract 2 p.divX

@[simp] theorem evenExtract_coeff (p : ZPoly) (k : ℕ) :
    (evenExtract p).coeff k = p.coeff (2*k) := by
  simp [evenExtract, coeff_contract, mul_comm]

@[simp] theorem oddExtract_coeff (p : ZPoly) (k : ℕ) :
    (oddExtract p).coeff k = p.coeff (2*k+1) := by
  simp [oddExtract, coeff_contract, coeff_divX, mul_comm]

theorem evenExtract_spec {p : ZPoly} (hp : flip p=p) :
    p = (evenExtract p).comp (X^2) := by
  apply Polynomial.ext
  intro k
  change p.coeff k = (Polynomial.expand ℤ 2 (evenExtract p)).coeff k
  rw [coeff_expand (by omega)]
  split_ifs with hk
  · rw [evenExtract_coeff, Nat.mul_div_cancel' hk]
  · have ho : Odd k := (Nat.even_or_odd k).resolve_left (fun h => hk (even_iff_two_dvd.mp h))
    exact even_coeff_odd_zero hp k ho

theorem odd_divX_even {p : ZPoly} (hp : flip p = -p) : flip p.divX = p.divX := by
  apply Polynomial.ext
  intro k
  rw [flip_coeff, coeff_divX]
  rcases Nat.even_or_odd k with he | ho
  · rw [he.neg_one_pow, mul_one]
  · rw [odd_coeff_even_zero hp (k+1) (ho.add_odd odd_one)]
    simp

theorem oddExtract_spec {p : ZPoly} (hp : flip p = -p) :
    p = X*(oddExtract p).comp (X^2) := by
  have h0 := odd_coeff_even_zero hp 0 (by exact ⟨0,rfl⟩)
  have hx := X_mul_divX_add p
  rw [h0, C_0, add_zero] at hx
  calc
    p = X*p.divX := hx.symm
    _ = X*(oddExtract p).comp (X^2) := by
      congr 1
      exact evenExtract_spec (odd_divX_even hp)

theorem q_ne_zero : q ≠ 0 := by
  intro he
  have h0 := congrArg (fun f : ZPoly => f.coeff 0) he
  simp [q] at h0

/-- Cancellation in `ℤ[X]` proves the quotient is even; this is not a parity premise. -/
theorem even_quotient {p a : ZPoly} (hp : flip p=p) (ha : p=q*a) : flip a=a := by
  apply mul_left_cancel₀ q_ne_zero
  calc
    q*flip a = flip (q*a) := by rw [map_mul, flip_q]
    _ = q*a := by rw [← ha, hp, ha]

/-- A usable integral normal form with both coordinate polynomials identified. -/
def normalForm (A B : ZPoly) : R :=
  ⟨q*A.comp (X^2), X*B.comp (X^2)⟩

theorem normalForm_ring (A B : ZPoly) :
    normalForm A B = (1+x^2)*C (A.comp (X^2)) + w*x*C (B.comp (X^2)) := by
  rw [← w_sq, pow_two]
  apply QuadraticAlgebra.ext
  · simp only [normalForm, QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul,
      C_re, C_im, w_re, w_im, x_re, x_im]
    ring
  · simp only [normalForm, QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul,
      C_re, C_im, w_re, w_im, x_re, x_im, QuadraticAlgebra.re_mul]
    ring

theorem integral_normalForm (z : R) (hr : flip z.re=z.re)
    (hi : flip z.im = -z.im) (hw : q ∣ z.re) :
    ∃ A : ZPoly, z=normalForm A (oddExtract z.im) := by
  obtain ⟨a,ha⟩ := hw
  refine ⟨evenExtract a, ?_⟩
  apply QuadraticAlgebra.ext
  · change z.re = q*(evenExtract a).comp (X^2)
    rw [← evenExtract_spec (even_quotient hr ha), ← ha]
  · exact oddExtract_spec hi

/-- Divisibility in the quadratic algebra gives genuine divisibility of integer
coefficients of the imaginary coordinate. -/
theorem integral_im_coeff_divisible (z : R) (e : ℕ) (hz : (2 : R)^e ∣ z) (k : ℕ) :
    (2 : ℤ)^e ∣ z.im.coeff k := by
  have hm : C ((2 : ZPoly)^e) ∣ z := by simpa only [map_pow, map_ofNat] using hz
  have hi : (2 : ZPoly)^e ∣ z.im :=
    (QuadraticAlgebra.algebraMap_dvd_iff.mp hm).2
  have hc : Polynomial.C ((2 : ℤ)^e) ∣ z.im := by
    simpa only [map_pow, map_ofNat] using hi
  exact (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hc k

theorem oddExtract_preserves_divisibility (z : R) (e : ℕ)
    (hz : (2 : R)^e ∣ z) (k : ℕ) :
    (2 : ℤ)^e ∣ (oddExtract z.im).coeff k := by
  rw [oddExtract_coeff]
  exact integral_im_coeff_divisible z e hz (2*k+1)

theorem oddExtract_zero : oddExtract 0 = 0 := by
  apply Polynomial.ext
  intro k
  simp

/-- Closed extraction for the concrete sequence at every odd spectral index. -/
theorem h_odd_normalForm (n i j : ℕ) (hn : Odd n) :
    ∃ A B : ZPoly,
      (h n).coeff (bidegree i j) = normalForm A B ∧
      (∀ k : ℕ, B.coeff k = ((h n).coeff (bidegree i j)).im.coeff (2*k+1)) ∧
      (Odd j → ∀ k : ℕ, (2 : ℤ)^sigma (i+j-1) ∣ B.coeff k) ∧
      (Even j → B=0) ∧ (Odd j → A=0) := by
  let z := (h n).coeff (bidegree i j)
  obtain ⟨hr,hi⟩ := h_odd_order_coordinates n hn (bidegree i j)
  obtain ⟨A,hA⟩ := integral_normalForm z hr hi (h_coefficient_re_divisible n (bidegree i j))
  refine ⟨A,oddExtract z.im,hA,?_,?_,?_,?_⟩
  · intro k
    exact oddExtract_coeff z.im k
  · intro hj k
    exact oddExtract_preserves_divisibility z (sigma (i+j-1))
      (h_odd_coefficient_divisible n i j (i+j) hj rfl) k
  · intro hj
    rw [show z.im=0 from h_even_j_im_zero n i j hj, oddExtract_zero]
  · intro hj
    have hz := h_odd_j_re_zero n i j hj
    have he : q*A.comp (X^2)=0 := by
      have hh := congrArg QuadraticAlgebra.re hA
      exact hh.symm.trans hz
    have ha : A.comp (X^2)=0 := (mul_eq_zero.mp he).resolve_left q_ne_zero
    exact (Polynomial.expand_eq_zero (R := ℤ) (by omega : 0<2)).mp ha

/-- The extracted odd polynomial satisfies divisibility in `ℤ[X]` itself. -/
theorem h_odd_extraction_divisible (n i j : ℕ) (hj : Odd j) :
    (2 : ZPoly)^sigma (i+j-1) ∣ oddExtract ((h n).coeff (bidegree i j)).im := by
  have hc : Polynomial.C ((2 : ℤ)^sigma (i+j-1)) ∣
      oddExtract ((h n).coeff (bidegree i j)).im := by
    apply (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr
    intro k
    exact oddExtract_preserves_divisibility _ _
      (h_odd_coefficient_divisible n i j (i+j) hj rfl) k
  simpa only [map_pow, map_ofNat] using hc

/-- Direct ring-expression interface, with canonical odd-part extraction. -/
theorem h_odd_normalForm_ring (n i j : ℕ) (hn : Odd n) :
    ∃ A : ZPoly, (h n).coeff (bidegree i j) =
      (1+x^2)*C (A.comp (X^2)) +
        w*x*C ((oddExtract ((h n).coeff (bidegree i j)).im).comp (X^2)) := by
  obtain ⟨hr,hi⟩ := h_odd_order_coordinates n hn (bidegree i j)
  obtain ⟨A,hA⟩ := integral_normalForm _ hr hi (h_coefficient_re_divisible n (bidegree i j))
  exact ⟨A,hA.trans (normalForm_ring _ _)⟩

end JacobiShifted.Midpoint
