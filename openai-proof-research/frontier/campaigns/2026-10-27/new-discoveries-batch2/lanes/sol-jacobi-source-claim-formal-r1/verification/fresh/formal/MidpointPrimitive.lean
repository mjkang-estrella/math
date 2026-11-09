import OddTriangular

set_option autoImplicit false
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace JacobiShifted.MidpointRational
open Polynomial

/-- Finite odd integration: only the odd integers `2k+1` are divided out. -/
def realIntegral (A : QPoly) : QPoly :=
  -(∑ k ∈ A.support, Polynomial.C (A.coeff k / (2*(k : ℚ)+1))*X^(2*k+1))

theorem sum_even (A : QPoly) :
    (∑ k ∈ A.support, Polynomial.C (A.coeff k)*X^(2*k)) = A.comp (X^2) := by
  conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq A]
  simp only [Polynomial.sum, sum_comp, mul_comp, C_comp, pow_comp, X_comp, ← pow_mul]

theorem derivative_odd_term (k : ℕ) (a : ℚ) :
    derivative (Polynomial.C (a/(2*(k : ℚ)+1))*X^(2*k+1)) =
      Polynomial.C a * X^(2*k) := by
  have hd : 2*(k : ℚ)+1 ≠ 0 := by positivity
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_pow, derivative_X,
    mul_one, Nat.add_sub_cancel]
  rw [← mul_assoc, ← Polynomial.C_mul]
  congr 1
  push_cast
  exact congrArg Polynomial.C (div_mul_cancel₀ a hd)

theorem derivative_realIntegral (A : QPoly) : derivative (realIntegral A) = -A.comp (X^2) := by
  simp only [realIntegral, derivative_neg, derivative_sum, derivative_odd_term]
  rw [sum_even]

theorem realIntegral_zero_eval (A : QPoly) : (realIntegral A).eval 0=0 := by
  simp [realIntegral, Polynomial.eval_finsetSum]

theorem flip_even_comp (f : QPoly) : flip (f.comp (X^2)) = f.comp (X^2) := by
  simp [flip_apply, Polynomial.comp_assoc]

theorem flip_realIntegral (A : QPoly) : flip (realIntegral A) = -realIntegral A := by
  simp [realIntegral, flip_apply, Polynomial.sum_comp, pow_add, pow_mul]

theorem delta_realIntegral (A : QPoly) :
    delta (C (realIntegral A)) = C (q*A.comp (X^2)) := by
  apply QuadraticAlgebra.ext <;> simp [derivative_realIntegral]

/-- The genuine quadratic primitive identity in the midpoint algebra. -/
theorem delta_quadratic (f : QPoly) :
    delta (w*C (f.comp (X^2))) = -w*x*C ((T f).comp (X^2)) := by
  have hs (g : QPoly) : w*C g = (⟨0,g⟩ : QAlg) := by
    apply QuadraticAlgebra.ext <;> simp
  have hx (g : QPoly) : -w*x*C g = (⟨0,-X*g⟩ : QAlg) := by
    apply QuadraticAlgebra.ext <;> simp
  rw [hs,hx]
  apply QuadraticAlgebra.ext
  · simp [delta]
  · change -X*f.comp (X^2)-q*derivative (f.comp (X^2)) = -X*(T f).comp (X^2)
    simp [T, q, derivative_comp, derivative_pow, Polynomial.C_ofNat]
    ring

/-- Expanded version of the same differential identity. -/
theorem delta_quadratic_expanded (f : QPoly) :
    delta (w*C (f.comp (X^2))) =
      -w*x*C (f.comp (X^2) + 2*(1+X^2)*(derivative f).comp (X^2)) := by
  rw [delta_quadratic]
  simp [T]

/-- A concrete tau-odd primitive for an integral midpoint normal form. -/
def primitive (A B : Midpoint.ZPoly) : QAlg :=
  C (realIntegral (zmap A)) + w*C ((inverseT (-zmap B)).comp (X^2))

@[simp] theorem primitive_re (A B : Midpoint.ZPoly) :
    (primitive A B).re = realIntegral (zmap A) := by simp [primitive, w]
@[simp] theorem primitive_im (A B : Midpoint.ZPoly) :
    (primitive A B).im = (inverseT (-zmap B)).comp (X^2) := by simp [primitive, w]

theorem primitive_delta (A B : Midpoint.ZPoly) :
    delta (primitive A B) = lift (Midpoint.normalForm A B) := by
  rw [primitive, map_add, delta_quadratic, T_inverseT]
  apply QuadraticAlgebra.ext
  · simp [C, delta, derivative_realIntegral, Midpoint.normalForm, zmap_comp, map_mul]
  · simp [w, x, C, Midpoint.normalForm, zmap_comp, map_mul]

theorem primitive_tau (A B : Midpoint.ZPoly) : tau (primitive A B) = -primitive A B := by
  apply QuadraticAlgebra.ext <;> simp [flip_realIntegral, flip_even_comp]

theorem primitive_midpoint (A B : Midpoint.ZPoly) :
    midpoint (primitive A B) = (inverseT (-zmap B)).coeff 0 := by
  simp [midpoint_apply, realIntegral_zero_eval, Polynomial.coeff_zero_eq_eval_zero]

/-- Integer polynomial divisibility supplies localization after division by `2^e`. -/
theorem zmap_twoLocal_of_dvd (B : Midpoint.ZPoly) (e : ℕ) (hB : (2 : Midpoint.ZPoly)^e ∣ B) :
    ∀ k : ℕ, TwoLocal ((zmap B).coeff k / (2 : ℚ)^e) := by
  obtain ⟨D,rfl⟩ := hB
  intro k
  have hh : zmap ((2 : Midpoint.ZPoly)^e * D) = Polynomial.C ((2 : ℚ)^e) * zmap D := by
    simp only [map_mul, map_pow, map_ofNat]
  rw [hh, coeff_C_mul, mul_div_cancel_left₀ _ (pow_ne_zero e (by norm_num)), zmap_coeff]
  exact twoLocal_int (D.coeff k)

theorem primitive_midpoint_twoLocal (A B : Midpoint.ZPoly) (e : ℕ)
    (hB : (2 : Midpoint.ZPoly)^e ∣ B) :
    TwoLocal (midpoint (primitive A B) / (2 : ℚ)^e) := by
  rw [primitive_midpoint]
  apply inverseT_twoLocal
  intro k
  simp only [coeff_neg, neg_div]
  exact twoLocal_neg (zmap_twoLocal_of_dvd B e hB k)

/-- A coordinate equation forces the quadratic part of every constant to vanish. -/
theorem imaginary_kernel (g : QPoly) (hg : X*g+q*derivative g=0) : g=0 := by
  by_contra hn
  let n := g.natDegree
  have hz : g.coeff (n+2)=0 := coeff_eq_zero_of_natDegree_lt (by dsimp [n]; omega)
  have hc := congrArg (fun p : QPoly => p.coeff (n+1)) hg
  have form : X*g+q*derivative g = X*g + derivative g + X*(X*derivative g) := by
    dsimp [q]; ring
  rw [form] at hc
  simp only [coeff_add, coeff_X_mul, coeff_derivative, coeff_X_derivative, coeff_zero,
    Nat.cast_add, Nat.cast_one] at hc
  rw [hz] at hc
  have hd : (n : ℚ)+1 ≠ 0 := by positivity
  have hh : ((n : ℚ)+1)*g.coeff n=0 := by linear_combination hc
  exact (leadingCoeff_ne_zero.mpr hn) ((mul_eq_zero.mp hh).resolve_left hd)

/-- The differential kernel consists exactly of scalar rational constants. -/
theorem delta_kernel (p : QAlg) : delta p=0 ↔ ∃ a : ℚ, p=C (Polynomial.C a) := by
  constructor
  · intro hp
    have hr := congrArg QuadraticAlgebra.re hp
    have hi := congrArg QuadraticAlgebra.im hp
    have hq : q ≠ 0 := by
      intro h
      have h0 := congrArg (fun f : QPoly => f.coeff 0) h
      simp [q] at h0
    have hd : derivative p.re=0 := by
      have hh : -q*derivative p.re=0 := hr
      exact (mul_eq_zero.mp hh).resolve_left (neg_ne_zero.mpr hq)
    have him : p.im=0 := imaginary_kernel p.im (by
      change -X*p.im-q*derivative p.im=0 at hi
      linear_combination -hi)
    refine ⟨p.re.coeff 0, ?_⟩
    apply QuadraticAlgebra.ext
    · exact eq_C_of_derivative_eq_zero hd
    · simpa using him
  · rintro ⟨a,rfl⟩
    apply QuadraticAlgebra.ext <;> simp [delta, C]

/-- Tau-oddness removes the entire differential kernel. -/
theorem normalized_kernel {p : QAlg} (hp : delta p=0) (ht : tau p = -p) : p=0 := by
  obtain ⟨a,rfl⟩ := (delta_kernel p).mp hp
  have hr := congrArg (fun z : QAlg => z.re.coeff 0) ht
  have ha : a=0 := by
    simp [C, flip_apply] at hr
    linear_combination (1/2 : ℚ)*hr
  simp [ha]

theorem normalized_unique {p r : QAlg} (hd : delta p=delta r)
    (hp : tau p = -p) (hr : tau r = -r) : p=r := by
  apply sub_eq_zero.mp
  apply normalized_kernel
  · simp [map_sub, hd]
  · simp [map_sub, hp, hr]; ring

theorem primitive_unique (A B : Midpoint.ZPoly) {p : QAlg}
    (hd : delta p=lift (Midpoint.normalForm A B)) (ht : tau p = -p) : p=primitive A B :=
  normalized_unique (hd.trans (primitive_delta A B).symm) ht (primitive_tau A B)

theorem normalForm_primitive_existsUnique (A B : Midpoint.ZPoly) :
    ∃! p : QAlg, delta p=lift (Midpoint.normalForm A B) ∧ tau p = -p := by
  exact ⟨primitive A B, ⟨primitive_delta A B,primitive_tau A B⟩,
    fun p hp => primitive_unique A B hp.1 hp.2⟩

end JacobiShifted.MidpointRational
