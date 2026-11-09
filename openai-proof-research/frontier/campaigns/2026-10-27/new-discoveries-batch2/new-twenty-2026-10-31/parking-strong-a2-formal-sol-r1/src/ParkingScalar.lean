module
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Tactic.Ring

public section
namespace ParkingScalar
variable {K : Type*} [Field K] [CharZero K]
@[expose] def theta1 (x y : K) : K := (x^10 + 3*x^4*y^6)/4
@[expose] def theta2 (x y : K) : K := (y^10 + 3*x^6*y^4)/4

theorem directional_identity (x y : K) :
    y * theta1 x y - x * theta2 x y = x*y*(x^3-y^3)^3/4 := by
  unfold theta1 theta2
  ring

theorem homogeneous1 (a x y : K) : theta1 (a*x) (a*y) = a^10 * theta1 x y := by
  unfold theta1
  ring

theorem homogeneous2 (a x y : K) : theta2 (a*x) (a*y) = a^10 * theta2 x y := by
  unfold theta2
  ring

theorem common_zero (x y : K) (hx : theta1 x y = 0) (hy : theta2 x y = 0) :
    x = 0 ∧ y = 0 := by
  have h4 : (4 : K) ≠ 0 := by exact OfNat.ofNat_ne_zero 4
  have a := (div_eq_iff h4).mp hx
  have b := (div_eq_iff h4).mp hy
  simp only [zero_mul] at a b
  by_cases hxo : x = 0
  · subst x
    simp only [zero_pow (by decide : 6 ≠ 0),
      mul_zero, zero_mul, add_zero] at b
    exact ⟨rfl, (pow_eq_zero_iff (by decide : 10 ≠ 0)).mp b⟩
  by_cases hyo : y = 0
  · subst y
    simp only [zero_pow (by decide : 6 ≠ 0), mul_zero, add_zero] at a
    exact ⟨(pow_eq_zero_iff (by decide : 10 ≠ 0)).mp a, rfl⟩
  have a' : x^6 + 3*y^6 = 0 := by
    apply (mul_eq_zero.mp (show x^4 * (x^6 + 3*y^6) = 0 from by
      calc _ = x^10 + 3*x^4*y^6 := by ring
           _ = 0 := a)).resolve_left (pow_ne_zero _ hxo)
  have b' : y^6 + 3*x^6 = 0 := by
    apply (mul_eq_zero.mp (show y^4 * (y^6 + 3*x^6) = 0 from by
      calc _ = y^10 + 3*x^6*y^4 := by ring
           _ = 0 := b)).resolve_left (pow_ne_zero _ hyo)
  have h8 : (8:K)*x^6 = 0 := by
    calc _ = 3*(y^6+3*x^6)-(x^6+3*y^6) := by ring
         _ = 0 := by rw [a', b']; ring
  have xx : x^6 = 0 := (mul_eq_zero.mp h8).resolve_left (show (8:K) ≠ 0 from OfNat.ofNat_ne_zero 8)
  exact False.elim (hxo ((pow_eq_zero_iff (by decide : 6 ≠ 0)).mp xx))

theorem fixed_directions (x y : K) (hx : theta1 x y = x) (hy : theta2 x y = y) :
    x = 0 ∨ y = 0 ∨ x^3 = y^3 := by
  have h4 : (4:K) ≠ 0 := OfNat.ofNat_ne_zero 4
  have hh : x*y*(x^3-y^3)^3 = 0 := by
    have hh0 : x*y*(x^3-y^3)^3/4 = 0 := by
      rw [← directional_identity, hx, hy]
      ring
    simpa only [zero_mul] using (div_eq_iff h4).mp hh0
  rcases mul_eq_zero.mp hh with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (sub_eq_zero.mp ((pow_eq_zero_iff (by decide : 3 ≠ 0)).mp h)))

theorem line_values (x y : K) (h : x^3 = y^3) :
    theta1 x y = x*y^9 ∧ theta2 x y = y*y^9 := by
  constructor
  · unfold theta1
    calc _ = (x*(x^3)^3+3*x*(x^3)*y^6)/4 := by ring
         _ = x*y^9 := by rw [h]; ring
  · unfold theta2
    calc _ = (y^10+3*(x^3)^2*y^4)/4 := by ring
         _ = y*y^9 := by rw [h]; ring

theorem off_axes_ninth (x y : K) (hy0 : y ≠ 0) (h : x^3 = y^3)
    (hy : theta2 x y = y) : y^9 = 1 := by
  apply mul_left_cancel₀ hy0
  calc y*y^9 = theta2 x y := (line_values x y h).2.symm
       _ = y*1 := by rw [hy, mul_one]

#print axioms fixed_directions
#print axioms line_values
#print axioms off_axes_ninth
#print axioms homogeneous1
#print axioms homogeneous2
#print axioms common_zero
#print axioms theta1
#print axioms theta2
#print axioms directional_identity
end ParkingScalar
