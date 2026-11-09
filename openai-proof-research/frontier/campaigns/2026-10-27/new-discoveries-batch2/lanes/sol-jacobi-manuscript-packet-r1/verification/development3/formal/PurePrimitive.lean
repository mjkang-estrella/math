import ScaledTop
import MidpointPrimitive
import BinomialOddSum

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section
namespace JacobiShifted.SourceBridge
open MidpointRational

@[simp] theorem rationalBase_two : rationalBase (2 : ℚ)=(2 : QAlg) := map_ofNat rationalBase 2

/-- The explicit finite odd primitive, with rational coefficients embedded as
constants (not as the polynomial indeterminate). -/
def purePrimitive (r : ℕ) : QAlg :=
  rationalBase ((catalan (r-1) : ℚ)/(2 : ℚ)^(2*r-1))*
    ∑ j ∈ Finset.range r, rationalBase (((r-1).choose j : ℚ)/(2*j+1))*t^(2*j+1)

theorem t_quadratic : 1+t^2=2*(w*t) := by
  dsimp [t]
  linear_combination -w_sq

theorem delta_t_pow (n : ℕ) : delta (t^n)= -(n : QAlg)*w*t^n := by
  cases n with
  | zero =>
    have he : delta (1 : QAlg)=0 := by simpa only [derivation_apply] using derivation.map_one_eq_zero
    simp [he]
  | succ n =>
    have he := derivation.leibniz_pow t (n+1)
    simp only [derivation_apply, Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul, delta_t] at he
    rw [he, pow_succ]
    ring

theorem delta_odd_term (j : ℕ) (q : ℚ) :
    delta (rationalBase (q/(2*j+1))*t^(2*j+1))=
      -rationalBase q*(w*t)*(t^2)^j := by
  rw [partial_mul, delta_rationalBase, zero_mul, zero_add, delta_t_pow]
  have hn : ((2*j+1 : ℕ) : QAlg)=rationalBase ((2*j+1 : ℕ) : ℚ) := by simp
  have hc : rationalBase (q/(2*j+1))*((2*j+1 : ℕ) : QAlg)=rationalBase q := by
    rw [hn, ← map_mul]
    apply congrArg rationalBase
    push_cast
    field_simp
  calc
    _ = -(rationalBase (q/(2*j+1))*((2*j+1 : ℕ) : QAlg))*w*t^(2*j+1) := by ring
    _ = _ := by rw [hc, pow_succ, pow_mul]; ring

theorem binomial_t_sum (m : ℕ) :
    (∑ j ∈ Finset.range (m+1), rationalBase (m.choose j : ℚ)*(t^2)^j)=(1+t^2)^m := by
  rw [add_comm (1 : QAlg), add_pow]
  apply Finset.sum_congr rfl
  intro j _
  simp only [one_pow, mul_one, map_natCast]
  ring

theorem delta_purePrimitive (r : ℕ) (hr : 1≤r) :
    delta (purePrimitive r)= -rationalBase ((catalan (r-1) : ℚ)/(2 : ℚ)^r)*(w*t)^r := by
  rw [purePrimitive, partial_mul, delta_rationalBase, zero_mul, zero_add, map_sum]
  simp_rw [delta_odd_term]
  have hs : (∑ j ∈ Finset.range r, -rationalBase (((r-1).choose j : ℚ))*(w*t)*(t^2)^j)=
      -(w*t)*(1+t^2)^(r-1) := by
    rw [show r=r-1+1 by omega, ← binomial_t_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs,t_quadratic,mul_pow]
  have hp : (w*t)*(w*t)^(r-1)=(w*t)^r := by
    rw [← pow_succ']
    congr 1
    omega
  have htwo : (2 : QAlg)^(r-1)=rationalBase ((2 : ℚ)^(r-1)) := by simp
  have hc : ((catalan (r-1) : ℚ)/(2 : ℚ)^(2*r-1))*2^(r-1)=
      (catalan (r-1) : ℚ)/(2 : ℚ)^r := by
    rw [show 2*r-1=r+(r-1) by omega, pow_add]
    field_simp
  calc
    _ = -(rationalBase ((catalan (r-1) : ℚ)/(2 : ℚ)^(2*r-1))*(2 : QAlg)^(r-1))*
        ((w*t)*(w*t)^(r-1)) := by ring
    _ = _ := by rw [htwo, ← map_mul, hc,hp]

theorem tau_purePrimitive (r : ℕ) : tau (purePrimitive r)= -purePrimitive r := by
  have ht : tau t= -t := by simp [t]; ring
  have ho (j : ℕ) : (-t)^(2*j+1)= -t^(2*j+1) := Odd.neg_pow ⟨j,by omega⟩ t
  simp only [purePrimitive,map_mul,map_sum,tau_rationalBase,map_pow,ht,ho,
    mul_neg, Finset.sum_neg_distrib]

theorem midpoint_purePrimitive (r : ℕ) (hr : 1≤r) :
    midpoint (purePrimitive r)=
      (catalan (r-1) : ℚ)*binomialOddSum (r-1)/(2 : ℚ)^(2*r-1) := by
  have ht : midpoint t=1 := by simp [t]
  simp only [purePrimitive,map_mul,map_sum,midpoint_rationalBase,map_pow,ht,one_pow,mul_one]
  have hs : (∑ j ∈ Finset.range r, ((r-1).choose j : ℚ)/(2*j+1))=binomialOddSum (r-1) := by
    rw [binomialOddSum,show r-1+1=r by omega]
  rw [hs]
  ring

end JacobiShifted.SourceBridge
