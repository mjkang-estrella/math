import ParameterDegree
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

noncomputable section
namespace JacobiShifted.ParameterDegree
open MvPolynomial
open JacobiShifted.BinaryFiltration hiding P
open JacobiShifted.Midpoint

/-- A finite parity split with the final even index retained. -/
theorem sum_range_parity {T : Type*} [AddCommMonoid T] (f : ℕ → T) (n : ℕ) :
    (∑ i ∈ Finset.range (2*n+1), f i)=
      (∑ j ∈ Finset.range (n+1), f (2*j))+
      ∑ j ∈ Finset.range n, f (2*j+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)+1=(2*n+1)+1+1 by omega]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    rw [Finset.sum_range_succ (fun j => f (2*j)) (n+1),
      Finset.sum_range_succ (fun j => f (2*j+1)) n]
    simp only [Nat.mul_add, Nat.mul_one]
    ac_rfl

def oddTop (k : ℕ) : Param := homogeneousComponent (k+1) (h (2*k+1))

theorem oddTop_zero : oddTop 0=P := by
  rw [oddTop]
  simp only [Nat.mul_zero, zero_add, h_one]
  apply homogeneousComponent_eq_self
  rw [P, initial_eq_variables]
  apply IsHomogeneous.add
  · simpa only [mul_comm] using isHomogeneous_C_mul_X (w^2) (0 : Fin 2)
  · simpa only [mul_comm] using isHomogeneous_C_mul_X (w*x) (1 : Fin 2)

/-- The actual recurrence supplies the Catalan convolution: the derivative and
all even-even products vanish at this degree by the proved degree bound. -/
theorem oddTop_recurrence (r : ℕ) (hr : 1≤r) :
    oddTop r= -∑ j ∈ Finset.range r, oddTop j*oddTop (r-1-j) := by
  rw [oddTop, h_recurrence (2*r) (by omega), map_sub, map_neg, map_sum]
  have hd : homogeneousComponent (r+1) (coefficientOperator delta (h (2*r)))=0 := by
    apply homogeneousComponent_eq_zero
    have hb := (coefficientOperator_totalDegree delta (h (2*r))).trans (h_totalDegree (2*r))
    omega
  rw [hd, neg_zero, zero_sub, sum_range_parity]
  have he : (∑ j ∈ Finset.range (r+1),
      homogeneousComponent (r+1) (h (2*j)*h (2*r-2*j)))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjr : j≤r := by simpa using hj
    apply homogeneousComponent_eq_zero
    have ha := h_totalDegree (2*j)
    have hb := h_totalDegree (2*r-2*j)
    have hc := totalDegree_mul (h (2*j)) (h (2*r-2*j))
    omega
  rw [he, zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j<r := Finset.mem_range.mp hj
  have hn : 2*r-(2*j+1)=2*(r-1-j)+1 := by omega
  rw [hn]
  change homogeneousComponent (r+1) (h (2*j+1)*h (2*(r-1-j)+1))=_
  rw [show r+1=(j+1)+(r-1-j+1) by omega]
  exact top_mul _ _ _ _ (by have := h_totalDegree (2*j+1); omega)
    (by have := h_totalDegree (2*(r-1-j)+1); omega)

/-- Catalan leading layer, derived from the concrete sequence rather than an
assumed recurrence for leading coefficients. -/
theorem oddTop_catalan (k : ℕ) :
    oddTop k=MvPolynomial.C ((-1 : R)^k*(catalan k : R))*P^(k+1) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [oddTop_zero]
    | succ k =>
      rw [oddTop_recurrence (k+1) (by omega)]
      have ht : ∀ j ∈ Finset.range (k+1),
          -(oddTop j*oddTop (k+1-1-j))=
          MvPolynomial.C ((-1 : R)^(k+1)*((catalan j : R)*(catalan (k-j) : R)))*P^(k+1+1) := by
        intro j hj
        have hjk : j≤k := by simpa using hj
        rw [ih j (by omega), ih (k+1-1-j) (by omega)]
        simp only [Nat.add_sub_cancel]
        have hs : -((-1 : R)^j*(-1 : R)^(k-j))=(-1 : R)^(k+1) := by
          rw [← pow_add, Nat.add_sub_of_le hjk, pow_succ]
          ring
        have hp : P^(j+1)*P^(k-j+1)=P^(k+1+1) := by
          rw [← pow_add]
          congr 1
          omega
        calc
          _ = MvPolynomial.C (-((-1 : R)^j*(-1 : R)^(k-j))*
                ((catalan j : R)*(catalan (k-j) : R)))*(P^(j+1)*P^(k-j+1)) := by
              simp only [map_mul, map_neg]
              ring
          _ = _ := by rw [hs,hp]
      rw [← Finset.sum_neg_distrib]
      simp_rw [Finset.sum_congr rfl ht]
      rw [← Finset.sum_mul, ← map_sum]
      congr 2
      rw [← Finset.mul_sum]
      congr 1
      have hc := catalan_succ k
      rw [Fin.sum_univ_eq_sum_range (fun j => catalan j*catalan (k-j)) (k+1)] at hc
      rw [hc, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.cast_mul]

/-- The exact degree-r homogeneous component at every positive odd order. -/
theorem h_odd_top (r : ℕ) (hr : 1≤r) :
    homogeneousComponent r (h (2*r-1))=
      MvPolynomial.C ((-1 : R)^(r-1)*(catalan (r-1) : R))*P^r := by
  have he : 2*r-1=2*(r-1)+1 := by omega
  have hs : r-1+1=r := by omega
  simpa only [oddTop, he, hs] using oddTop_catalan (r-1)

/-- All bidegrees of total degree r, with no restriction to a pure monomial. -/
theorem h_odd_top_coeff (r : ℕ) (hr : 1≤r) (a : Exponent) (ha : a.degree=r) :
    (h (2*r-1)).coeff a=
      ((-1 : R)^(r-1)*(catalan (r-1) : R))*(P^r).coeff a := by
  have he := congrArg (fun f : Param => f.coeff a) (h_odd_top r hr)
  simpa only [coeff_homogeneousComponent, ha, ite_true, coeff_C_mul] using he

end JacobiShifted.ParameterDegree
