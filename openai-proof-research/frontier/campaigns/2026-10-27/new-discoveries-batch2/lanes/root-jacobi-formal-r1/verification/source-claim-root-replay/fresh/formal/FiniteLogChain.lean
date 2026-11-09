import LiteralFinite
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

noncomputable section
namespace JacobiShifted.SourceBridge.FiniteChain

variable {R : Type*} [CommRing R]

/-- Coefficientwise extension, unrelated to differentiation in the series variable. -/
def liftD (d : R →+ R) : PowerSeries R →+ PowerSeries R where
  toFun f := PowerSeries.mk fun n => d (PowerSeries.coeff n f)
  map_zero' := by ext n; simp
  map_add' f g := by ext n; simp

@[simp] theorem coeff_liftD (d : R →+ R) (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (liftD d f)=d (PowerSeries.coeff n f) := by simp [liftD]

@[simp] theorem liftD_C (d : R →+ R) (a : R) :
    liftD d (PowerSeries.C a)=PowerSeries.C (d a) := by
  ext n
  simp only [coeff_liftD, PowerSeries.coeff_C]
  split_ifs <;> simp

theorem liftD_mul (d : R →+ R)
    (hd : ∀ a b, d (a*b)=d a*b+a*d b) (f g : PowerSeries R) :
    liftD d (f*g)=liftD d f*g+f*liftD d g := by
  ext n
  simp only [coeff_liftD, PowerSeries.coeff_mul, map_sum, hd,
    map_add, Finset.sum_add_distrib]

theorem liftD_pow (d : R →+ R) (hd : ∀ a b, d (a*b)=d a*b+a*d b)
    (h1 : d 1=0) (f : PowerSeries R) (k : ℕ) :
    liftD d (f^(k+1))=PowerSeries.C (k+1 : R)*f^k*liftD d f := by
  have hone : liftD d 1=0 := by
    rw [← map_one (PowerSeries.C : R →+* PowerSeries R), liftD_C, h1, map_zero]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, liftD_mul d hd, ih, Nat.cast_add, Nat.cast_one, pow_succ]
    simp only [map_add, map_one]
    ring

theorem coeff_mul_range (f g : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (f*g)=
      ∑ j ∈ Finset.range (n+1), PowerSeries.coeff j f*PowerSeries.coeff (n-j) g := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem coeff_finitePower (f : ℕ → R) (k n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.mk f)^k)=finitePower f k n := by
  induction k generalizing n with
  | zero => simp [finitePower]
  | succ k ih =>
    rw [pow_succ', coeff_mul_range]
    simp only [PowerSeries.coeff_mk, ih, finitePower]

theorem coeff_pow_vanish (a : PowerSeries R) (h0 : PowerSeries.coeff 0 a=0)
    (k n : ℕ) (hn : n<k) : PowerSeries.coeff n (a^k)=0 := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    rw [pow_succ', coeff_mul_range]
    apply Finset.sum_eq_zero
    intro j hj
    have hjn : j≤n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
    by_cases hj0 : j=0
    · simp [hj0, h0]
    · rw [ih (n-j) (by omega), mul_zero]

/-- Finite logarithm polynomial, with positive powers indexed from zero. -/
def truncLog (q : ℚ →+* R) (a : PowerSeries R) (N : ℕ) : PowerSeries R :=
  ∑ k ∈ Finset.range N,
    PowerSeries.C (q (((-1 : ℚ)^(k+2))/(k+1 : ℚ)))*a^(k+1)

theorem log_scalar (q : ℚ →+* R) (k : ℕ) :
    q (((-1 : ℚ)^(k+2))/(k+1 : ℚ))*(k+1 : R)=q ((-1 : ℚ)^k) := by
  rw [show (k+1 : R)=q (k+1 : ℚ) by simp, ← map_mul]
  congr 1
  have hk : (k+1 : ℚ)≠0 := by positivity
  field_simp
  ring

theorem liftD_truncLog (d : R →+ R) (hd : ∀ a b, d (a*b)=d a*b+a*d b)
    (h1 : d 1=0) (q : ℚ →+* R) (hq : ∀ r, d (q r)=0)
    (a : PowerSeries R) (N : ℕ) :
    liftD d (truncLog q a N)=
      liftD d a * ∑ k ∈ Finset.range N, (-a)^k := by
  simp only [truncLog, map_sum, liftD_mul d hd, liftD_C, hq,
    map_zero, zero_mul, zero_add, liftD_pow d hd h1, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← mul_assoc, ← mul_assoc, ← map_mul, log_scalar]
  rw [map_pow, map_neg, map_one, map_pow, map_neg, map_one]
  rw [neg_pow]
  ring

theorem geometric (a : PowerSeries R) (N : ℕ) :
    (1+a)*(∑ k ∈ Finset.range N, (-a)^k)=1-(-a)^N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

theorem truncated_chain (d : R →+ R) (hd : ∀ a b, d (a*b)=d a*b+a*d b)
    (h1 : d 1=0) (q : ℚ →+* R) (hq : ∀ r, d (q r)=0)
    (a : PowerSeries R) (N : ℕ) :
    (1+a)*liftD d (truncLog q a N)=liftD d a*(1-(-a)^N) := by
  rw [liftD_truncLog d hd h1 q hq]
  calc
    _ = liftD d a*((1+a)*∑ k ∈ Finset.range N, (-a)^k) := by ring
    _ = _ := by rw [geometric]

/-- The positive-power truncation has the exact literal finite-log coefficient. -/
theorem coeff_truncLog (q : ℚ →+* R) (f : ℕ → R) (N n : ℕ) (hn : n<N) :
    PowerSeries.coeff n (truncLog q (PowerSeries.mk (augment f)) N)=
      ∑ k ∈ Finset.range (n+1), if k=0 then 0 else
        q (((-1 : ℚ)^(k+1))/(k : ℚ))*finitePower (augment f) k n := by
  have h0 : PowerSeries.coeff 0 (PowerSeries.mk (augment f))=0 := by simp [augment]
  have hext : PowerSeries.coeff n (truncLog q (PowerSeries.mk (augment f)) N)=
      PowerSeries.coeff n (truncLog q (PowerSeries.mk (augment f)) n) := by
    simp only [truncLog, map_sum]
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k hk hk'
    have hnk : n<k+1 := by simp only [Finset.mem_range] at hk'; omega
    simp only [PowerSeries.coeff_C_mul,
      coeff_pow_vanish _ h0 (k+1) n hnk, mul_zero]
  rw [hext]
  simp only [truncLog, map_sum, PowerSeries.coeff_C_mul, coeff_finitePower]
  rw [Finset.sum_range_succ']
  simp only [ite_true, add_zero, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, ite_false, Nat.add_assoc, Nat.cast_add, Nat.cast_one]


/-- The same finite coefficient formula as `literalLog`, without its source arguments. -/
def finiteLog (q : ℚ →+* R) (f : ℕ → R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range (n+1), if k=0 then 0 else
    q (((-1 : ℚ)^(k+1))/(k : ℚ))*finitePower (augment f) k n

/-- Coefficientwise chain rule for the literal finite power-sum logarithm. -/
theorem finite_log_chain (d : R →+ R) (hd : ∀ a b, d (a*b)=d a*b+a*d b)
    (h1 : d 1=0) (q : ℚ →+* R) (hq : ∀ r, d (q r)=0)
    (f : ℕ → R) (hf : f 0=1) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), f j*d (finiteLog q f (n-j)))=d (f n) := by
  let a := PowerSeries.mk (augment f)
  have ha : PowerSeries.coeff 0 a=0 := by simp [a, augment]
  have he : PowerSeries.mk f=1+a := by
    ext j
    by_cases hj : j=0 <;> simp [a, augment, hj, hf]
  have hone : liftD d (1 : PowerSeries R)=0 := by
    rw [← map_one (PowerSeries.C : R →+* PowerSeries R), liftD_C, h1, map_zero]
  have hda : liftD d a=liftD d (PowerSeries.mk f) := by rw [he, map_add, hone, zero_add]
  have hz : PowerSeries.coeff n (liftD d a*(-a)^(n+1))=0 := by
    rw [coeff_mul_range]
    apply Finset.sum_eq_zero
    intro j hj
    have hneg : PowerSeries.coeff 0 (-a)=0 := by rw [map_neg, ha, neg_zero]
    rw [coeff_pow_vanish (-a) hneg (n+1) (n-j) (by omega), mul_zero]
  have hc := congrArg (PowerSeries.coeff n) (truncated_chain d hd h1 q hq a (n+1))
  rw [← he, mul_sub, mul_one, map_sub, hz, sub_zero, hda, coeff_liftD,
    PowerSeries.coeff_mk, coeff_mul_range] at hc
  convert hc using 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [PowerSeries.coeff_mk, coeff_liftD, coeff_truncLog q f (n+1) (n-j) (by omega)]
  rfl


/-- Cancellation uses only the constant coefficient, by coefficient induction. -/
theorem cancel_zero (f g : PowerSeries R) (hf : PowerSeries.coeff 0 f=1)
    (hfg : f*g=0) : g=0 := by
  ext n
  simp only [map_zero]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hc := congrArg (PowerSeries.coeff n) hfg
    rw [mul_comm, coeff_mul_range, Finset.sum_range_succ] at hc
    have hs : (∑ j ∈ Finset.range n,
        PowerSeries.coeff j g*PowerSeries.coeff (n-j) f)=0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [ih j (Finset.mem_range.mp hj), zero_mul]
    simpa only [hs, zero_add, Nat.sub_self, hf, mul_one, map_zero] using hc

theorem cancel_left (f g h : PowerSeries R) (hf : PowerSeries.coeff 0 f=1)
    (he : f*g=f*h) : g=h := by
  apply sub_eq_zero.mp
  apply cancel_zero f (g-h) hf
  rw [mul_sub, he, sub_self]

end JacobiShifted.SourceBridge.FiniteChain
