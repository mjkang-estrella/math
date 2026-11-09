import MidpointRational
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace JacobiShifted.MidpointRational
open Polynomial

/-- The scalar localization used here is exactly odd reduced denominator. -/
def TwoLocal (a : ℚ) : Prop := Odd a.den

theorem twoLocal_iff_odd_den (a : ℚ) : TwoLocal a ↔ Odd a.den := Iff.rfl

@[simp] theorem twoLocal_zero : TwoLocal 0 := by simp [TwoLocal]
@[simp] theorem twoLocal_int (a : ℤ) : TwoLocal (a : ℚ) := by simp [TwoLocal]
@[simp] theorem twoLocal_nat (a : ℕ) : TwoLocal (a : ℚ) := by simp [TwoLocal]
theorem twoLocal_add {a b : ℚ} (ha : TwoLocal a) (hb : TwoLocal b) : TwoLocal (a+b) :=
  (ha.mul hb).of_dvd_nat (Rat.add_den_dvd a b)
theorem twoLocal_mul {a b : ℚ} (ha : TwoLocal a) (hb : TwoLocal b) : TwoLocal (a*b) :=
  (ha.mul hb).of_dvd_nat (Rat.mul_den_dvd a b)
theorem twoLocal_neg {a : ℚ} (ha : TwoLocal a) : TwoLocal (-a) := by
  simpa only [TwoLocal, Rat.neg_den] using ha
theorem twoLocal_sub {a b : ℚ} (ha : TwoLocal a) (hb : TwoLocal b) : TwoLocal (a-b) :=
  by simpa only [sub_eq_add_neg] using twoLocal_add ha (twoLocal_neg hb)

theorem twoLocal_div_odd_nat {a : ℚ} (ha : TwoLocal a) (d : ℕ) (hd : Odd d) :
    TwoLocal (a / (d : ℚ)) := by
  have hden : (1 / (d : ℚ)).den ∣ d := by
    have h : (((1 : ℚ)/(d : ℚ)).den : ℤ) ∣ (d : ℤ) := by
      simpa only [Rat.divInt_eq_div, Int.cast_one, Int.cast_natCast] using Rat.den_dvd 1 (d : ℤ)
    exact Int.natCast_dvd_natCast.mp h
  simpa only [div_eq_mul_inv, one_mul] using twoLocal_mul ha (hd.of_dvd_nat hden)

/-- Polynomials of degree strictly less than `N`, including zero. -/
def Bounded (N : ℕ) (f : QPoly) : Prop := ∀ k : ℕ, N ≤ k → f.coeff k=0

theorem bounded_self (f : QPoly) : Bounded (f.natDegree+1) f := by
  intro k hk
  exact coeff_eq_zero_of_natDegree_lt (by omega)
theorem bounded_zero (N : ℕ) : Bounded N 0 := by intro k _; simp
theorem bounded_mono {N M : ℕ} {f : QPoly} (h : Bounded N f) (hNM : N ≤ M) :
    Bounded M f := fun k hk => h k (hNM.trans hk)
theorem bounded_add {N : ℕ} {f g : QPoly} (hf : Bounded N f) (hg : Bounded N g) :
    Bounded N (f+g) := by intro k hk; simp [hf k hk, hg k hk]
theorem bounded_sub {N : ℕ} {f g : QPoly} (hf : Bounded N f) (hg : Bounded N g) :
    Bounded N (f-g) := by intro k hk; simp [hf k hk, hg k hk]
theorem bounded_term (n : ℕ) (c : ℚ) : Bounded (n+1) (Polynomial.C c * X^n) := by
  intro k hk
  simp [show k ≠ n by omega]

/-- The actual finite-degree submodule. -/
def finiteDegree (N : ℕ) : Submodule ℚ QPoly where
  carrier := {f | Bounded N f}
  zero_mem' := bounded_zero N
  add_mem' := bounded_add
  smul_mem' a f hf := by intro k hk; simp [hf k hk]

/-- The odd-unit triangular polynomial differential operator. -/
def T (f : QPoly) : QPoly := f + 2*(1+X)*derivative f

@[simp] theorem T_zero : T 0 = 0 := by simp [T]
theorem T_add (f g : QPoly) : T (f+g) = T f + T g := by
  simp [T, derivative_add]; ring
theorem T_sub (f g : QPoly) : T (f-g) = T f - T g := by
  simp [T, derivative_sub]; ring
theorem T_smul (a : ℚ) (f : QPoly) : T (a • f) = a • T f := by
  simp [T, smul_eq_C_mul, derivative_mul]; ring

theorem coeff_X_derivative (f : QPoly) (k : ℕ) :
    (X*derivative f).coeff k = (k : ℚ)*f.coeff k := by
  cases k with
  | zero => simp
  | succ k => simp [coeff_derivative]; ring

theorem T_coeff (f : QPoly) (k : ℕ) :
    (T f).coeff k = (2*(k : ℚ)+1)*f.coeff k + 2*((k : ℚ)+1)*f.coeff (k+1) := by
  have ht : T f = f + Polynomial.C 2 * derivative f +
      Polynomial.C 2 * (X * derivative f) := by simp [T, Polynomial.C_ofNat]; ring
  rw [ht]
  simp only [coeff_add, coeff_C_mul, coeff_derivative, coeff_X_derivative]
  ring

theorem T_bounded {N : ℕ} {f : QPoly} (hf : Bounded N f) : Bounded N (T f) := by
  intro k hk
  rw [T_coeff, hf k hk, hf (k+1) (by omega)]
  ring

/-- Eliminate the highest coefficient and reconstruct a genuine polynomial. -/
theorem T_surjective_bounded (N : ℕ) (B : QPoly) (hB : Bounded N B) :
    ∃ f : QPoly, Bounded N f ∧ T f = B := by
  induction N generalizing B with
  | zero =>
    have hb : B=0 := by ext k; exact hB k (Nat.zero_le _)
    exact ⟨0, bounded_zero _, by simp [hb]⟩
  | succ N ih =>
    let c : ℚ := B.coeff N / (2*(N : ℚ)+1)
    let m : QPoly := Polynomial.C c * X^N
    have hd : (2*(N : ℚ)+1) ≠ 0 := by positivity
    have hm : Bounded (N+1) m := bounded_term N c
    have htop : (T m).coeff N = B.coeff N := by
      rw [T_coeff]
      simp only [m, coeff_C_mul_X_pow, ite_true, show N+1 ≠ N by omega, ite_false,
        mul_zero, add_zero]
      dsimp [c]
      exact mul_div_cancel₀ _ hd
    have hD : Bounded N (B-T m) := by
      intro k hk
      rcases eq_or_lt_of_le hk with rfl | hk
      · simp [htop]
      · exact bounded_sub hB (T_bounded hm) k (by omega)
    obtain ⟨f,hf,he⟩ := ih (B-T m) hD
    refine ⟨f+m, bounded_add (bounded_mono hf (by omega)) hm, ?_⟩
    rw [T_add, he]
    ring

/-- Zero-kernel proof uses the nonzero top diagonal, and includes constants. -/
theorem T_kernel {f : QPoly} (hf : T f=0) : f=0 := by
  by_contra hn
  have hc := congrArg (fun p : QPoly => p.coeff f.natDegree) hf
  have hz : f.coeff (f.natDegree+1)=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [T_coeff, coeff_zero, hz, mul_zero, add_zero] at hc
  have hd : (2*(f.natDegree : ℚ)+1) ≠ 0 := by positivity
  exact (leadingCoeff_ne_zero.mpr hn) ((mul_eq_zero.mp hc).resolve_left hd)

theorem T_injective : Function.Injective T := by
  intro f g h
  have hz : T (f-g)=0 := by rw [T_sub, h]; ring
  exact sub_eq_zero.mp (T_kernel hz)

theorem T_bijective : Function.Bijective T :=
  ⟨T_injective, fun B => let ⟨f,_,hf⟩ := T_surjective_bounded _ B (bounded_self B); ⟨f,hf⟩⟩

/-- The inverse is selected only after proving actual polynomial existence. -/
def inverseT (B : QPoly) : QPoly := Classical.choose (T_bijective.2 B)
@[simp] theorem T_inverseT (B : QPoly) : T (inverseT B)=B := Classical.choose_spec (T_bijective.2 B)
@[simp] theorem inverseT_T (f : QPoly) : inverseT (T f)=f := T_injective (T_inverseT (T f))
theorem inverseT_unique {f B : QPoly} (h : T f=B) : f=inverseT B :=
  T_injective (h.trans (T_inverseT B).symm)
@[simp] theorem inverseT_zero : inverseT 0=0 := T_injective (by simp)
theorem inverseT_add (A B : QPoly) : inverseT (A+B)=inverseT A+inverseT B := by
  apply T_injective
  simp [T_add]
theorem inverseT_smul (a : ℚ) (B : QPoly) : inverseT (a • B)=a • inverseT B := by
  apply T_injective
  simp [T_smul]

theorem inverseT_bounded {N : ℕ} {B : QPoly} (hB : Bounded N B) : Bounded N (inverseT B) := by
  obtain ⟨f,hf,he⟩ := T_surjective_bounded N B hB
  rwa [inverseT_unique he] at hf

theorem T_finiteDegree_bijective (N : ℕ) :
    Function.Bijective (fun f : finiteDegree N => (⟨T f, T_bounded f.property⟩ : finiteDegree N)) := by
  constructor
  · intro a b h
    apply Subtype.ext
    exact T_injective (congrArg Subtype.val h)
  · intro B
    obtain ⟨f,hf,he⟩ := T_surjective_bounded N B B.property
    exact ⟨⟨f,hf⟩, Subtype.ext he⟩

/-- Every fixed power of two survives triangular inversion over the localization.
The argument descends through all coefficients of a finite polynomial. -/
theorem T_twoLocal {f B : QPoly} (e : ℕ) (he : T f=B)
    (hB : ∀ k : ℕ, TwoLocal (B.coeff k / (2 : ℚ)^e)) :
    ∀ k : ℕ, TwoLocal (f.coeff k / (2 : ℚ)^e) := by
  let N := f.natDegree+1
  have hf : Bounded N f := bounded_self f
  have hd (k : ℕ) : (2*(k : ℚ)+1) ≠ 0 := by positivity
  have down : ∀ k : ℕ, k ≤ N → TwoLocal (f.coeff k / (2 : ℚ)^e) := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self => simp [hf N (le_refl _)]
    | of_succ k hk ih =>
      have hc := congrArg (fun p : QPoly => p.coeff k) he
      rw [T_coeff] at hc
      have solve : f.coeff k / (2 : ℚ)^e =
          (B.coeff k / (2 : ℚ)^e - (2*((k : ℚ)+1))*(f.coeff (k+1)/(2 : ℚ)^e)) /
            ((2*k+1 : ℕ) : ℚ) := by
        push_cast
        field_simp
        linear_combination hc
      rw [solve]
      apply twoLocal_div_odd_nat
      · apply twoLocal_sub (hB k)
        apply twoLocal_mul _ ih
        simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using twoLocal_nat (2*(k+1))
      · exact ⟨k, rfl⟩
  intro k
  by_cases hk : k ≤ N
  · exact down k hk
  · simp [hf k (by omega)]

theorem inverseT_twoLocal (B : QPoly) (e : ℕ)
    (hB : ∀ k : ℕ, TwoLocal (B.coeff k / (2 : ℚ)^e)) :
    ∀ k : ℕ, TwoLocal ((inverseT B).coeff k / (2 : ℚ)^e) :=
  T_twoLocal e (T_inverseT B) hB

end JacobiShifted.MidpointRational
