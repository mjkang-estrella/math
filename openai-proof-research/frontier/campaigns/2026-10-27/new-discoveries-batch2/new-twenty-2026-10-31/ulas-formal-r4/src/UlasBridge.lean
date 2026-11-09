import UlasFinal3
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.LinearCombination
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
open PowerSeries
namespace Ulas.Round4
noncomputable def y : PowerSeries ℤ := X * geomStep 1
noncomputable def ev : Polynomial ℤ →+* PowerSeries ℤ :=
  Polynomial.eval₂RingHom PowerSeries.C y
@[simp] theorem ev_X : ev Polynomial.X = y := by simp [ev]
@[simp] theorem ev_C (a : ℤ) : ev (Polynomial.C a) = PowerSeries.C a := by simp [ev]
theorem one_add_y : 1 + y = geomStep 1 := by
  ext n
  cases n with
  | zero => simp [y, geomStep, coeff_mul]
  | succ n => simp [y, geomStep, coeff_succ_X_mul]
theorem X_one_add_y : X * (1+y) = y := by rw [one_add_y]; rfl
theorem y_split : y = expand 2 (by decide) y +
    X * expand 2 (by decide) (1+y) := by
  rw [one_add_y, y, map_mul, expand_X, geom_expand]
  rw [geom_split]
  ring
theorem w_y : w = 1+2*y := by
  rw [w, ← one_add_y]
  have h := X_one_add_y
  linear_combination h
/-- Simultaneous parity sections; the odd section has a factor 1+y. -/
def Represents (f : PowerSeries ℤ) (a b : Polynomial ℤ) : Prop :=
  f = expand 2 (by decide) (ev a) +
    X * expand 2 (by decide) ((1+y)*ev b)
theorem represents_one : Represents 1 1 0 := by simp [Represents]
theorem represents_mul_y {f : PowerSeries ℤ} {a b : Polynomial ℤ}
    (hf : Represents f a b) :
    Represents (y*f)
      (Polynomial.X*a + Polynomial.X*(1+Polynomial.X)*b)
      (a+Polynomial.X*b) := by
  unfold Represents at *
  rw [hf]
  conv_lhs => lhs; rw [y_split]
  simp only [map_add, map_mul, map_one, ev_X]
  have h := X_one_add_y
  have hx : (X : PowerSeries ℤ)^2 = expand 2 (by decide) X := by simp [expand_X]
  calc
    _ = expand 2 (by decide) (y*ev a) +
        expand 2 (by decide) X * expand 2 (by decide) ((1+y)^2*ev b) +
        X * expand 2 (by decide) ((1+y)*(ev a+y*ev b)) := by
          rw [← hx]
          simp only [map_add, map_mul, map_pow, map_one]
          ring
    _ = _ := by
      rw [← map_mul]
      have hh : X*((1+y)^2*ev b) = y*(1+y)*ev b := by
        calc
          _ = (X*(1+y))*(1+y)*ev b := by ring
          _ = _ := by rw [h]
      rw [hh]
      simp only [map_add, map_mul, map_one]
noncomputable def parityPair : ℕ → Polynomial ℤ × Polynomial ℤ
  | 0 => (1,0)
  | E+1 => let p := parityPair E
    (Polynomial.X*p.1 + Polynomial.X*(1+Polynomial.X)*p.2,
      p.1+Polynomial.X*p.2)
theorem parityPair_correct (E : ℕ) :
    Represents (y^E) (parityPair E).1 (parityPair E).2 := by
  induction E with
  | zero => simpa [parityPair] using represents_one
  | succ E ih => simpa [parityPair, pow_succ, mul_comm] using represents_mul_y ih
noncomputable def polyEven (F : Polynomial ℤ) : Polynomial ℤ :=
  ∑ E ∈ F.support, Polynomial.C (F.coeff E) * (parityPair E).1
@[simp] theorem sectionEven_C_mul (a : ℤ) (f : PowerSeries ℤ) :
    sectionEven (PowerSeries.C a * f) = PowerSeries.C a * sectionEven f := by
  ext n
  simp [coeff_C_mul]
@[simp] theorem sectionEven_sum {α : Type*} (s : Finset α) (f : α → PowerSeries ℤ) :
    sectionEven (∑ a ∈ s, f a) = ∑ a ∈ s, sectionEven (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext n; simp [sectionEven]
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]
theorem sectionEven_parityPair (E : ℕ) :
    sectionEven (y^E) = ev (parityPair E).1 := by
  rw [parityPair_correct E, sectionEven_add, sectionEven_expand,
    sectionEven_X_expand, add_zero]
theorem ev_eq_sum (F : Polynomial ℤ) :
    ev F = ∑ E ∈ F.support, PowerSeries.C (F.coeff E)*y^E := by
  exact Polynomial.eval₂_eq_sum
/-- Polynomial-to-series even-section bridge, without degree restrictions. -/
theorem sectionEven_ev (F : Polynomial ℤ) :
    sectionEven (ev F) = ev (polyEven F) := by
  rw [ev_eq_sum, sectionEven_sum]
  simp only [sectionEven_C_mul, sectionEven_parityPair]
  simp [polyEven]
noncomputable def polyTransfer (m : ℕ) (F : Polynomial ℤ) : Polynomial ℤ :=
  polyEven ((1+2*Polynomial.X)^m*F)
theorem sectionEven_C_ev (m : ℕ) (F : Polynomial ℤ) :
    sectionEven (C^m*ev F) = C^m*ev (polyTransfer m F) := by
  rw [sectionEven_C_pow_mul]
  have h : w^m*ev F = ev ((1+2*Polynomial.X)^m*F) := by
    simp only [map_mul, map_pow, map_add, map_one, map_ofNat, ev_X, w_y]
  rw [h, sectionEven_ev]
  rfl

theorem represents_add {f g : PowerSeries ℤ} {a b c d : Polynomial ℤ}
    (hf : Represents f a b) (hg : Represents g c d) :
    Represents (f+g) (a+c) (b+d) := by
  unfold Represents at *
  rw [hf, hg]
  simp only [map_add, mul_add]
  ring

theorem represents_C_mul (z : ℤ) {f : PowerSeries ℤ} {a b : Polynomial ℤ}
    (hf : Represents f a b) :
    Represents (PowerSeries.C z*f) (Polynomial.C z*a) (Polynomial.C z*b) := by
  unfold Represents at *
  rw [hf]
  simp only [map_mul, ev_C]
  have hz : expand 2 (by decide) (PowerSeries.C z) = PowerSeries.C z := by simp
  rw [hz]
  ring

theorem represents_mul_w {f : PowerSeries ℤ} {a b : Polynomial ℤ}
    (hf : Represents f a b) :
    Represents (w*f)
      ((1+2*Polynomial.X)*a+2*Polynomial.X*(1+Polynomial.X)*b)
      (2*a+(1+2*Polynomial.X)*b) := by
  have h := represents_add hf (represents_C_mul 2 (represents_mul_y hf))
  have ha : a+Polynomial.C 2*(Polynomial.X*a+Polynomial.X*(1+Polynomial.X)*b) =
      (1+2*Polynomial.X)*a+2*Polynomial.X*(1+Polynomial.X)*b := by norm_num; ring
  have hb : b+Polynomial.C 2*(a+Polynomial.X*b) =
      2*a+(1+2*Polynomial.X)*b := by norm_num; ring
  rw [ha, hb] at h
  convert h using 1 <;> simp only [w_y, map_ofNat] <;> ring

/-- The two reduced parity numerators. Multiplication by y and w remains integral. -/
noncomputable def reducedPair : ℕ → ℕ → Polynomial ℤ × Polynomial ℤ
  | 0, 0 => (2,1+2*Polynomial.X)
  | 0, E+1 => let p := reducedPair 0 E
    (Polynomial.X*p.1+p.2, Polynomial.X*(1+Polynomial.X)*p.1+Polynomial.X*p.2)
  | m+1, E => let p := reducedPair m E
    ((1+2*Polynomial.X)*p.1+2*p.2,
      2*Polynomial.X*(1+Polynomial.X)*p.1+(1+2*Polynomial.X)*p.2)

theorem reducedPair_correct (m E : ℕ) :
    Represents (w^m*(y*(1+y)*y^E))
      (Polynomial.X*(1+Polynomial.X)*(reducedPair m E).1)
      (reducedPair m E).2 := by
  induction m with
  | zero =>
    induction E with
    | zero =>
      have h1 := represents_mul_y represents_one
      have h2 := represents_mul_y h1
      have h := represents_add h1 h2
      convert h using 1 <;> simp [reducedPair] <;> ring
    | succ E ih =>
      have h := represents_mul_y ih
      convert h using 1 <;> simp [reducedPair, pow_succ] <;> ring
  | succ m ih =>
    have h := represents_mul_w ih
    convert h using 1 <;> simp [reducedPair, pow_succ] <;> ring

noncomputable def recursiveReduced (m : ℕ) (R : Polynomial ℤ) : Polynomial ℤ :=
  ∑ E ∈ R.support, Polynomial.C (R.coeff E)*(reducedPair m E).1

theorem sectionEven_reduced_monomial (m E : ℕ) :
    sectionEven (w^m*(y*(1+y)*y^E)) = y*(1+y)*ev (reducedPair m E).1 := by
  rw [reducedPair_correct, sectionEven_add, sectionEven_expand,
    sectionEven_X_expand, add_zero]
  simp

/-- The reduced series bridge for a recursive, integral polynomial operator. -/
theorem sectionEven_recursiveReduced (m : ℕ) (R : Polynomial ℤ) :
    sectionEven (w^m*(y*(1+y)*ev R)) = y*(1+y)*ev (recursiveReduced m R) := by
  rw [ev_eq_sum]
  simp only [Finset.mul_sum]
  have h (E : ℕ) : w^m*(y*(1+y)*(PowerSeries.C (R.coeff E)*y^E)) =
      PowerSeries.C (R.coeff E)*(w^m*(y*(1+y)*y^E)) := by ring
  simp only [h, sectionEven_sum, sectionEven_C_mul, sectionEven_reduced_monomial]
  simp only [recursiveReduced, map_sum, map_mul, ev_C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E _
  ring

/-- This is the remaining purely polynomial identity, not an assumption hidden
in the preceding series bridge. -/
def BinomialIdentification : Prop :=
  ∀ m R, recursiveReduced m R = Round3.reduced m R

theorem lemma_R (h : BinomialIdentification) (m : ℕ) (R : Polynomial ℤ) :
    sectionEven (w^m*(y*(1+y)*ev R)) = y*(1+y)*ev (Round3.reduced m R) := by
  rw [sectionEven_recursiveReduced, h]
end Ulas.Round4
