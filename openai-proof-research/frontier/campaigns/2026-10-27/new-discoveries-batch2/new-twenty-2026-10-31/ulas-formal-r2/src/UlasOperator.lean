import UlasSeries
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic.Ring

open PowerSeries
namespace Ulas
noncomputable def w : PowerSeries ℤ := (1 + X) * geomStep 1

theorem geom_expand (k : ℕ) : expand 2 (by decide) (geomStep k) = geomStep (2*k) := by
  ext n
  rw [coeff_expand]
  simp only [geomStep, coeff_mk]
  by_cases h : 2 ∣ n
  · obtain ⟨a, rfl⟩ := h
    simp [Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)]
  · have hh : ¬ 2*k ∣ n := fun hh => h (dvd_trans (dvd_mul_right 2 k) hh)
    simp [h, hh]

theorem geom_split : geomStep 1 = (1 + X) * geomStep 2 := by
  ext n
  cases n with
  | zero => simp [geomStep, coeff_mul]
  | succ n =>
    simp only [add_mul, one_mul, map_add, coeff_succ_X_mul, geomStep, coeff_mk]
    have h : (2 ∣ n+1) ↔ ¬ 2 ∣ n := by omega
    simp only [one_dvd, ite_true, h]
    by_cases h : 2 ∣ n <;> simp [h]

theorem G_expand (N : ℕ) : G (N+1) = w * expand 2 (by decide) (G N) := by
  simp only [G, map_mul, map_prod, geom_expand, Finset.prod_range_succ', pow_zero,
    pow_succ]
  simp only [w, geom_split]
  ring

theorem agree_expand {n : ℕ} {f g : PowerSeries ℤ} (h : Agree n f g) :
    Agree n (expand 2 (by decide) f) (expand 2 (by decide) g) := by
  intro i hi
  rw [coeff_expand, coeff_expand]
  split_ifs
  · exact h _ (le_trans (Nat.div_le_self _ _) hi)
  · rfl

/-- The faithful infinite product satisfies F1. -/
theorem C_functional : C = w * expand 2 (by decide) C := by
  ext n
  have h := agree_mul (show Agree n w w from fun _ _ => rfl)
    (agree_expand (C_agree n (n+1) le_rfl))
  rw [h n le_rfl, ← G_expand]
  exact C_agree n (n+2) (by omega) n le_rfl

/-- The m-colour functional identity needed by the even-section operator. -/
theorem C_pow_functional (m : ℕ) :
    C^m = w^m * expand 2 (by decide) (C^m) := by
  conv_lhs => rw [C_functional]
  rw [mul_pow, map_pow]
/-- The coefficient-level even section; no division by two is used. -/
noncomputable def sectionEven (f : PowerSeries ℤ) : PowerSeries ℤ :=
  mk fun n => coeff (2*n) f
noncomputable def sectionOdd (f : PowerSeries ℤ) : PowerSeries ℤ :=
  mk fun n => coeff (2*n+1) f

@[simp] theorem coeff_sectionEven (f : PowerSeries ℤ) (n : ℕ) :
    coeff n (sectionEven f) = coeff (2*n) f := coeff_mk _ _

@[simp] theorem sectionEven_add (f g : PowerSeries ℤ) :
    sectionEven (f+g) = sectionEven f + sectionEven g := by
  ext n
  simp

@[simp] theorem sectionEven_sub (f g : PowerSeries ℤ) :
    sectionEven (f-g) = sectionEven f - sectionEven g := by
  ext n
  simp

@[simp] theorem sectionEven_expand (f : PowerSeries ℤ) :
    sectionEven (expand 2 (by decide) f) = f := by
  ext n
  simp

@[simp] theorem sectionEven_X_expand (f : PowerSeries ℤ) :
    sectionEven (X * expand 2 (by decide) f) = 0 := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_sectionEven, show 2*(n+1) = (2*n+1)+1 by omega, coeff_succ_X_mul]
    rw [coeff_expand_of_not_dvd 2 (by decide) f (by omega)]
    simp

theorem even_odd_decomposition (f : PowerSeries ℤ) :
    f = expand 2 (by decide) (sectionEven f) +
      X * expand 2 (by decide) (sectionOdd f) := by
  ext n
  cases n with
  | zero =>
    simp only [map_add, coeff_zero_X_mul, add_zero, constantCoeff_expand,
      coeff_zero_eq_constantCoeff]
    simp only [← coeff_zero_eq_constantCoeff, coeff_sectionEven, mul_zero]
  | succ n =>
    simp only [map_add, coeff_succ_X_mul, coeff_expand]
    by_cases hn : 2 ∣ n
    · have hn' : ¬ 2 ∣ n+1 := by omega
      simp only [hn, hn', ite_true, ite_false, zero_add, sectionOdd, coeff_mk]
      exact congrArg (fun i => coeff i f) (by omega)
    · have hn' : 2 ∣ n+1 := by omega
      simp only [hn, hn', ite_true, ite_false, add_zero, coeff_sectionEven]
      exact congrArg (fun i => coeff i f) (by omega)

/-- F2's general even-section convolution rule. -/
theorem sectionEven_mul_expand (f g : PowerSeries ℤ) :
    sectionEven (f * expand 2 (by decide) g) = sectionEven f * g := by
  conv_lhs => rw [even_odd_decomposition f]
  rw [add_mul, ← map_mul, mul_assoc, ← map_mul, sectionEven_add,
    sectionEven_expand, sectionEven_X_expand, add_zero]

/-- The operator identity before changing to the polynomial y-basis. -/
theorem sectionEven_C_pow_mul (m : ℕ) (f : PowerSeries ℤ) :
    sectionEven (C^m * f) = C^m * sectionEven (w^m * f) := by
  conv_lhs => rw [C_pow_functional]
  rw [show w^m * expand 2 (by decide) (C^m) * f =
    (w^m*f) * expand 2 (by decide) (C^m) by ring,
    sectionEven_mul_expand, mul_comm]
/-- Iterated transfer on the full integer series ring. -/
noncomputable def transferIter (m : ℕ) : ℕ → PowerSeries ℤ
  | 0 => 1
  | j+1 => sectionEven (w^m * transferIter m j)

/-- The general-j coefficient identity, before the reduced basis. -/
theorem c_transfer (m j n : ℕ) :
    c m (2^j*n) = coeff n (C^m * transferIter m j) := by
  induction j generalizing n with
  | zero => simp [c, transferIter]
  | succ j ih =>
    rw [show 2^(j+1)*n = 2^j*(2*n) by ring, ih]
    rw [← coeff_sectionEven, sectionEven_C_pow_mul]
    rfl
end Ulas
