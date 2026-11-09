import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Nth

set_option autoImplicit false
set_option warningAsError true

namespace InversePeriodDoubling

def d (n : ℕ) : ZMod 2 := (padicValNat 2 (n + 1) : ZMod 2)

theorem d_even (n : ℕ) : d (2 * n) = 0 := by
  have h : ¬ 2 ∣ 2 * n + 1 := by omega
  have hv : padicValNat 2 (2 * n + 1) = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr h))
  simp [d, hv]

theorem d_odd (n : ℕ) : d (2 * n + 1) = d n + 1 := by
  have h : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
  simp only [d, h, padicValNat_base_mul (by decide : 1 < 2) (by omega : n + 1 ≠ 0),
    Nat.cast_add, Nat.cast_one]
noncomputable def D : PowerSeries (ZMod 2) := PowerSeries.mk d

theorem D_constant : D.constantCoeff = 0 := by
  simp [D, d, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem D_linear : D.coeff 1 = 1 := by
  simp [D, d]

theorem D_linear_unit : IsUnit (D.coeff 1) := by rw [D_linear]; exact isUnit_one

noncomputable def U : PowerSeries (ZMod 2) := D.substInvOfIsUnit D_linear_unit
noncomputable def u (n : ℕ) : ZMod 2 := U.coeff n

theorem D_subst_U : D.subst U = PowerSeries.X :=
  PowerSeries.subst_substInvOfIsUnit_right D D_constant D_linear_unit

theorem U_subst_D : U.subst D = PowerSeries.X :=
  PowerSeries.subst_substInvOfIsUnit_left D D_constant D_linear_unit

theorem u_zero : u 0 = 0 := by
  simp [u, U, PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem u_one : u 1 = 1 := by
  simp only [u, U, PowerSeries.coeff_one_substInvOfIsUnit]
  have h : D_linear_unit.unit = 1 := by
    apply Units.ext
    simpa using D_linear
  rw [h]
  rfl

theorem U_unique (Q : PowerSeries (ZMod 2)) (hQ : PowerSeries.HasSubst Q)
    (h : D.subst Q = PowerSeries.X) : Q = U :=
  PowerSeries.eq_substInvOfIsUnit_of_subst_eq_X D D_constant D_linear_unit hQ h

noncomputable def b : ℕ → ℕ := Nat.nth (fun n => u n = 0)
noncomputable def a : ℕ → ℕ := Nat.nth (fun n => u n = 1)
noncomputable def g (n : ℕ) : ℕ := b (n + 1) - b n
noncomputable def c (j : ℕ) : ℕ := a j - j - 1

theorem b_zero : b 0 = 0 := Nat.nth_zero_of_zero u_zero

-- These are literal source endpoints, not certificates of their truth.
def ScalarRecurrence : Prop :=
  (∀ n, u (2 * n) = 0) ∧
  (∀ n, 1 ≤ n → u (4 * n + 1) = u (2 * n - 1)) ∧
  (∀ n, u (4 * n + 3) = u n)

def EnumerationEndpoint : Prop :=
  Set.Infinite {n | u n = 0} ∧ Set.Infinite {n | u n = 1} ∧
  StrictMono b ∧ StrictMono a ∧ StrictMono c ∧
  (∀ n, g n = 1 ∨ g n = 2) ∧
  (∀ n, g n = 2 ↔ ∃ j, n = c j)

end InversePeriodDoubling
