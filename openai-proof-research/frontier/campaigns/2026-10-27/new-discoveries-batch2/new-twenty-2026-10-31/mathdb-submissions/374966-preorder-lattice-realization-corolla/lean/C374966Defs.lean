import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fin.VecNotation

/-!
# MathDB 374966 — shared definitions

Athanasiadis–Chapoton, arXiv:2605.26916v1, Section 8:
`M_P(x,y) = ∑_{a ⪯ b} μ_P(a,b) x^{ρ a} y^{ρ b}` and the transmutation
`f̄(x,y) = f((1-y)/(1-xy), 1-xy)`.  Here `x = X 0`, `y = X 1`, coefficients in `ℚ`,
and `μ` is Mathlib's `IncidenceAlgebra.mu`.
-/

namespace C374966

open Finset MvPolynomial

/-- The polynomial ring `ℚ[x,y]`. -/
abbrev Pxy := MvPolynomial (Fin 2) ℚ

/-- The rational function field `ℚ(x,y)`. -/
abbrev FracXY := FractionRing Pxy

/-- The image of `x` in `ℚ(x,y)`. -/
notation "xF" => algebraMap C374966.Pxy C374966.FracXY (MvPolynomial.X 0)
/-- The image of `y` in `ℚ(x,y)`. -/
notation "yF" => algebraMap C374966.Pxy C374966.FracXY (MvPolynomial.X 1)

/-- Exponent vector of `x^i y^j`. -/
noncomputable abbrev mon (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

theorem mon_inj {i j i' j' : ℕ} : mon i j = mon i' j' ↔ i = i' ∧ j = j' := by
  constructor
  · intro h
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    simp [mon] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem CXX (c : ℚ) (i j : ℕ) :
    (C c * X 0 ^ i * X 1 ^ j : Pxy) = monomial (mon i j) c := by
  rw [mul_assoc, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul,
    C_mul_monomial, mul_one]

/-- The M-triangle `M_P(x,y) = ∑_{a ≤ b} μ(a,b) x^{ρ a} y^{ρ b}` of a finite poset with rank map `ρ`. -/
noncomputable def Mtri (α : Type*) [PartialOrder α] [Fintype α] [LocallyFiniteOrder α]
    [DecidableEq α] [DecidableLE α] (ρ : α → ℕ) : Pxy :=
  ∑ a : α, ∑ b ∈ univ.filter (fun b => a ≤ b),
    C (IncidenceAlgebra.mu ℚ a b) * X 0 ^ ρ a * X 1 ^ ρ b

/-- Coefficient table of `Mtri`: `Tab α ρ i j = ∑_{a ≤ b, ρ a = i, ρ b = j} μ(a,b)`. -/
noncomputable def Tab (α : Type*) [PartialOrder α] [Fintype α] [LocallyFiniteOrder α]
    [DecidableEq α] [DecidableLE α] (ρ : α → ℕ) (i j : ℕ) : ℚ :=
  ∑ a : α, ∑ b : α, if ρ a = i ∧ ρ b = j then
    (if a ≤ b then IncidenceAlgebra.mu ℚ a b else 0) else 0

theorem Mtri_eq (α : Type*) [PartialOrder α] [Fintype α] [LocallyFiniteOrder α]
    [DecidableEq α] [DecidableLE α] (ρ : α → ℕ) :
    Mtri α ρ = ∑ a : α, ∑ b : α,
      C (if a ≤ b then IncidenceAlgebra.mu ℚ a b else 0) * X 0 ^ ρ a * X 1 ^ ρ b := by
  unfold Mtri
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a ≤ b
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, map_zero, zero_mul, zero_mul]

/-- `[x^i y^j] M_P = Tab α ρ i j`, for every `i j`. -/
theorem coeff_Mtri (α : Type*) [PartialOrder α] [Fintype α] [LocallyFiniteOrder α]
    [DecidableEq α] [DecidableLE α] (ρ : α → ℕ) (i j : ℕ) :
    (Mtri α ρ).coeff (mon i j) = Tab α ρ i j := by
  rw [Mtri_eq, coeff_sum]
  unfold Tab
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coeff_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [CXX, coeff_monomial]
  by_cases h : ρ a = i ∧ ρ b = j
  · rw [ite_eq_left (mon_inj.2 h), ite_eq_left h]
  · rw [ite_eq_right (show ¬ (mon (ρ a) (ρ b) = mon i j) from fun h' => h (mon_inj.1 h')), ite_eq_right h]

/-- A polynomial of bidegree `≤ (3,3)` given by its coefficient table. -/
noncomputable def tab (t : ℕ → ℕ → ℚ) : Pxy :=
  ∑ i ∈ range 4, ∑ j ∈ range 4, C (t i j) * X 0 ^ i * X 1 ^ j

theorem coeff_tab (t : ℕ → ℕ → ℚ) {i j : ℕ} (hi : i < 4) (hj : j < 4) :
    (tab t).coeff (mon i j) = t i j := by
  unfold tab
  rw [coeff_sum, Finset.sum_eq_single_of_mem i (Finset.mem_range.2 hi)]
  · rw [coeff_sum, Finset.sum_eq_single_of_mem j (Finset.mem_range.2 hj)]
    · rw [CXX, coeff_monomial, ite_eq_left rfl]
    · intro j' _ hj'
      rw [CXX, coeff_monomial,
        ite_eq_right (show ¬ (mon i j' = mon i j) from fun h => hj' (mon_inj.1 h).2)]
  · intro i' _ hi'
    rw [coeff_sum]
    refine Finset.sum_eq_zero fun j' _ => ?_
    rw [CXX, coeff_monomial,
      ite_eq_right (show ¬ (mon i' j' = mon i j) from fun h => hi' (mon_inj.1 h).1)]

theorem tab_congr {t t' : ℕ → ℕ → ℚ} (h : ∀ i < 4, ∀ j < 4, t i j = t' i j) :
    tab t = tab t' := by
  unfold tab
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [h i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj)]

theorem sum_swap4 {ι κ M : Type*} [AddCommMonoid M] (s : Finset ι) (t : Finset κ)
    (G : ι → ι → κ → κ → M) :
    ∑ i ∈ s, ∑ j ∈ s, ∑ a ∈ t, ∑ b ∈ t, G i j a b
      = ∑ a ∈ t, ∑ b ∈ t, ∑ i ∈ s, ∑ j ∈ s, G i j a b := by
  calc ∑ i ∈ s, ∑ j ∈ s, ∑ a ∈ t, ∑ b ∈ t, G i j a b
      = ∑ i ∈ s, ∑ a ∈ t, ∑ j ∈ s, ∑ b ∈ t, G i j a b :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a ∈ t, ∑ i ∈ s, ∑ j ∈ s, ∑ b ∈ t, G i j a b := Finset.sum_comm
    _ = ∑ a ∈ t, ∑ i ∈ s, ∑ b ∈ t, ∑ j ∈ s, G i j a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a ∈ t, ∑ b ∈ t, ∑ i ∈ s, ∑ j ∈ s, G i j a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm

/-- Regrouping a double sum of monomials into its coefficient table. -/
theorem regroup {α : Type*} [Fintype α] (ρ : α → ℕ) (hρ : ∀ a, ρ a < 4) (w : α → α → ℚ) :
    tab (fun i j => ∑ a, ∑ b, if ρ a = i ∧ ρ b = j then w a b else 0)
      = ∑ a, ∑ b, C (w a b) * X 0 ^ ρ a * X 1 ^ ρ b := by
  unfold tab
  simp only [map_sum, Finset.sum_mul]
  rw [sum_swap4]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single_of_mem (ρ a) (Finset.mem_range.2 (hρ a))]
  · rw [Finset.sum_eq_single_of_mem (ρ b) (Finset.mem_range.2 (hρ b))]
    · rw [ite_eq_left (show ρ a = ρ a ∧ ρ b = ρ b from ⟨rfl, rfl⟩)]
    · intro j _ hj
      rw [ite_eq_right (show ¬ (ρ a = ρ a ∧ ρ b = j) from fun h => hj h.2.symm),
        map_zero, zero_mul, zero_mul]
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [ite_eq_right (show ¬ (ρ a = i ∧ ρ b = j) from fun h => hi h.1.symm),
      map_zero, zero_mul, zero_mul]

/-- Uniqueness of the Möbius function: a function with `f a a = 1` whose interval sums vanish
agrees with Mathlib's `IncidenceAlgebra.mu` on comparable pairs. -/
theorem mu_eq_of_sum {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]
    (f : α → α → ℚ) (h1 : ∀ a, f a a = 1)
    (h2 : ∀ a b, a < b → ∑ z ∈ Finset.Icc a b, f a z = 0) (a : α) :
    ∀ b, a ≤ b → IncidenceAlgebra.mu ℚ a b = f a b := by
  suffices H : ∀ n : ℕ, ∀ b, (Finset.Ico a b).card = n → a ≤ b →
      IncidenceAlgebra.mu ℚ a b = f a b from fun b hab => H _ b rfl hab
  intro n
  refine Nat.strong_induction_on
    (p := fun n => ∀ b, (Finset.Ico a b).card = n → a ≤ b →
      IncidenceAlgebra.mu ℚ a b = f a b) n ?_
  intro n ih b hn hab
  rcases eq_or_ne a b with rfl | hne
  · rw [IncidenceAlgebra.mu_apply, ite_eq_left rfl, h1]
  · rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hne]
    have hs : ∑ x ∈ Finset.Ico a b, IncidenceAlgebra.mu ℚ a x
        = ∑ x ∈ Finset.Ico a b, f a x := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := Finset.mem_Ico.1 hx
      have hsub : Finset.Ico a x ⊂ Finset.Ico a b :=
        (Finset.ssubset_iff_of_subset (Finset.Ico_subset_Ico_right hx'.2.le)).2
          ⟨x, hx, Finset.right_notMem_Ico⟩
      have hlt : (Finset.Ico a x).card < n := by
        rw [← hn]; exact Finset.card_lt_card hsub
      exact ih _ hlt x rfl hx'.1
    rw [hs]
    have h := h2 a b (lt_of_le_of_ne hab hne)
    rw [← Finset.Ico_insert_right hab, Finset.sum_insert Finset.right_notMem_Ico] at h
    linarith

/-- The literal transmutation substitution `x ↦ (1-y)/(1-xy)`, `y ↦ 1-xy`, landing in `ℚ(x,y)`. -/
noncomputable def transmuteHom : Pxy →+* FracXY :=
  eval₂Hom ((algebraMap Pxy FracXY).comp C) ![(1 - yF) / (1 - xF * yF), 1 - xF * yF]

/-- Transmutation `f̄(x,y) = f((1-y)/(1-xy), 1-xy)` of a polynomial, as an element of `ℚ(x,y)`. -/
noncomputable def transmute (f : Pxy) : FracXY := transmuteHom f

theorem tr_X0 : transmuteHom (X 0) = (1 - yF) / (1 - xF * yF) := by
  simp [transmuteHom]

theorem tr_X1 : transmuteHom (X 1) = 1 - xF * yF := by
  simp [transmuteHom]

/-- `1 - xy ≠ 0` in `ℚ(x,y)`. -/
theorem one_sub_xy_ne : (1 : FracXY) - xF * yF ≠ 0 := by
  intro h
  have h' : algebraMap Pxy FracXY (1 - X 0 * X 1) = algebraMap Pxy FracXY 0 := by
    rw [map_sub, map_one, map_mul, map_zero]
    exact h
  have h'' := IsFractionRing.injective Pxy FracXY h'
  have h3 := congrArg MvPolynomial.constantCoeff h''
  simp at h3

/-- Coercion injectivity `ℚ[x,y] → ℚ(x,y)`. -/
theorem iota_injective : Function.Injective (algebraMap Pxy FracXY) :=
  IsFractionRing.injective Pxy FracXY

end C374966
