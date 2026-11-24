# Lean source appendix: MathDB 355348

34 modules, in import order. Each block is byte-identical to `src/<Module>.lean`.
Lean 4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 (see PINS.json).

### `BiasDefinitions.lean`

```lean
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Card

open Filter Asymptotics

namespace BiasGrowth

/-- The real part of the logarithmic derivative of the complex Gamma function. -/
noncomputable def psi (x : ℝ) : ℝ := (Complex.digamma (x : ℂ)).re

/-- Positive representative of the inverse residue, with zero represented by t. -/
noncomputable def rbar (k t r : ℕ) : ℕ :=
  let v := (((r : ZMod t) * (k : ZMod t)⁻¹) : ZMod t).val
  if v = 0 then t else v

/-- The source's second-order score, equation (1.5). -/
noncomputable def psiKT (k t r : ℕ) : ℝ :=
  -psi ((r : ℝ) / t) + psi ((rbar k t r : ℝ) / t) / k

/-- Every strict score comparison is present, and only weak comparisons are present. -/
def Compatible (t : ℕ) (R : ℕ → Fin t → Fin t → Prop) : Prop :=
  ∀ k, 2 ≤ k → Nat.Coprime k t → ∀ r s : Fin t,
    (psiKT k t (r.val+1) > psiKT k t (s.val+1) → R k r s) ∧
    (R k r s → psiKT k t (r.val+1) ≥ psiKT k t (s.val+1)) ∧ ¬ R k r r

/-- Full set of labelled relations; the parameter k has no cap. -/
def orderings (t : ℕ) (R : ℕ → Fin t → Fin t → Prop) : Set (Fin t → Fin t → Prop) :=
  {S | ∃ k : ℕ, 2 ≤ k ∧ Nat.Coprime k t ∧ S = R k}

noncomputable def orderCount (t : ℕ) (R : ℕ → Fin t → Fin t → Prop) : ℕ :=
  Set.ncard {S : Fin t → Fin t → Prop | ∃ k : ℕ, 2 ≤ k ∧ Nat.Coprime k t ∧ S = R k}

noncomputable def strictFamily (t k : ℕ) (r s : Fin t) : Prop :=
  psiKT k t (s.val+1) < psiKT k t (r.val+1)

/-- The required endpoint proposition. No theorem of this type is claimed yet. -/
def Conjecture355348 : Prop :=
  ∀ (R : ∀ t : ℕ, ℕ → Fin t → Fin t → Prop),
    (∀ t, 2 ≤ t → Compatible t (R t)) →
    (fun t : ℕ => (orderCount t (R t) : ℝ) / Nat.totient t) =o[atTop] (fun t => (t : ℝ)) ∧
    (fun t : ℕ => Real.log t) =o[atTop]
      (fun t => (orderCount t (R t) : ℝ) / Nat.totient t)

/-- The strict instance makes the compatibility hypothesis nonvacuous, for every modulus. -/
theorem compatible_strict (t : ℕ) : Compatible t (strictFamily t) := by
  intro k _ _ r s
  exact ⟨id, le_of_lt, lt_irrefl _⟩

theorem compatible_satisfiable (t : ℕ) :
    ∃ R : ℕ → Fin t → Fin t → Prop, Compatible t R :=
  ⟨strictFamily t, compatible_strict t⟩

theorem psi_one : psi 1 = -Real.eulerMascheroniConstant := by
  simp [psi, Complex.digamma_one]

/-- Finiteness uses the finite universe of labelled relations, not a truncation of k. -/
theorem orderings_finite (t : ℕ) (R : ℕ → Fin t → Fin t → Prop) :
    (orderings t R).Finite := Set.toFinite _

theorem orderings_nonempty (t : ℕ) (ht : 2 ≤ t)
    (R : ℕ → Fin t → Fin t → Prop) : (orderings t R).Nonempty := by
  refine ⟨R (t+1), t+1, by omega, ?_, rfl⟩
  simp

theorem orderCount_pos (t : ℕ) (ht : 2 ≤ t)
    (R : ℕ → Fin t → Fin t → Prop) : 0 < orderCount t R := by
  exact Set.ncard_pos (orderings_finite t R) |>.mpr (orderings_nonempty t ht R)

theorem rbar_pos (k t r : ℕ) (ht : 0 < t) : 1 ≤ rbar k t r := by
  dsimp only [rbar]
  split_ifs with h
  · exact ht
  · omega

theorem rbar_le (k t r : ℕ) (ht : 0 < t) : rbar k t r ≤ t := by
  have : NeZero t := ⟨ht.ne'⟩
  dsimp only [rbar]
  split_ifs
  · exact le_rfl
  · exact (ZMod.val_lt _).le

theorem rbar_cast (k t r : ℕ) (ht : 0 < t) :
    (rbar k t r : ZMod t) = (r : ZMod t) * (k : ZMod t)⁻¹ := by
  have : NeZero t := ⟨ht.ne'⟩
  dsimp only [rbar]
  split_ifs with h
  · rw [ZMod.natCast_self]
    have he := ZMod.natCast_zmod_val ((r : ZMod t) * (k : ZMod t)⁻¹)
    rw [h, Nat.cast_zero] at he
    exact he
  · exact ZMod.natCast_zmod_val _

theorem rbar_correct (k t r : ℕ) (ht : 0 < t) (hk : Nat.Coprime k t) :
    (k : ZMod t) * (rbar k t r : ZMod t) = (r : ZMod t) := by
  rw [rbar_cast k t r ht, mul_left_comm, ZMod.coe_mul_inv_eq_one k hk, mul_one]

theorem rbar_modEq (k t r : ℕ) (ht : 0 < t) (hk : Nat.Coprime k t) :
    Nat.ModEq t (k * rbar k t r) r := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  exact rbar_correct k t r ht hk

#print Conjecture355348
#print axioms compatible_strict
#print axioms compatible_satisfiable
#print axioms psi_one
#print axioms orderings_finite
#print axioms orderings_nonempty
#print axioms orderCount_pos
#print axioms rbar_pos
#print axioms rbar_le
#print axioms rbar_correct
#print axioms rbar_modEq

end BiasGrowth
```

### `BiasDigamma.lean`

```lean
import BiasDefinitions
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Filter Topology Set

namespace BiasGrowth

private theorem complex_not_pole {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (x : ℂ) ≠ -(n : ℂ) := by
  intro h
  have := congrArg Complex.re h
  simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at this
  have : (n : ℝ) < 0 := by linarith
  exact (Nat.cast_nonneg n).not_gt this

/-- The chosen psi is also the real logarithmic derivative of Gamma. -/
theorem psi_eq_deriv_logGamma {x : ℝ} (hx : 0 < x) :
    psi x = deriv (Real.log ∘ Real.Gamma) x := by
  have hc := (Complex.differentiableAt_Gamma (x : ℂ) (complex_not_pole hx)).hasDerivAt
  have hr : deriv Real.Gamma x = (deriv Complex.Gamma (x : ℂ)).re :=
    hc.real_of_complex.deriv
  have hd := Real.differentiableAt_Gamma (s := x) (fun n => by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith)
  rw [Function.comp_def, deriv.log hd (Real.Gamma_pos_of_pos hx).ne']
  rw [psi, Complex.digamma_def, logDeriv_apply, Complex.Gamma_ofReal, hr]
  simp only [Complex.div_ofReal_re]

/-- Monotonicity follows from the Bohr–Mollerup log convexity already in Mathlib. -/
theorem psi_monotoneOn : MonotoneOn psi (Ioi 0) := by
  intro x hx y hy hxy
  rw [psi_eq_deriv_logGamma hx, psi_eq_deriv_logGamma hy]
  apply Real.convexOn_log_Gamma.monotoneOn_deriv _ hx hy hxy
  intro z hz
  change 0 < z at hz
  exact (Real.differentiableAt_Gamma (fun n => by
    have := Nat.cast_nonneg (α := ℝ) n
    exact ne_of_gt (by linarith : -(n : ℝ) < z))).log
      (Real.Gamma_pos_of_pos hz).ne'

theorem psi_add_nat {x : ℝ} (hx : 0 < x) (N : ℕ) :
    psi (x + N) = psi x + ∑ n ∈ Finset.range N, 1 / (x + n) := by
  have h := congrArg Complex.re (Complex.digamma_apply_add_nat (complex_not_pole hx) N)
  simpa only [psi, ← Complex.ofReal_natCast, ← Complex.ofReal_add,
    ← Complex.ofReal_inv, Complex.add_re, Complex.ofReal_re, Complex.re_sum, one_div] using h

theorem psi_add_one {x : ℝ} (hx : 0 < x) :
    psi (x + 1) = psi x + 1 / x := by
  simpa using psi_add_nat hx 1

/-- Shift the gap to the right and squeeze it between zero and one reciprocal. -/
theorem shifted_psi_gap_bounds {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (N : ℕ) :
    0 ≤ psi (1 + N) - psi (x + N) ∧
    psi (1 + N) - psi (x + N) ≤ 1 / (x + N) := by
  have hp : 0 < x + (N : ℝ) := by positivity
  have hq : 0 < 1 + (N : ℝ) := by positivity
  have h₁ := psi_monotoneOn hp hq (by linarith : x + (N : ℝ) ≤ 1 + N)
  have h₂ := psi_monotoneOn hq (by positivity : 0 < (x + (N : ℝ)) + 1)
    (by linarith : 1 + (N : ℝ) ≤ (x + N) + 1)
  rw [psi_add_one hp] at h₂
  constructor <;> linarith

theorem shifted_psi_gap_tendsto {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Tendsto (fun N : ℕ => psi (1 + N) - psi (x + N)) atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => 1 / (x + (N : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, one_div] using
      (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop))
  exact squeeze_zero (fun N => (shifted_psi_gap_bounds hx hx1 N).1)
    (fun N => (shifted_psi_gap_bounds hx hx1 N).2) hi

/-- Exact partial-sum identity, including the genuine digamma remainder. -/
theorem psi_gap_partial_sum {x : ℝ} (hx : 0 < x) (N : ℕ) :
    (∑ n ∈ Finset.range N, (1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + 1))) =
      psi 1 - psi x - (psi (1 + N) - psi (x + N)) := by
  rw [psi_add_nat (by norm_num : (0 : ℝ) < 1), psi_add_nat hx, Finset.sum_sub_distrib]
  simp only [add_comm (1 : ℝ), add_comm x]
  ring

/-- The mandatory Gamma-to-series bridge, with summability certified by HasSum. -/
theorem psi_gap_hasSum {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + 1))
      (psi 1 - psi x) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => ?_) _).2
  · have := (tendsto_const_nhds (x := psi 1 - psi x)).sub
      (shifted_psi_gap_tendsto hx hx1)
    simpa only [sub_zero, ← psi_gap_partial_sum hx] using this
  · apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem psi_gap_series {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    psi 1 - psi x =
      ∑' n : ℕ, (1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + 1)) :=
  (psi_gap_hasSum hx hx1).tsum_eq.symm

#print axioms psi_eq_deriv_logGamma
#print axioms psi_monotoneOn
#print axioms psi_add_nat
#print axioms psi_gap_hasSum
#print axioms psi_gap_series

end BiasGrowth
```

### `BiasResidues.lean`

```lean
import BiasDefinitions

namespace BiasGrowth

/-- Casting the positive representatives 1,...,t into ZMod t is injective. -/
theorem positive_representative_injective {t a b : ℕ}
    (ha : 1 ≤ a) (hat : a ≤ t) (hb : 1 ≤ b) (hbt : b ≤ t)
    (h : (a : ZMod t) = (b : ZMod t)) : a = b := by
  have hsub : ((a - 1 : ℕ) : ZMod t) = ((b - 1 : ℕ) : ZMod t) := by
    push_cast [Nat.cast_sub ha, Nat.cast_sub hb]
    rw [h]
  have he := (ZMod.natCast_eq_natCast_iff _ _ _).mp hsub
  have := he.eq_of_lt_of_lt (by omega) (by omega)
  omega

/-- The positive representative satisfying the source congruence is unique. -/
theorem rbar_eq_iff {k t r a : ℕ} (ht : 0 < t) (hk : Nat.Coprime k t)
    (ha : 1 ≤ a) (hat : a ≤ t) :
    rbar k t r = a ↔ (k : ZMod t) * (a : ZMod t) = (r : ZMod t) := by
  constructor
  · intro h
    rw [← h]
    exact rbar_correct k t r ht hk
  · intro h
    apply positive_representative_injective (rbar_pos k t r ht) (rbar_le k t r ht) ha hat
    rw [rbar_cast k t r ht, ← h, mul_comm (k : ZMod t) (a : ZMod t), mul_assoc, ZMod.coe_mul_inv_eq_one k hk, mul_one]

theorem rbar_injectiveOn {k t : ℕ} (ht : 0 < t) (hk : Nat.Coprime k t) :
    Set.InjOn (rbar k t) (Set.Icc 1 t) := by
  intro r hr s hs he
  have hc := congrArg (fun a : ℕ => (k : ZMod t) * (a : ZMod t)) he
  rw [rbar_correct k t r ht hk, rbar_correct k t s ht hk] at hc
  exact positive_representative_injective hr.1 hr.2 hs.1 hs.2 hc

/-- Every inverse residue in [1,t] occurs, not just at most once. -/
theorem rbar_surjectiveOn {k t : ℕ} (ht : 0 < t) (hk : Nat.Coprime k t) :
    Set.SurjOn (rbar k t) (Set.Icc 1 t) (Set.Icc 1 t) := by
  intro a ha
  let r := rbar 1 t (k * a)
  have hr : (r : ZMod t) = (k : ZMod t) * (a : ZMod t) := by
    simp [r, rbar_cast 1 t (k*a) ht]
  refine ⟨r, ⟨rbar_pos 1 t (k*a) ht, rbar_le 1 t (k*a) ht⟩, ?_⟩
  exact (rbar_eq_iff ht hk ha.1 ha.2).mpr hr.symm

theorem rbar_bijOn {k t : ℕ} (ht : 0 < t) (hk : Nat.Coprime k t) :
    Set.BijOn (rbar k t) (Set.Icc 1 t) (Set.Icc 1 t) :=
  ⟨fun r _ => ⟨rbar_pos k t r ht, rbar_le k t r ht⟩,
    rbar_injectiveOn ht hk, rbar_surjectiveOn ht hk⟩

/-- The distinguished label k mod t has inverse representative 1. -/
theorem rbar_distinguished {k t q : ℕ} (ht : 0 < t) (hk : Nat.Coprime k t)
    (hq : (k : ZMod t) = (q : ZMod t)) : rbar k t q = 1 := by
  exact (rbar_eq_iff ht hk (by omega) ht).mpr (by simpa using hq)

/-- The inverse-residue permutation is unchanged within a congruence class of k. -/
theorem rbar_congr {k l t r : ℕ} (h : Nat.ModEq t k l) :
    rbar k t r = rbar l t r := by
  have hc := (ZMod.natCast_eq_natCast_iff k l t).mpr h
  simp only [rbar, hc]

#print axioms positive_representative_injective
#print axioms rbar_eq_iff
#print axioms rbar_bijOn
#print axioms rbar_distinguished
#print axioms rbar_congr

end BiasGrowth
```

### `BiasEstimates.lean`

```lean
import BiasDigamma
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.NormNum

open Filter Topology Set

namespace BiasGrowth

noncomputable def A (x : ℝ) : ℝ := psi 1 - psi x

/-- The loose form of estimate (1), sufficient for the support and recovery bounds. -/
theorem A_bounds {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    1 / x - 1 ≤ A x ∧ A x ≤ 1 / x := by
  have h₁ := psi_monotoneOn (by norm_num : (0 : ℝ) < 1)
    (by positivity : 0 < x + 1) (by linarith : (1 : ℝ) ≤ x + 1)
  have h₂ := psi_monotoneOn (by positivity : 0 < x + 1)
    (by norm_num : (0 : ℝ) < 1 + 1) (by linarith : x + 1 ≤ 1 + 1)
  rw [psi_add_one hx] at h₁ h₂
  rw [psi_add_one (by norm_num : (0 : ℝ) < 1)] at h₂
  simp only [one_div] at h₁ h₂ ⊢
  norm_num at h₂
  constructor <;> dsimp [A] <;> linarith

theorem A_nonneg {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : 0 ≤ A x := by
  exact sub_nonneg.mpr (psi_monotoneOn hx (by norm_num) hx1)

/-- Subtracting the two genuine digamma series is justified by HasSum. -/
theorem psi_difference_hasSum {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hx1 : x ≤ 1) (hy1 : y ≤ 1) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + y))
      (psi y - psi x) := by
  convert (psi_gap_hasSum hx hx1).sub (psi_gap_hasSum hy hy1) using 1
  · funext n
    ring
  · ring

/-- A summand identity used for both slope bounds. -/
theorem reciprocal_difference {n x y : ℝ} (hx : 0 < n + x) (hy : 0 < n + y) :
    1 / (n + x) - 1 / (n + y) = (y - x) / ((n + x) * (n + y)) := by
  field_simp
  ring

/-- Seven terms already give the uniform lower slope 3/2. -/
theorem psi_slope_lower {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    (3 / 2 : ℝ) * (y - x) ≤ psi y - psi x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hx1 : x ≤ 1 := hxy.trans hy1
  have hs := psi_difference_hasSum hx hy hx1 hy1
  have hp := sum_le_hasSum (Finset.range 7) (fun n _ =>
    sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))) hs
  have hterm (n : ℕ) : (y - x) / ((n : ℝ) + 1)^2 ≤
      1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + y) := by
    rw [reciprocal_difference (by positivity) (by positivity)]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hden : ((n : ℝ) + x) * ((n : ℝ) + y) ≤ ((n : ℝ) + 1)^2 := by
      nlinarith [mul_nonneg (show 0 ≤ 1 - x by linarith)
        (show 0 ≤ 1 - y by linarith)]
    exact mul_le_mul_of_nonneg_left hden (sub_nonneg.mpr hxy)
  have hsum := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range 7) => hterm n)
  have hrat : (3 / 2 : ℝ) * (y - x) ≤
      ∑ n ∈ Finset.range 7, (y - x) / ((n : ℝ) + 1)^2 := by
    norm_num [Finset.sum_range_succ]
    linarith
  exact hrat.trans (hsum.trans hp)

#print axioms A_bounds
#print axioms A_nonneg
#print axioms psi_difference_hasSum
#print axioms psi_slope_lower

end BiasGrowth
```

### `BiasSlopeUpper.lean`

```lean
import BiasEstimates

open Filter Topology

namespace BiasGrowth

/-- The n≥1 part is controlled by a telescoping reciprocal difference. -/
theorem reciprocal_difference_succ_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (n : ℕ) :
    1 / ((n : ℝ) + 1 + x) - 1 / ((n : ℝ) + 1 + y) ≤
      (y - x) * (1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + 1 + x)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 < (n : ℝ) + x := by positivity
  have hq : 0 < (n : ℝ) + 1 + x := by positivity
  have hr : 0 < (n : ℝ) + 1 + y := by linarith
  rw [reciprocal_difference hq hr]
  have he : 1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + 1 + x) =
      1 / (((n : ℝ) + x) * ((n : ℝ) + 1 + x)) := by
    field_simp
    ring
  rw [he, mul_one_div]
  apply (div_le_div_iff₀ (mul_pos hq hr) (mul_pos hp hq)).2
  have hden : ((n : ℝ) + x) * ((n : ℝ) + 1 + x) ≤
      ((n : ℝ) + 1 + x) * ((n : ℝ) + 1 + y) := by
    nlinarith
  exact mul_le_mul_of_nonneg_left hden (sub_nonneg.mpr hxy)

/-- Uniform analytic upper slope before restricting x to [9/10,1]. -/
theorem psi_slope_upper_general {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    psi y - psi x ≤ (y - x) * (1 / x^2 + 1 / x) := by
  have hy : 0 < y := hx.trans_le hxy
  have hd : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hs := psi_difference_hasSum hx hy (hxy.trans hy1) hy1
  have hzero : 1 / x - 1 / y ≤ (y - x) / x^2 := by
    rw [show 1 / x - 1 / y = (y-x)/(x*y) by field_simp]
    apply (div_le_div_iff₀ (mul_pos hx hy) (sq_pos_of_pos hx)).2
    have := mul_le_mul_of_nonneg_left hxy hx.le
    nlinarith
  have hsum (N : ℕ) :
      (∑ n ∈ Finset.range (N+1), (1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + y))) ≤
      (y - x) * (1 / x^2 + 1 / x) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one]
    have htail := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range N) =>
      reciprocal_difference_succ_le hx hxy n)
    rw [← Finset.mul_sum] at htail
    have htel : (∑ n ∈ Finset.range N,
        (1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + 1 + x))) =
        1 / x - 1 / ((N : ℝ) + x) := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add] using
        Finset.sum_range_sub' (fun n : ℕ => 1 / ((n : ℝ) + x)) N
    rw [htel] at htail
    have hlast : 0 ≤ (y-x) / ((N : ℝ) + x) := by positivity
    simp only [div_eq_mul_inv] at htail hzero hlast ⊢
    nlinarith [htail, hzero]
  apply le_of_tendsto hs.tendsto_sum_nat
  filter_upwards [eventually_ge_atTop 1] with N hN
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  exact hsum M

/-- Estimate (3) from the written proof. -/
theorem psi_slope_upper {x y : ℝ} (hx : (9 / 10 : ℝ) ≤ x)
    (hxy : x ≤ y) (hy1 : y ≤ 1) :
    psi y - psi x ≤ (5 / 2 : ℝ) * (y - x) := by
  have hxp : 0 < x := by linarith
  have hd : 0 ≤ y-x := sub_nonneg.mpr hxy
  have h₁ : 1 / x ≤ (10 / 9 : ℝ) := (div_le_iff₀ hxp).2 (by linarith)
  have h₂ : 1 / x^2 ≤ (100 / 81 : ℝ) := (div_le_iff₀ (sq_pos_of_pos hxp)).2 (by
    nlinarith [sq_nonneg (x - 9/10)])
  have hb : 1 / x^2 + 1 / x ≤ (5 / 2 : ℝ) := by linarith
  exact (psi_slope_upper_general hxp hxy hy1).trans (by nlinarith)

#print axioms reciprocal_difference_succ_le
#print axioms psi_slope_upper_general
#print axioms psi_slope_upper

end BiasGrowth
```

### `BiasScoreSupport.lean`

```lean
import BiasEstimates
import BiasResidues

namespace BiasGrowth

/-- Score with increasing natural order; differs from minus psiKT by a common constant. -/
noncomputable def B (k t r : ℕ) : ℝ :=
  psi ((r : ℝ) / t) + A ((rbar k t r : ℝ) / t) / k

theorem B_eq (k t r : ℕ) : B k t r = psi 1 / k - psiKT k t r := by
  unfold B A psiKT
  ring

/-- Literal-score support estimate for non-strict inversions, hence allowing ties. -/
theorem score_inversion_support {k t r s : ℕ}
    (hk : 0 < k) (ht : 0 < t) (hr : 1 ≤ r) (hrs : r ≤ s) (hst : s ≤ t)
    (hinv : B k t s ≤ B k t r) :
    3 * (k : ℝ) * (rbar k t r : ℝ) * ((s : ℝ) - r) ≤ 2 * (t : ℝ)^2 := by
  have htr : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  have hkr : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hrr : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hsr : (r : ℝ) ≤ s := Nat.cast_le.mpr hrs
  have hst' : (s : ℝ) ≤ t := Nat.cast_le.mpr hst
  have ha : (0 : ℝ) < rbar k t r := Nat.cast_pos.mpr (rbar_pos k t r ht)
  have hb : (0 : ℝ) < rbar k t s := Nat.cast_pos.mpr (rbar_pos k t s ht)
  have hal : (rbar k t r : ℝ) ≤ t := Nat.cast_le.mpr (rbar_le k t r ht)
  have hbl : (rbar k t s : ℝ) ≤ t := Nat.cast_le.mpr (rbar_le k t s ht)
  have hlow := psi_slope_lower (div_pos hrr htr)
    ((div_le_div_iff_of_pos_right htr).mpr hsr) ((div_le_one htr).mpr hst')
  have hupper := (A_bounds (div_pos ha htr) ((div_le_one htr).mpr hal)).2
  rw [one_div_div] at hupper
  have hnon := A_nonneg (div_pos hb htr) ((div_le_one htr).mpr hbl)
  have hmul : (k : ℝ) * (psi ((s : ℝ)/t) - psi ((r : ℝ)/t)) ≤
      A ((rbar k t r : ℝ)/t) := by
    unfold B at hinv
    have he := (mul_le_mul_of_nonneg_left hinv hkr.le)
    have hrdiv : (k : ℝ) * (A ((rbar k t r : ℝ)/t) / k) =
        A ((rbar k t r : ℝ)/t) := mul_div_cancel₀ _ hkr.ne'
    have hsdiv : (k : ℝ) * (A ((rbar k t s : ℝ)/t) / k) =
        A ((rbar k t s : ℝ)/t) := mul_div_cancel₀ _ hkr.ne'
    rw [mul_add, mul_add, hrdiv, hsdiv] at he
    linarith
  have hlow' : (3 / 2 : ℝ) * ((s : ℝ)-r) ≤
      (t : ℝ) * (psi ((s : ℝ)/t) - psi ((r : ℝ)/t)) := by
    have h := (mul_le_mul_of_nonneg_left hlow htr.le)
    field_simp at h ⊢
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hmul ha.le
  have hu := (le_div_iff₀ ha).mp hupper
  have hl := mul_le_mul_of_nonneg_left hlow' (mul_nonneg hkr.le ha.le)
  nlinarith

#print axioms B_eq
#print axioms score_inversion_support

end BiasGrowth
```

### `BiasInversions.lean`

```lean
import BiasDefinitions

namespace BiasGrowth

/-- Count the right inversions of a labelled relation oriented as "more common".
Since B is minus the source score up to a constant, an inversion at r is S s r. -/
noncomputable def rightInversions {t : ℕ} (S : Fin t → Fin t → Prop) (r : Fin t) :
    Finset (Fin t) := by
  classical
  exact Finset.univ.filter (fun s => r < s ∧ S s r)

noncomputable def rightInvCount {t : ℕ} (S : Fin t → Fin t → Prop) (r : Fin t) : ℕ :=
  (rightInversions S r).card

/-- If a relation has a unique maximizer, that label is recoverable from the relation alone. -/
theorem recover_label_of_unique_maxima {t : ℕ} (S T : Fin t → Fin t → Prop)
    (p q : Fin t)
    (hp : ∀ r, r ≠ p → rightInvCount S r < rightInvCount S p)
    (hq : ∀ r, r ≠ q → rightInvCount T r < rightInvCount T q)
    (hST : S = T) : p = q := by
  subst T
  by_contra h
  exact (hp q (fun he => h he.symm)).not_gt (hq p h)

/-- A switch witness together with no newly appearing inversions forces a strict count drop. -/
theorem rightInvCount_strict_drop {t : ℕ} (S T : Fin t → Fin t → Prop) (r : Fin t)
    (hmono : ∀ s, r < s → T s r → S s r)
    (hw : ∃ s, r < s ∧ S s r ∧ ¬ T s r) :
    rightInvCount T r < rightInvCount S r := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro s hs
    obtain ⟨_, hrs, hT⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrs, hmono s hrs hT⟩
  · obtain ⟨s, hrs, hS, hT⟩ := hw
    intro he
    have hs : s ∈ rightInversions S r := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrs, hS⟩
    rw [← he] at hs
    exact hT (Finset.mem_filter.mp hs).2.2

#print axioms recover_label_of_unique_maxima
#print axioms rightInvCount_strict_drop

end BiasGrowth
```

### `BiasTailCombinatorics.lean`

```lean
import Mathlib.Data.Finset.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace BiasGrowth

/-- A chain of subsets of a D-element set has at most D+1 members. -/
theorem subset_chain_card_le {α : Type*} [DecidableEq α]
    (U : Finset α) (S : Finset (Finset α))
    (hsub : ∀ a ∈ S, a ⊆ U)
    (hchain : ∀ a ∈ S, ∀ b ∈ S, a ⊆ b ∨ b ⊆ a) :
    S.card ≤ U.card + 1 := by
  apply le_trans ?_ (le_of_eq (Finset.card_range (U.card + 1)))
  apply Finset.card_le_card_of_injOn Finset.card (t := Finset.range (U.card + 1))
  · intro a ha
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_card (hsub a ha)))
  · intro a ha b hb hab
    rcases hchain a ha b hb with h | h
    · exact Finset.eq_of_subset_of_card_le h hab.ge
    · exact (Finset.eq_of_subset_of_card_le h hab.le).symm

/-- Positive-intercept affine functions of 1/x have a unique zero on x>0. -/
theorem reciprocal_crossing_unique {c d x y : ℝ} (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y)
    (h₁ : c + d / x = 0) (h₂ : c + d / y = 0) : x = y := by
  have h₁' : c * x + d = 0 := by
    have := congrArg (fun z : ℝ => z * x) h₁
    simpa [add_mul, hx.ne'] using this
  have h₂' : c * y + d = 0 := by
    have := congrArg (fun z : ℝ => z * y) h₂
    simpa [add_mul, hy.ne'] using this
  nlinarith

/-- Negative signs can only disappear as the positive parameter increases. -/
theorem reciprocal_negative_antitone {c d x y : ℝ} (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y)
    (h : c + d / y < 0) : c + d / x < 0 := by
  have heq (z : ℝ) (hz : z ≠ 0) : c + d / z = (c * z + d) / z := by
    field_simp
  rw [heq y hy.ne', div_lt_iff₀ hy, zero_mul] at h
  rw [heq x hx.ne', div_lt_iff₀ hx, zero_mul]
  nlinarith

/-- At most D exceptional parameters can have a zero in D coordinates. -/
theorem exceptional_card_le {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (U : Finset ι) (E : Finset κ) (tie : ι → κ → Prop)
    (hex : ∀ j ∈ E, ∃ i ∈ U, tie i j)
    (hunique : ∀ i ∈ U, ∀ j ∈ E, ∀ k ∈ E, tie i j → tie i k → j = k) :
    E.card ≤ U.card := by
  classical
  choose f hf hf' using hex
  let g : E → U := fun j => ⟨f j.val j.property, hf j.val j.property⟩
  have hg : Function.Injective g := by
    intro j k h
    apply Subtype.ext
    have he : f j.val j.property = f k.val k.property := congrArg Subtype.val h
    apply hunique _ (hf _ j.property) _ j.property _ k.property (hf' _ j.property)
    rw [he]
    exact hf' _ k.property
  have := Fintype.card_le_of_injective g hg
  simpa only [Fintype.card_coe] using this

/-- A relation family determined by a chain off at most D exceptional parameters
has at most 2D+1 values. At each exception its value is unrestricted. -/
theorem chain_with_exceptions_card_le {ι κ β : Type*}
    [DecidableEq ι] [DecidableEq κ] [DecidableEq β]
    (U : Finset ι) (J E : Finset κ) (v : κ → Finset ι) (R : κ → β)
    (hE : E ⊆ J) (hcard : E.card ≤ U.card)
    (hsub : ∀ j ∈ J \ E, v j ⊆ U)
    (hchain : ∀ i ∈ J \ E, ∀ j ∈ J \ E, v i ⊆ v j ∨ v j ⊆ v i)
    (hdet : ∀ i ∈ J \ E, ∀ j ∈ J \ E, v i = v j → R i = R j) :
    (J.image R).card ≤ 2 * U.card + 1 := by
  classical
  let G := J \ E
  let P := G.image v
  have hp : P.card ≤ U.card + 1 := by
    apply subset_chain_card_le U P
    · intro a ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
      exact hsub j hj
    · intro a ha b hb
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      exact hchain i hi j hj
  have hgood : (G.image R).card ≤ P.card := by
    have hex : ∀ p ∈ P, ∃ j ∈ G, v j = p := fun p hp => Finset.mem_image.mp hp
    choose f hf hf' using hex
    let g : P → G.image R := fun p =>
      ⟨R (f p.val p.property), Finset.mem_image.mpr ⟨_, hf _ p.property, rfl⟩⟩
    have hg : Function.Surjective g := by
      intro b
      obtain ⟨j, hj, hR⟩ := Finset.mem_image.mp b.property
      let p : P := ⟨v j, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
      refine ⟨p, Subtype.ext ?_⟩
      change R (f p.val p.property) = b.val
      rw [hdet _ (hf _ p.property) j hj (hf' _ p.property), hR]
    have := Fintype.card_le_of_surjective g hg
    simpa only [Fintype.card_coe] using this
  have hsplit : J = G ∪ E := (Finset.sdiff_union_of_subset hE).symm
  calc
    (J.image R).card = ((G.image R) ∪ (E.image R)).card := by rw [hsplit, Finset.image_union]
    _ ≤ (G.image R).card + (E.image R).card := Finset.card_union_le _ _
    _ ≤ P.card + E.card := Nat.add_le_add hgood Finset.card_image_le
    _ ≤ 2 * U.card + 1 := by omega

/-- The single-crossing count, allowing arbitrary values of R at ties.
The parameter set J is any finite sample, with no upper bound on its elements. -/
theorem reciprocal_patterns_card_le {ι β : Type*}
    [DecidableEq ι] [DecidableEq β]
    (U : Finset ι) (J : Finset ℝ) (c d : ι → ℝ) (R : ℝ → β)
    (hc : ∀ i ∈ U, 0 < c i) (hJ : ∀ x ∈ J, 0 < x)
    (hdet : ∀ x ∈ J, ∀ y ∈ J,
      (∀ i ∈ U, c i + d i / x ≠ 0) →
      (∀ i ∈ U, c i + d i / y ≠ 0) →
      (∀ i ∈ U, (c i + d i / x < 0 ↔ c i + d i / y < 0)) → R x = R y) :
    (J.image R).card ≤ 2 * U.card + 1 := by
  classical
  let E := J.filter (fun x => ∃ i ∈ U, c i + d i / x = 0)
  let v := fun x => U.filter (fun i => c i + d i / x < 0)
  have hE : E ⊆ J := Finset.filter_subset _ _
  have hcard : E.card ≤ U.card := by
    apply exceptional_card_le U E (fun i x => c i + d i / x = 0)
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro i hi x hx y hy h₁ h₂
      exact reciprocal_crossing_unique (hc i hi) (hJ x (hE hx)) (hJ y (hE hy)) h₁ h₂
  apply chain_with_exceptions_card_le U J E v R hE hcard
  · intro x _
    exact Finset.filter_subset _ _
  · intro x hx y hy
    have hxp := hJ x (Finset.mem_sdiff.mp hx).1
    have hyp := hJ y (Finset.mem_sdiff.mp hy).1
    have hmono {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) : v b ⊆ v a := by
      intro i hi
      obtain ⟨hi, hn⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨hi, reciprocal_negative_antitone (hc i hi) ha hb hab hn⟩
    rcases le_total x y with h | h
    · exact Or.inr (hmono hxp hyp h)
    · exact Or.inl (hmono hyp hxp h)
  · intro x hx y hy hxy
    have hxJ := (Finset.mem_sdiff.mp hx).1
    have hyJ := (Finset.mem_sdiff.mp hy).1
    apply hdet x hxJ y hyJ
    · intro i hi hzero
      exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_filter.mpr ⟨hxJ, i, hi, hzero⟩)
    · intro i hi hzero
      exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_filter.mpr ⟨hyJ, i, hi, hzero⟩)
    · intro i hi
      have := Finset.ext_iff.mp hxy i
      simpa only [v, Finset.mem_filter, hi, true_and] using this

#print axioms subset_chain_card_le
#print axioms reciprocal_crossing_unique
#print axioms reciprocal_negative_antitone
#print axioms exceptional_card_le
#print axioms chain_with_exceptions_card_le
#print axioms reciprocal_patterns_card_le

end BiasGrowth
```

### `BiasTailRange.lean`

```lean
import BiasTailCombinatorics
import Mathlib.Data.Set.Card

namespace BiasGrowth

/-- Finite-sample bounds give the same bound on the whole, potentially unbounded,
parameter set. No numerical cutoff on parameters is introduced. -/
theorem image_ncard_le_of_finset_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Set α) (R : α → β) (N : ℕ) (hfin : (R '' A).Finite)
    (hbound : ∀ J : Finset α, (∀ x ∈ J, x ∈ A) → (J.image R).card ≤ N) :
    (R '' A).ncard ≤ N := by
  classical
  obtain ⟨B, hBA, hB, hBeq⟩ :=
    (Set.exists_subset_image_finite_and (f := R) (s := A)
      (p := fun T => T = R '' A)).mp ⟨R '' A, Set.Subset.rfl, hfin, rfl⟩
  have hcoe : (hB.toFinset.image R : Set β) = R '' A := by
    rw [Finset.coe_image, hB.coe_toFinset, hBeq]
  rw [← hcoe, Set.ncard_coe_finset]
  apply hbound
  intro x hx
  exact hBA (hB.mem_toFinset.mp hx)

/-- The full single-crossing bound on an unbounded positive parameter set.
At tie parameters the value of R is entirely arbitrary. -/
theorem reciprocal_patterns_ncard_le {ι β : Type*}
    [DecidableEq ι] [DecidableEq β]
    (U : Finset ι) (A : Set ℝ) (c d : ι → ℝ) (R : ℝ → β)
    (hfin : (R '' A).Finite) (hc : ∀ i ∈ U, 0 < c i)
    (hA : ∀ x ∈ A, 0 < x)
    (hdet : ∀ x ∈ A, ∀ y ∈ A,
      (∀ i ∈ U, c i + d i / x ≠ 0) →
      (∀ i ∈ U, c i + d i / y ≠ 0) →
      (∀ i ∈ U, (c i + d i / x < 0 ↔ c i + d i / y < 0)) → R x = R y) :
    (R '' A).ncard ≤ 2 * U.card + 1 := by
  apply image_ncard_le_of_finset_bound A R _ hfin
  intro J hJ
  apply reciprocal_patterns_card_le U J c d R hc
  · intro x hx
    exact hA x (hJ x hx)
  · intro x hx y hy
    exact hdet x (hJ x hx) y (hJ y hy)

#print axioms image_ncard_le_of_finset_bound
#print axioms reciprocal_patterns_ncard_le

end BiasGrowth
```

### `BiasAudit.lean`

```lean
import BiasDefinitions
import BiasDigamma
import BiasResidues
import BiasEstimates
import BiasSlopeUpper
import BiasScoreSupport
import BiasInversions
import BiasTailCombinatorics
import BiasTailRange

#eval Lean.versionString

#print BiasGrowth.psi
#print BiasGrowth.rbar
#print BiasGrowth.psiKT
#print BiasGrowth.Compatible
#print BiasGrowth.orderCount
#print BiasGrowth.Conjecture355348
#check @BiasGrowth.compatible_strict
#print axioms BiasGrowth.compatible_strict
#check @BiasGrowth.compatible_satisfiable
#print axioms BiasGrowth.compatible_satisfiable
#check @BiasGrowth.psi_one
#print axioms BiasGrowth.psi_one
#check @BiasGrowth.orderings_finite
#print axioms BiasGrowth.orderings_finite
#check @BiasGrowth.orderings_nonempty
#print axioms BiasGrowth.orderings_nonempty
#check @BiasGrowth.orderCount_pos
#print axioms BiasGrowth.orderCount_pos
#check @BiasGrowth.rbar_pos
#print axioms BiasGrowth.rbar_pos
#check @BiasGrowth.rbar_le
#print axioms BiasGrowth.rbar_le
#check @BiasGrowth.rbar_cast
#print axioms BiasGrowth.rbar_cast
#check @BiasGrowth.rbar_correct
#print axioms BiasGrowth.rbar_correct
#check @BiasGrowth.rbar_modEq
#print axioms BiasGrowth.rbar_modEq
#check @BiasGrowth.psi_eq_deriv_logGamma
#print axioms BiasGrowth.psi_eq_deriv_logGamma
#check @BiasGrowth.psi_monotoneOn
#print axioms BiasGrowth.psi_monotoneOn
#check @BiasGrowth.psi_add_nat
#print axioms BiasGrowth.psi_add_nat
#check @BiasGrowth.psi_add_one
#print axioms BiasGrowth.psi_add_one
#check @BiasGrowth.shifted_psi_gap_bounds
#print axioms BiasGrowth.shifted_psi_gap_bounds
#check @BiasGrowth.shifted_psi_gap_tendsto
#print axioms BiasGrowth.shifted_psi_gap_tendsto
#check @BiasGrowth.psi_gap_partial_sum
#print axioms BiasGrowth.psi_gap_partial_sum
#check @BiasGrowth.psi_gap_hasSum
#print axioms BiasGrowth.psi_gap_hasSum
#check @BiasGrowth.psi_gap_series
#print axioms BiasGrowth.psi_gap_series
#check @BiasGrowth.positive_representative_injective
#print axioms BiasGrowth.positive_representative_injective
#check @BiasGrowth.rbar_eq_iff
#print axioms BiasGrowth.rbar_eq_iff
#check @BiasGrowth.rbar_injectiveOn
#print axioms BiasGrowth.rbar_injectiveOn
#check @BiasGrowth.rbar_surjectiveOn
#print axioms BiasGrowth.rbar_surjectiveOn
#check @BiasGrowth.rbar_bijOn
#print axioms BiasGrowth.rbar_bijOn
#check @BiasGrowth.rbar_distinguished
#print axioms BiasGrowth.rbar_distinguished
#check @BiasGrowth.rbar_congr
#print axioms BiasGrowth.rbar_congr
#check @BiasGrowth.A_bounds
#print axioms BiasGrowth.A_bounds
#check @BiasGrowth.A_nonneg
#print axioms BiasGrowth.A_nonneg
#check @BiasGrowth.psi_difference_hasSum
#print axioms BiasGrowth.psi_difference_hasSum
#check @BiasGrowth.reciprocal_difference
#print axioms BiasGrowth.reciprocal_difference
#check @BiasGrowth.psi_slope_lower
#print axioms BiasGrowth.psi_slope_lower
#check @BiasGrowth.reciprocal_difference_succ_le
#print axioms BiasGrowth.reciprocal_difference_succ_le
#check @BiasGrowth.psi_slope_upper_general
#print axioms BiasGrowth.psi_slope_upper_general
#check @BiasGrowth.psi_slope_upper
#print axioms BiasGrowth.psi_slope_upper
#check @BiasGrowth.B_eq
#print axioms BiasGrowth.B_eq
#check @BiasGrowth.score_inversion_support
#print axioms BiasGrowth.score_inversion_support
#check @BiasGrowth.recover_label_of_unique_maxima
#print axioms BiasGrowth.recover_label_of_unique_maxima
#check @BiasGrowth.rightInvCount_strict_drop
#print axioms BiasGrowth.rightInvCount_strict_drop
#check @BiasGrowth.subset_chain_card_le
#print axioms BiasGrowth.subset_chain_card_le
#check @BiasGrowth.reciprocal_crossing_unique
#print axioms BiasGrowth.reciprocal_crossing_unique
#check @BiasGrowth.reciprocal_negative_antitone
#print axioms BiasGrowth.reciprocal_negative_antitone
#check @BiasGrowth.exceptional_card_le
#print axioms BiasGrowth.exceptional_card_le
#check @BiasGrowth.chain_with_exceptions_card_le
#print axioms BiasGrowth.chain_with_exceptions_card_le
#check @BiasGrowth.reciprocal_patterns_card_le
#print axioms BiasGrowth.reciprocal_patterns_card_le
#check @BiasGrowth.image_ncard_le_of_finset_bound
#print axioms BiasGrowth.image_ncard_le_of_finset_bound
#check @BiasGrowth.reciprocal_patterns_ncard_le
#print axioms BiasGrowth.reciprocal_patterns_ncard_le
```

### `BiasLowerResidues.lean`

```lean
import BiasScoreSupport
import Mathlib.Tactic.Ring

namespace BiasGrowth

/-- In the selected unit interval, inverse residues 1,...,9 lie at labels ≤q. -/
theorem low_inverse_residue_label_le {k t q s : ℕ}
    (ht : 0 < t) (hq : q < t) (hqlo : 9*t ≤ 10*q)
    (hk : Nat.Coprime k t) (hmod : Nat.ModEq t k q)
    (hs : 1 ≤ s) (hst : s ≤ t) (ha : rbar k t s ≤ 9) : s ≤ q := by
  let h := t-q
  let a := rbar k t s
  have ha0 : 1 ≤ a := rbar_pos k t s ht
  have hh : 0 < h := Nat.sub_pos_of_lt hq
  have hhq : q+h = t := by dsimp [h]; omega
  have h10 : 10*h ≤ t := by omega
  have hah : a*h < t := by dsimp [a] at *; nlinarith
  have hab : 1 ≤ t-a*h := by omega
  have hat : t-a*h ≤ t := Nat.sub_le _ _
  have hc : (s : ZMod t) = ((t-a*h : ℕ) : ZMod t) := by
    have hkc : (k : ZMod t) = (q : ZMod t) := (ZMod.natCast_eq_natCast_iff k q t).mpr hmod
    have hqz : (q : ZMod t) = -(h : ZMod t) := by
      have he := congrArg (fun n : ℕ => (n : ZMod t)) hhq
      push_cast at he
      rw [ZMod.natCast_self] at he
      exact eq_neg_of_add_eq_zero_left he
    rw [Nat.cast_sub hah.le, ZMod.natCast_self, Nat.cast_mul, zero_sub]
    rw [← rbar_correct k t s ht hk, hkc, hqz]
    change -(h : ZMod t) * (a : ZMod t) = -((a : ZMod t)*(h : ZMod t))
    ring
  have he := positive_representative_injective hs hst hab hat hc
  have hsum := Nat.sub_add_cancel hah.le
  nlinarith

/-- All labels to the right of q have inverse residue at least ten. -/
theorem right_label_inverse_ge_ten {k t q s : ℕ}
    (ht : 0 < t) (hq : q < t) (hqlo : 9*t ≤ 10*q)
    (hk : Nat.Coprime k t) (hmod : Nat.ModEq t k q)
    (hqs : q < s) (hst : s ≤ t) : 10 ≤ rbar k t s := by
  by_contra h
  have := low_inverse_residue_label_le ht hq hqlo hk hmod (by omega) hst (by omega)
  omega

#print axioms low_inverse_residue_label_le
#print axioms right_label_inverse_ge_ten
end BiasGrowth
```

### `BiasTailSupport.lean`

```lean
import BiasScoreSupport
import Mathlib.Data.Finset.Prod

namespace BiasGrowth

noncomputable def pairC {t : ℕ} (p : Fin t × Fin t) : ℝ :=
  psi (((p.2.val+1 : ℕ) : ℝ)/t) - psi (((p.1.val+1 : ℕ) : ℝ)/t)
noncomputable def pairD (q t : ℕ) (p : Fin t × Fin t) : ℝ :=
  A ((rbar q t (p.2.val+1) : ℝ)/t) - A ((rbar q t (p.1.val+1) : ℝ)/t)
noncomputable def tailPairs (q t H : ℕ) : Finset (Fin t × Fin t) := by
  classical
  exact Finset.univ.filter (fun p => p.1 < p.2 ∧
    rbar q t (p.1.val+1) ≤ H ∧ p.2.val - p.1.val ≤ H)

theorem pairC_pos {t : ℕ} (p : Fin t × Fin t) (hp : p.1 < p.2) :
    0 < pairC p := by
  have ht : (0 : ℝ) < t := by exact_mod_cast (Nat.zero_lt_of_lt p.2.isLt)
  have hr : (0 : ℝ) < (p.1.val+1 : ℕ) := by positivity
  have hrs : ((p.1.val+1 : ℕ) : ℝ) < (p.2.val+1 : ℕ) := by exact_mod_cast (show p.1.val+1 < p.2.val+1 by omega)
  have hs : ((p.2.val+1 : ℕ) : ℝ) ≤ t := by exact_mod_cast p.2.isLt
  have h := psi_slope_lower (div_pos hr ht)
    (div_le_div_of_nonneg_right hrs.le ht.le) ((div_le_one ht).mpr hs)
  unfold pairC
  have : 0 < ((p.2.val+1 : ℕ) : ℝ)/t - ((p.1.val+1 : ℕ) : ℝ)/t :=
    sub_pos.mpr ((div_lt_div_iff_of_pos_right ht).mpr hrs)
  linarith

theorem pair_difference {q k t : ℕ} (hmod : Nat.ModEq t k q) (p : Fin t × Fin t) :
    B k t (p.2.val+1) - B k t (p.1.val+1) = pairC p + pairD q t p / k := by
  unfold B pairC pairD
  rw [rbar_congr (r := p.1.val+1) hmod, rbar_congr (r := p.2.val+1) hmod]
  push_cast
  ring

theorem tailPairs_card_le {q t H : ℕ} (ht : 0 < t) (hq : Nat.Coprime q t) :
    (tailPairs q t H).card ≤ H * H := by
  classical
  let f : Fin t × Fin t → ℕ × ℕ := fun p =>
    (rbar q t (p.1.val+1) - 1, p.2.val - p.1.val - 1)
  have hm {p} (hp : p ∈ tailPairs q t H) :
      p.1 < p.2 ∧ rbar q t (p.1.val+1) ≤ H ∧ p.2.val - p.1.val ≤ H := by
    simpa [tailPairs] using hp
  have hbound : (tailPairs q t H).card ≤
      ((Finset.range H) ×ˢ (Finset.range H)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro p hp
      have h := hm hp
      have ha := rbar_pos q t (p.1.val+1) ht
      change f p ∈ (Finset.range H) ×ˢ (Finset.range H)
      rw [Finset.mem_product]
      change rbar q t (p.1.val+1) - 1 ∈ Finset.range H ∧
        p.2.val-p.1.val-1 ∈ Finset.range H
      simp only [Finset.mem_range]
      have hh : p.1.val < p.2.val := h.1
      omega
    · intro p hp z hz he
      have h₁ := congrArg Prod.fst he
      have h₂ := congrArg Prod.snd he
      have ha := rbar_pos q t (p.1.val+1) ht
      have hb := rbar_pos q t (z.1.val+1) ht
      simp only [f] at h₁ h₂
      have hab : rbar q t (p.1.val+1) = rbar q t (z.1.val+1) := by omega
      have hr := rbar_injectiveOn ht hq
        (show p.1.val+1 ∈ Set.Icc 1 t from ⟨by omega, by omega⟩)
        (show z.1.val+1 ∈ Set.Icc 1 t from ⟨by omega, by omega⟩) hab
      have hp' := (hm hp).1
      have hz' := (hm hz).1
      apply Prod.ext
      · apply Fin.ext; omega
      · apply Fin.ext; change p.1.val < p.2.val at hp'; change z.1.val < z.2.val at hz'
        omega
  simpa using hbound

theorem inversion_mem_tailPairs {q k t H : ℕ}
    (ht : 0 < t) (hk : 0 < k) (hmod : Nat.ModEq t k q)
    (hcut : (t : ℝ)^2 ≤ (k : ℝ) * H)
    (p : Fin t × Fin t) (hp : p.1 < p.2)
    (hinv : B k t (p.2.val+1) ≤ B k t (p.1.val+1)) :
    p ∈ tailPairs q t H := by
  classical
  have hs := score_inversion_support hk ht
    (r := p.1.val+1) (s := p.2.val+1) (by omega) (by exact Nat.succ_le_succ hp.le)
    (by omega) hinv
  rw [rbar_congr hmod] at hs
  have ha := rbar_pos q t (p.1.val+1) ht
  have hd : 1 ≤ p.2.val-p.1.val := by exact Nat.sub_pos_of_lt hp
  have hcast : ((p.2.val+1 : ℕ) : ℝ) - (p.1.val+1 : ℕ) =
      (p.2.val-p.1.val : ℕ) := by rw [Nat.cast_sub hp.le]; push_cast; ring
  rw [hcast] at hs
  have hak : (1 : ℝ) ≤ rbar q t (p.1.val+1) := by exact_mod_cast ha
  have hdk : (1 : ℝ) ≤ (p.2.val-p.1.val : ℕ) := by exact_mod_cast hd
  have hkr : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have had : (rbar q t (p.1.val+1) : ℝ) * (p.2.val-p.1.val : ℕ) ≤ H := by
    nlinarith
  have haH : rbar q t (p.1.val+1) ≤ H := by
    exact_mod_cast (show (rbar q t (p.1.val+1) : ℝ) ≤ H by nlinarith)
  have hdH : p.2.val-p.1.val ≤ H := by
    exact_mod_cast (show ((p.2.val-p.1.val : ℕ) : ℝ) ≤ H by nlinarith)
  simpa [tailPairs] using And.intro hp (And.intro haH hdH)

#print axioms pairC_pos
#print axioms pair_difference
#print axioms tailPairs_card_le
#print axioms inversion_mem_tailPairs
end BiasGrowth
```

### `BiasRelationDetermination.lean`

```lean
import BiasScoreSupport

namespace BiasGrowth

theorem compatible_iff_B {t k : ℕ} {R : ℕ → Fin t → Fin t → Prop}
    (hR : Compatible t R) (hk : 2 ≤ k) (hcop : Nat.Coprime k t)
    (r s : Fin t) (hne : B k t (r.val+1) ≠ B k t (s.val+1)) :
    R k r s ↔ B k t (r.val+1) < B k t (s.val+1) := by
  have h := hR k hk hcop r s
  rw [B_eq, B_eq] at hne ⊢
  constructor
  · intro hr
    have := h.2.1 hr
    rcases lt_or_eq_of_le this with hl | he
    · linarith
    · exact (hne (by linarith)).elim
  · intro hr
    apply h.1
    linarith

theorem same_relation_of_pair_signs {t k l : ℕ} {R : ℕ → Fin t → Fin t → Prop}
    (hR : Compatible t R) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (hkc : Nat.Coprime k t) (hlc : Nat.Coprime l t)
    (hnk : ∀ r s : Fin t, r < s → B k t (s.val+1) - B k t (r.val+1) ≠ 0)
    (hnl : ∀ r s : Fin t, r < s → B l t (s.val+1) - B l t (r.val+1) ≠ 0)
    (hs : ∀ r s : Fin t, r < s →
      (B k t (s.val+1) - B k t (r.val+1) < 0 ↔
       B l t (s.val+1) - B l t (r.val+1) < 0)) : R k = R l := by
  funext r s
  apply propext
  rcases lt_trichotomy r s with hrs | rfl | hsr
  · have hnk' := hnk r s hrs
    have hnl' := hnl r s hrs
    rw [compatible_iff_B hR hk hkc r s (by intro he; exact hnk' (by linarith)),
      compatible_iff_B hR hl hlc r s (by intro he; exact hnl' (by linarith))]
    have := hs r s hrs
    constructor <;> intro h <;> by_contra hn
    · have : B l t (s.val+1) - B l t (r.val+1) < 0 := by
        have := le_of_not_gt hn
        rcases lt_or_eq_of_le this with hh | hh
        · linarith
        · exact (hnl' (by linarith)).elim
      have := (hs r s hrs).mpr this
      linarith
    · have : B k t (s.val+1) - B k t (r.val+1) < 0 := by
        have := le_of_not_gt hn
        rcases lt_or_eq_of_le this with hh | hh
        · linarith
        · exact (hnk' (by linarith)).elim
      have := (hs r s hrs).mp this
      linarith
  · exact iff_of_false (hR k hk hkc r r).2.2 (hR l hl hlc r r).2.2
  · have hnk' := hnk s r hsr
    have hnl' := hnl s r hsr
    rw [compatible_iff_B hR hk hkc r s (by intro he; exact hnk' (by linarith)),
      compatible_iff_B hR hl hlc r s (by intro he; exact hnl' (by linarith))]
    simpa only [sub_lt_zero] using hs s r hsr

#print axioms compatible_iff_B
#print axioms same_relation_of_pair_signs
end BiasGrowth
```

### `BiasLowerScores.lean`

```lean
import BiasLowerResidues
import BiasTailSupport
import BiasSlopeUpper
import BiasRelationDetermination

namespace BiasGrowth

theorem distinguished_gap_lower {t a : ℕ} (ht : 0 < t) (ha : 10 ≤ a) (hat : a ≤ t) :
    (9/10:ℝ)*t-1 ≤ A (1/(t:ℝ)) - A ((a:ℝ)/t) := by
  have htr : (0:ℝ) < t := Nat.cast_pos.mpr ht
  have har : (10:ℝ) ≤ a := Nat.cast_le.mpr ha
  have htar : (a:ℝ) ≤ t := Nat.cast_le.mpr hat
  have h1 := (A_bounds (one_div_pos.mpr htr) ((div_le_one htr).mpr (by exact_mod_cast ht))).1
  have h2 := (A_bounds (div_pos (by linarith) htr) ((div_le_one htr).mpr htar)).2
  rw [one_div_one_div] at h1
  rw [one_div_div] at h2
  have h3 : (t:ℝ)/a ≤ (t:ℝ)/10 := by
    apply div_le_div_of_nonneg_left htr.le (by norm_num) har
  linarith

/-- Every sufficiently close right label is forced to invert at the distinguished q. -/
theorem forced_right_inversion {k t q s : ℕ}
    (ht : 40 < t) (hk : 2 ≤ k) (hcop : Nat.Coprime k t)
    (hq : q < t) (hqlo : 9*t ≤ 10*q) (hmod : Nat.ModEq t k q)
    (hqs : q < s) (hst : s ≤ t)
    (hnear : (k:ℝ)*((s:ℝ)-q) ≤ (7/20:ℝ)*(t:ℝ)^2) :
    B k t s < B k t q := by
  have ht0 : 0 < t := by omega
  have htr : (0:ℝ) < t := Nat.cast_pos.mpr ht0
  have hkr : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hs' : (s:ℝ) ≤ t := Nat.cast_le.mpr hst
  have hqs' : (q:ℝ) ≤ s := Nat.cast_le.mpr hqs.le
  have hqlo' : (9/10:ℝ) ≤ (q:ℝ)/t := by
    apply (le_div_iff₀ htr).mpr
    have : (9:ℝ)*t ≤ 10*q := by exact_mod_cast hqlo
    linarith
  have hupper := psi_slope_upper hqlo' (div_le_div_of_nonneg_right hqs' htr.le)
    ((div_le_one htr).mpr hs')
  have ha := right_label_inverse_ge_ten ht0 hq hqlo hcop hmod hqs hst
  have hgap := distinguished_gap_lower ht0 ha (rbar_le k t s ht0)
  have hqbar : rbar k t q = 1 :=
    rbar_distinguished ht0 hcop ((ZMod.natCast_eq_natCast_iff k q t).mpr hmod)
  have hupper' : (k:ℝ)*(psi ((s:ℝ)/t)-psi ((q:ℝ)/t)) ≤ (7/8:ℝ)*t := by
    have hm := mul_le_mul_of_nonneg_left hupper hkr.le
    have hm' := (mul_le_mul_of_nonneg_right hm htr.le)
    have hsimp : ((s:ℝ)/t-(q:ℝ)/t)*t = (s:ℝ)-q := by field_simp
    have hh : (5/2:ℝ)*k*((s:ℝ)/t-(q:ℝ)/t)*t =
        (5/2:ℝ)*k*((s:ℝ)-q) := by rw [mul_assoc, mul_assoc, hsimp]; ring
    have hm2 : (k:ℝ)*(psi ((s:ℝ)/t)-psi ((q:ℝ)/t))*t ≤
        (5/2:ℝ)*k*((s:ℝ)-q) := by nlinarith [hm']
    nlinarith
  have hdiff : (k:ℝ)*(psi ((s:ℝ)/t)-psi ((q:ℝ)/t)) <
      A (1/(t:ℝ)) - A ((rbar k t s:ℝ)/t) := by
    have : (40:ℝ) < t := Nat.cast_lt.mpr ht
    linarith
  unfold B
  rw [hqbar, Nat.cast_one]
  apply (lt_of_mul_lt_mul_left (a := (k:ℝ)))
  · have he (x : ℝ) : (k:ℝ)*(x/k) = x := mul_div_cancel₀ _ hkr.ne'
    rw [mul_add, mul_add, he, he]
    linarith
  · exact hkr.le

/-- A weak inversion at a later parameter is strict at every earlier parameter
in that residue class, so compatible tie choices cannot create new inversions. -/
theorem right_inversions_antitone {t k l : ℕ}
    (hkl : k < l) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (hkc : Nat.Coprime k t) (hlc : Nat.Coprime l t) (hmod : Nat.ModEq t k l)
    (R : ℕ → Fin t → Fin t → Prop) (hR : Compatible t R)
    (r s : Fin t) (hrs : r < s) (hinv : R l s r) : R k s r := by
  have hc := pairC_pos (r,s) hrs
  have hkr : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlr : (0:ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hklr : (k:ℝ) < l := Nat.cast_lt.mpr hkl
  have hweak : B l t (s.val+1) - B l t (r.val+1) ≤ 0 := by
    have hh := (hR l hl hlc s r).2.1 hinv
    rw [B_eq, B_eq]
    linarith
  rw [pair_difference (Nat.ModEq.refl l) (r,s)] at hweak
  have he (x : ℝ) (hx : x ≠ 0) : pairC (r,s) + pairD l t (r,s)/x =
      (pairC (r,s)*x+pairD l t (r,s))/x := by field_simp
  rw [he (l:ℝ) hlr.ne', div_le_iff₀ hlr] at hweak
  have hstrict : B k t (s.val+1) < B k t (r.val+1) := by
    apply sub_neg.mp
    rw [pair_difference hmod (r,s), he (k:ℝ) hkr.ne', div_lt_iff₀ hkr]
    nlinarith
  apply (hR k hk hkc s r).1
  rw [B_eq, B_eq] at hstrict
  linarith

#print axioms distinguished_gap_lower
#print axioms forced_right_inversion
#print axioms right_inversions_antitone
end BiasGrowth
```

### `BiasClassRecovery.lean`

```lean
import BiasLowerScores
import BiasInversions
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace BiasGrowth

theorem other_inverse_ge_two {t k : ℕ} (ht : 0 < t) (hk : Nat.Coprime k t)
    (q r : Fin t) (hmod : Nat.ModEq t k (q.val+1)) (hne : r ≠ q) :
    2 ≤ rbar k t (r.val+1) := by
  have hq := rbar_distinguished ht hk ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod)
  have hr := rbar_pos k t (r.val+1) ht
  by_contra h
  have he : rbar k t (r.val+1) = rbar k t (q.val+1) := by omega
  have h := rbar_injectiveOn ht hk
    (show r.val+1 ∈ Set.Icc 1 t from ⟨by omega, by omega⟩)
    (show q.val+1 ∈ Set.Icc 1 t from ⟨by omega, by omega⟩) he
  exact hne (Fin.ext (by omega))

theorem other_inversion_count_le {t k : ℕ} (ht : 0 < t) (hk : 2 ≤ k)
    (hcop : Nat.Coprime k t) (q r : Fin t) (hmod : Nat.ModEq t k (q.val+1))
    (hne : r ≠ q) (R : ℕ → Fin t → Fin t → Prop) (hR : Compatible t R) :
    rightInvCount (R k) r ≤ ⌊(t:ℝ)^2 / (3*k)⌋₊ := by
  classical
  have hkr : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ha := other_inverse_ge_two ht hcop q r hmod hne
  unfold rightInvCount
  apply le_trans (Finset.card_le_card_of_injOn (fun s : Fin t => s.val-r.val-1)
    (t := Finset.range ⌊(t:ℝ)^2/(3*k)⌋₊) ?_ ?_) (by rw [Finset.card_range])
  · intro s hs
    obtain ⟨_,hrs,hinv⟩ := Finset.mem_filter.mp hs
    have hweak : B k t (s.val+1) ≤ B k t (r.val+1) := by
      have h := (hR k hk hcop s r).2.1 hinv
      rw [B_eq,B_eq]; linarith
    have hsup := score_inversion_support (by omega) ht (by omega)
      (show r.val+1 ≤ s.val+1 by exact Nat.succ_le_succ hrs.le) (by omega) hweak
    have had : (2:ℝ) ≤ rbar k t (r.val+1) := by exact_mod_cast ha
    have hdcast : ((s.val+1:ℕ):ℝ)-(r.val+1:ℕ) = (s.val-r.val:ℕ) := by
      rw [Nat.cast_sub hrs.le]; push_cast; ring
    rw [hdcast] at hsup
    have hdnon : (0:ℝ) ≤ (s.val-r.val:ℕ) := Nat.cast_nonneg _
    have hd : ((s.val-r.val:ℕ):ℝ) ≤ (t:ℝ)^2/(3*k) := by
      apply (le_div_iff₀ (by positivity : (0:ℝ) < 3*k)).mpr
      nlinarith
    have hd' : s.val-r.val ≤ ⌊(t:ℝ)^2/(3*k)⌋₊ := (Nat.le_floor_iff (by positivity)).mpr hd
    change s.val-r.val-1 ∈ Finset.range _
    rw [Finset.mem_range]
    have : r.val < s.val := hrs
    omega
  · intro s hs z hz he
    have hs' := (Finset.mem_filter.mp hs).2.1
    have hz' := (Finset.mem_filter.mp hz).2.1
    change s.val-r.val-1 = z.val-r.val-1 at he
    apply Fin.ext
    change r.val < s.val at hs'
    change r.val < z.val at hz'
    omega

/-- The actual analytic class-recovery theorem, uniformly for compatible tie choices. -/
theorem class_recovery_general {t k : ℕ} (q : Fin t)
    (ht : 40 < t) (hk : 2 ≤ k) (hcop : Nat.Coprime k t)
    (hklarge : 20*t ≤ k) (hmod : Nat.ModEq t k (q.val+1))
    (hq0 : 9*t ≤ 10*(q.val+1)) (hq1 : 20*(q.val+1) ≤ 19*t)
    (hX : 60 < (t:ℝ)^2/k)
    (R : ℕ → Fin t → Fin t → Prop) (hR : Compatible t R) :
    ∀ r : Fin t, r ≠ q → rightInvCount (R k) r < rightInvCount (R k) q := by
  classical
  have ht0 : 0 < t := by omega
  have htr : (0:ℝ) < t := Nat.cast_pos.mpr ht0
  have hkr : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  let X : ℝ := (t:ℝ)^2/k
  let L : ℕ := ⌊(7/20:ℝ)*X⌋₊
  have hX0 : 0 < X := by dsimp [X]; positivity
  have hL : (L:ℝ) ≤ (7/20:ℝ)*X := Nat.floor_le (by positivity)
  have hklarge' : (20:ℝ)*t ≤ k := by exact_mod_cast hklarge
  have hXt : X ≤ (t:ℝ)/20 := by
    dsimp [X]
    apply (div_le_iff₀ hkr).mpr
    nlinarith
  have hq1' : (20:ℝ)*(q.val+1) ≤ 19*t := by exact_mod_cast hq1
  have hLspace : q.val+1+L ≤ t := by
    have : ((q.val+1+L:ℕ):ℝ) ≤ t := by push_cast; nlinarith
    exact_mod_cast this
  let f : Fin L → Fin t := fun i => ⟨q.val+(i.val+1), by have := i.isLt; omega⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Fin.ext
    have := congrArg Fin.val he
    dsimp [f] at this
    omega
  have hmem (i : Fin L) : f i ∈ rightInversions (R k) q := by
    have hi := i.isLt
    have hqs : q.val+1 < (f i).val+1 := by dsimp [f]; omega
    have hnear : (k:ℝ)*(((f i).val+1:ℕ):ℝ)-(k:ℝ)*(q.val+1:ℕ) ≤
        (7/20:ℝ)*(t:ℝ)^2 := by
      have hLd : (k:ℝ)*(L:ℝ) ≤ (7/20:ℝ)*(t:ℝ)^2 := by
        have := mul_le_mul_of_nonneg_left hL hkr.le
        dsimp [X] at this
        field_simp at this
        nlinarith
      have hid : ((f i).val+1:ℕ) ≤ q.val+1+L := by dsimp [f]; omega
      have hid' : (((f i).val+1:ℕ):ℝ) ≤ (q.val+1:ℕ)+(L:ℝ) := by exact_mod_cast hid
      nlinarith
    have hscore := forced_right_inversion ht hk hcop
      (q := q.val+1) (s := (f i).val+1) (by omega) hq0 hmod hqs
      (by have := (f i).isLt; omega) (by nlinarith [hnear])
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, (hR k hk hcop (f i) q).1 ?_⟩
    · change q.val < q.val+(i.val+1); omega
    · rw [B_eq,B_eq] at hscore; linarith
  have hcount : L ≤ rightInvCount (R k) q := by
    have hh := Finset.card_le_card_of_injOn f (s := Finset.univ)
      (t := rightInversions (R k) q) (fun i _ => hmem i) (fun _ _ _ _ he => hf he)
    simpa [rightInvCount] using hh
  have hLgt : ⌊(t:ℝ)^2/(3*k)⌋₊ < L := by
    have hfloor := Nat.lt_floor_add_one ((7/20:ℝ)*X)
    have hfloor2 := Nat.floor_le (show 0 ≤ (t:ℝ)^2/(3*k) by positivity)
    have he : (t:ℝ)^2/(3*k) = X/3 := by dsimp [X]; field_simp
    have hfloor3 := hfloor2.trans_eq he
    change (7/20:ℝ)*X < (L:ℝ)+1 at hfloor
    have : (⌊(t:ℝ)^2/(3*k)⌋₊:ℝ) < L := by change 60 < X at hX; linarith
    exact_mod_cast this
  intro r hne
  exact lt_of_le_of_lt (other_inversion_count_le ht0 hk hcop q r hmod hne R hR)
    (lt_of_lt_of_le hLgt hcount)

#print axioms other_inverse_ge_two
#print axioms other_inversion_count_le
#print axioms class_recovery_general
end BiasGrowth
```

### `BiasNatPatterns.lean`

```lean
import BiasTailRange
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace BiasGrowth

/-- Natural parameters, with no upper cutoff, retain the ties-allowed count. -/
theorem nat_reciprocal_patterns_ncard_le {ι β : Type*}
    [DecidableEq ι] [DecidableEq β]
    (U : Finset ι) (A : Set ℕ) (c d : ι → ℝ) (R : ℕ → β)
    (hfin : (R '' A).Finite) (hc : ∀ i ∈ U, 0 < c i)
    (hA : ∀ x ∈ A, 0 < x)
    (hdet : ∀ x ∈ A, ∀ y ∈ A,
      (∀ i ∈ U, c i + d i / (x : ℝ) ≠ 0) →
      (∀ i ∈ U, c i + d i / (y : ℝ) ≠ 0) →
      (∀ i ∈ U, (c i + d i / (x : ℝ) < 0 ↔ c i + d i / (y : ℝ) < 0)) →
      R x = R y) :
    (R '' A).ncard ≤ 2 * U.card + 1 := by
  classical
  apply image_ncard_le_of_finset_bound A R _ hfin
  intro J hJ
  let K : Finset ℝ := J.image (fun n : ℕ => (n : ℝ))
  let S : ℝ → β := fun x => R ⌊x⌋₊
  have hfloor (n : ℕ) : S (n : ℝ) = R n := by simp [S]
  have he : K.image S = J.image R := by
    ext b
    simp only [K, Finset.mem_image]
    constructor
    · rintro ⟨x, ⟨n, hn, rfl⟩, hb⟩
      exact ⟨n, hn, by simpa [hfloor] using hb⟩
    · rintro ⟨n, hn, hb⟩
      exact ⟨n, ⟨n, hn, rfl⟩, by simpa [hfloor] using hb⟩
  rw [← he]
  apply reciprocal_patterns_card_le U K c d S hc
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    exact Nat.cast_pos.mpr (hA n (hJ n hn))
  · intro x hx y hy hn hm hs
    obtain ⟨n, hn', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨m, hm', rfl⟩ := Finset.mem_image.mp hy
    simpa only [hfloor] using hdet n (hJ n hn') m (hJ m hm') hn hm hs

#print axioms nat_reciprocal_patterns_ncard_le
end BiasGrowth
```

### `BiasMesh.lean`

```lean
import BiasNatPatterns
import Mathlib.Tactic.Ring

namespace BiasGrowth

/-- A mesh with jumps at most δ cannot skip an interval of length δ. -/
theorem mesh_point (y : ℕ → ℝ) (N : ℕ) (δ z : ℝ)
    (hy0 : y 0 ≤ z) (hyN : z < y N)
    (hstep : ∀ j, j < N → y (j+1) ≤ y j + δ) :
    ∃ j, 0 < j ∧ j ≤ N ∧ z < y j ∧ y j ≤ z+δ := by
  have hex : ∃ j, j ≤ N ∧ z < y j := ⟨N,le_rfl,hyN⟩
  let j := Nat.find hex
  have hj : j ≤ N ∧ z < y j := Nat.find_spec hex
  have hj0 : 0 < j := by
    by_contra h
    have : j=0 := by omega
    rw [this] at hj
    linarith
  have hprev : y (j-1) ≤ z := by
    by_contra h
    have hbad : j ≤ j-1 := Nat.find_min' hex ⟨by omega,lt_of_not_ge h⟩
    omega
  have hstep' := hstep (j-1) (by omega)
  have he : j-1+1=j := by omega
  rw [he] at hstep'
  exact ⟨j,hj0,hj.1,hj.2,by linarith⟩

/-- An open mesh interval of width more than Aδ contains a point whose
injective positive integer label is at least A. -/
theorem mesh_avoids_small_labels (y : ℕ → ℝ) (b : ℕ → ℕ) (N A : ℕ) (δ u v : ℝ)
    (hA : 0 < A) (hδ : 0 < δ) (hy0 : y 0 ≤ u) (hyN : v < y N)
    (hstep : ∀ j, j < N → y (j+1) ≤ y j+δ)
    (hwidth : (A:ℝ)*δ < v-u)
    (hbpos : ∀ j, 0 < j → j ≤ N → 1 ≤ b j)
    (hbinj : ∀ i, 0 < i → i ≤ N → ∀ j, 0 < j → j ≤ N → b i = b j → i=j) :
    ∃ j, 0 < j ∧ j ≤ N ∧ u < y j ∧ y j < v ∧ A ≤ b j := by
  classical
  have hex (i : Fin A) : ∃ j, 0 < j ∧ j ≤ N ∧ u+(i.val:ℝ)*δ < y j ∧
      y j ≤ u+(i.val:ℝ)*δ+δ := by
    apply mesh_point y N δ (u+(i.val:ℝ)*δ)
    · have : (0:ℝ) ≤ (i.val:ℝ)*δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
      linarith
    · have hi : (i.val:ℝ) < A := Nat.cast_lt.mpr i.isLt
      nlinarith
    · exact hstep
  choose f hf0 hfN hflo hfhi using hex
  have hfinj : Function.Injective f := by
    intro i j he
    by_contra hne
    have hij : i.val ≠ j.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hij with h | h
    · have hh : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast h
      have hprod := mul_le_mul_of_nonneg_right hh hδ.le
      have hi := hfhi i
      have hj := hflo j
      rw [he] at hi
      nlinarith
    · have hh : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast h
      have hprod := mul_le_mul_of_nonneg_right hh hδ.le
      have hi := hfhi j
      have hj := hflo i
      rw [← he] at hi
      nlinarith
  by_contra hnone
  have hall (i : Fin A) : b (f i) < A := by
    by_contra hn
    apply hnone
    refine ⟨f i,hf0 i,hfN i,?_,?_,by omega⟩
    · have hh := hflo i
      have hprod := mul_nonneg (Nat.cast_nonneg i.val) hδ.le
      linarith
    · have hh := hfhi i
      have hi : (i.val:ℝ)+1 ≤ A := by exact_mod_cast i.isLt
      have hprod := mul_le_mul_of_nonneg_right hi hδ.le
      nlinarith
  let g : Fin A → Fin (A-1) := fun i => ⟨b (f i)-1, by
    have := hall i
    have := hbpos (f i) (hf0 i) (hfN i)
    omega⟩
  have hginj : Function.Injective g := by
    intro i j he
    apply hfinj
    apply hbinj (f i) (hf0 i) (hfN i) (f j) (hf0 j) (hfN j)
    have h := congrArg Fin.val he
    have hi := hbpos (f i) (hf0 i) (hfN i)
    have hj := hbpos (f j) (hf0 j) (hfN j)
    dsimp [g] at h
    omega
  have hh := Fintype.card_le_of_injective g hginj
  simp only [Fintype.card_fin] at hh
  omega

#print axioms mesh_point
#print axioms mesh_avoids_small_labels
end BiasGrowth
```

### `BiasSwitchBounds.lean`

```lean
import BiasNatPatterns
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace BiasGrowth

/-- Numerical mesh bounds, separated from the special functions. -/
theorem switch_scalar_bounds (t m q a : ℝ) (hm : 20 ≤ m)
    (hq : 0 ≤ q) (hqt : q ≤ t) (ht : 100*(m+2)^3 < t)
    (ha0 : t-1 ≤ a) (ha1 : a ≤ t) :
    let k := m*t+q
    let A := 4*(m+2)
    0 ≤ a/(k+t) ∧ (a-t/A)/k < (3/40:ℝ) ∧
      A*(5/(2*t)) < (a-t/A)/k-a/(k+t) := by
  dsimp only
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m+2 := by linarith
  have ht4 : 4 < t := by nlinarith [sq_nonneg (m+2)]
  have ht0 : 0 < t := by linarith
  have hk : 0 < m*t+q := by positivity
  have hkt : 0 < m*t+q+t := by positivity
  have hA : 0 < 4*(m+2) := by positivity
  have ha : 0 < a := by linarith
  constructor
  · positivity
  constructor
  · have h1 : (a-t/(4*(m+2)))/(m*t+q) ≤ t/(m*t+q) := by
      apply div_le_div_of_nonneg_right _ hk.le
      have : 0 ≤ t/(4*(m+2)) := by positivity
      linarith
    have h2 : t/(m*t+q) ≤ 1/m := by
      apply (div_le_div_iff₀ hk hm0).mpr
      nlinarith
    have h3 : 1/m ≤ (1/20:ℝ) := by
      apply (div_le_iff₀ hm0).mpr
      linarith
    linarith
  have h1 : (3/4:ℝ)/(m+2) ≤ a/(m*t+q+t) := by
    apply (div_le_div_iff₀ hm2 hkt).mpr
    have h := mul_nonneg (show 0 ≤ a-(t-1) by linarith) hm2.le
    nlinarith
  have h2 : (1/2:ℝ)/(m+2) ≤ a/(m*t+q+t)-1/(4*(m+2)) := by
    have he : 1/(4*(m+2)) = (1/4:ℝ)/(m+2) := by field_simp
    rw [he]
    have he2 : (3/4:ℝ)/(m+2)-(1/4:ℝ)/(m+2) = (1/2:ℝ)/(m+2) := by ring
    linarith
  have h3 : 1/(m+2) ≤ t/(m*t+q) := by
    apply (div_le_div_iff₀ hm2 hk).mpr
    nlinarith
  have h4 : (1/2:ℝ)/(m+2)^2 ≤
      (t/(m*t+q))*(a/(m*t+q+t)-1/(4*(m+2))) := by
    have hh := mul_le_mul h3 h2 (by positivity : (0:ℝ) ≤ (1/2)/(m+2))
      (by positivity : (0:ℝ) ≤ t/(m*t+q))
    convert hh using 1; field_simp
  have he : (a-t/(4*(m+2)))/(m*t+q)-a/(m*t+q+t) =
      (t/(m*t+q))*(a/(m*t+q+t)-1/(4*(m+2))) := by
    field_simp
    ring
  rw [he]
  apply lt_of_lt_of_le _ h4
  apply (lt_div_iff₀ (sq_pos_of_pos hm2)).mpr
  have he' : 4*(m+2)*(5/(2*t))*(m+2)^2 = (10*(m+2)^3)/t := by
    field_simp
    ring
  rw [he']
  apply (div_lt_iff₀ ht0).mpr
  nlinarith [sq_nonneg (m+2)]

#print axioms switch_scalar_bounds
end BiasGrowth
```

### `BiasConsecutiveSwitch.lean`

```lean
import BiasClassRecovery
import BiasMesh
import BiasSwitchBounds

namespace BiasGrowth

/-- The literal mesh/exceptions switch, including strict scores at both ends. -/
theorem consecutive_switch_general {t k m : ℕ} (q : Fin t)
    (hm : 20 ≤ m) (ht : 100*(m+2)^3 < t)
    (hq0 : 9*t ≤ 10*(q.val+1)) (hq1 : 20*(q.val+1) ≤ 19*t)
    (hkeq : k = m*t+(q.val+1)) (hcop : Nat.Coprime k t)
    (hlcop : Nat.Coprime (k+t) t)
    (R : ℕ → Fin t → Fin t → Prop) (hR : Compatible t R) :
    rightInvCount (R (k+t)) q < rightInvCount (R k) q := by
  classical
  have ht40 : 40 < t := by nlinarith [sq_nonneg (m+2)]
  have ht0 : 0 < t := by omega
  have htr : (0:ℝ) < t := Nat.cast_pos.mpr ht0
  have hk2 : 2 ≤ k := by rw [hkeq]; nlinarith
  have hkr : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlr : (0:ℝ) < k+t := by positivity
  have hqnat : q.val+1 < t := by omega
  let h : ℕ := t-(q.val+1)
  let N : ℕ := 4*(m+2)
  let a : ℝ := A (1/(t:ℝ))
  let u := a/((k:ℝ)+t)
  let v := (a-(t:ℝ)/N)/k
  let δ := 5/(2*(t:ℝ))
  let y : ℕ → ℝ := fun j => psi (((q.val+1+j:ℕ):ℝ)/t)-psi (((q.val+1:ℕ):ℝ)/t)
  let b : ℕ → ℕ := fun j => rbar k t (q.val+1+j)
  have hab := A_bounds (one_div_pos.mpr htr) ((div_le_one htr).mpr (by exact_mod_cast ht0))
  rw [one_div_one_div] at hab
  have hscalar := switch_scalar_bounds (t:ℝ) m (q.val+1) a
    (by exact_mod_cast hm) (by positivity) (by exact_mod_cast q.isLt)
    (by exact_mod_cast ht) hab.1 hab.2
  have hkeqr : (k:ℝ) = (m:ℝ)*t+(q.val+1) := by exact_mod_cast hkeq
  have hNr : (N:ℝ) = 4*((m:ℝ)+2) := by dsimp [N]; push_cast; ring
  rw [← hkeqr, ← hNr] at hscalar
  change 0 ≤ u ∧ v < (3/40:ℝ) ∧ (N:ℝ)*δ < v-u at hscalar
  have hqlo : (9/10:ℝ) ≤ ((q.val+1:ℕ):ℝ)/t := by
    apply (le_div_iff₀ htr).mpr
    have : (9:ℝ)*t ≤ 10*(q.val+1) := by exact_mod_cast hq0
    push_cast
    linarith
  have hyh : (3/40:ℝ) ≤ y h := by
    have hsum : q.val+1+h=t := by dsimp [h]; omega
    have hlower := psi_slope_lower (x := ((q.val+1:ℕ):ℝ)/t) (y := 1)
      (by positivity) ((div_le_one htr).mpr (by exact_mod_cast q.isLt)) le_rfl
    have hqhi : (20:ℝ)*(q.val+1) ≤ 19*t := by exact_mod_cast hq1
    have hd : (1-((q.val+1:ℕ):ℝ)/t)*t = (t:ℝ)-(q.val+1)  := by push_cast; field_simp
    have hd' := mul_le_mul_of_nonneg_right hlower htr.le
    dsimp [y]
    rw [hsum, div_self htr.ne']
    push_cast at hd hd' ⊢
    have hdeq : (3/2:ℝ)*(1-((q.val:ℝ)+1)/t)*t = (3/2:ℝ)*(t-((q.val:ℝ)+1)) := by rw [mul_assoc,hd]
    nlinarith only [htr,hqhi,hd',hdeq]
  have hstep (j : ℕ) (hj : j < h) : y (j+1) ≤ y j+δ := by
    have hjt : q.val+1+(j+1) ≤ t := by dsimp [h] at hj; omega
    have hxlo : (9/10:ℝ) ≤ ((q.val+1+j:ℕ):ℝ)/t := by
      apply le_trans hqlo
      apply div_le_div_of_nonneg_right _ htr.le
      exact_mod_cast (by omega : q.val+1 ≤ q.val+1+j)
    have hupper := psi_slope_upper hxlo
      (y := ((q.val+1+(j+1):ℕ):ℝ)/t)
      (div_le_div_of_nonneg_right (by exact_mod_cast (by omega : q.val+1+j ≤ q.val+1+(j+1))) htr.le)
      ((div_le_one htr).mpr (by exact_mod_cast hjt))
    have he : ((q.val+1+(j+1):ℕ):ℝ)/t-((q.val+1+j:ℕ):ℝ)/t=1/(t:ℝ) := by
      push_cast; ring
    rw [he] at hupper
    have he' : (5/2:ℝ)*(1/(t:ℝ)) = 5/(2*(t:ℝ)) := by ring
    rw [he'] at hupper
    dsimp [y,δ]
    linarith
  obtain ⟨j,hj0,hjh,hju,hjv,hja⟩ := mesh_avoids_small_labels y b h N δ u v
    (by dsimp [N]; omega) (by dsimp [δ]; positivity)
    (by dsimp [y]; simpa using hscalar.1) (lt_of_lt_of_le hscalar.2.1 hyh) hstep hscalar.2.2
    (fun j _ _ => rbar_pos _ _ _ ht0) (by
      intro i hi hih j hj hjh he
      have he' := rbar_injectiveOn ht0 hcop
        (show q.val+1+i ∈ Set.Icc 1 t from ⟨by omega,by dsimp [h] at hih; omega⟩)
        (show q.val+1+j ∈ Set.Icc 1 t from ⟨by omega,by dsimp [h] at hjh; omega⟩) he
      omega)
  let s : Fin t := ⟨q.val+j,by dsimp [h] at hjh; omega⟩
  have hqs : q < s := by change q.val < q.val+j; omega
  have hslabel : s.val+1=q.val+1+j := by dsimp [s]; omega
  have hmod : Nat.ModEq t k (q.val+1) := by
    rw [hkeq]
    change (m*t+(q.val+1))%t=(q.val+1)%t
    simp [Nat.add_mod]
  have hmod' : Nat.ModEq t (k+t) k := by
    change (k+t)%t=k%t
    simp
  have hqbar := rbar_distinguished ht0 hcop ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod)
  have hqbar' := rbar_distinguished ht0 hlcop ((ZMod.natCast_eq_natCast_iff _ _ _).mpr (hmod'.trans hmod))
  have hbs : rbar (k+t) t (s.val+1) = rbar k t (s.val+1) := rbar_congr hmod'
  have hba : (N:ℝ) ≤ rbar k t (s.val+1) := by rw [hslabel]; exact_mod_cast hja
  have hNpos : (0:ℝ) < N := by dsimp [N]; positivity
  have hapos : (0:ℝ) < rbar k t (s.val+1) := by exact_mod_cast (rbar_pos k t (s.val+1) ht0)
  have hAa := A_bounds (div_pos hapos htr) ((div_le_one htr).mpr
    (by exact_mod_cast (rbar_le k t (s.val+1) ht0)))
  rw [one_div_div] at hAa
  have hAupper : A ((rbar k t (s.val+1):ℝ)/t) ≤ (t:ℝ)/N :=
    hAa.2.trans (div_le_div_of_nonneg_left htr.le hNpos hba)
  have hAnon : 0 ≤ A ((rbar k t (s.val+1):ℝ)/t) :=
    A_nonneg (div_pos hapos htr) ((div_le_one htr).mpr (by exact_mod_cast (rbar_le k t (s.val+1) ht0)))
  have hstrict : B k t (s.val+1) < B k t (q.val+1) := by
    have hmul := (lt_div_iff₀ hkr).mp hjv
    dsimp [v,y,a] at hmul
    unfold B
    rw [hqbar,Nat.cast_one,hslabel]
    apply (mul_lt_mul_iff_right₀ hkr).mp
    rw [mul_add,mul_add,mul_div_cancel₀ _ hkr.ne',mul_div_cancel₀ _ hkr.ne']
    rw [hslabel] at hAupper
    nlinarith only [hmul,hAupper]
  have hreverse : B (k+t) t (q.val+1) < B (k+t) t (s.val+1) := by
    have hmul := (div_lt_iff₀ hlr).mp hju
    dsimp [u,y,a] at hmul
    unfold B
    rw [hqbar',hbs,Nat.cast_one]
    have he1 : ((k+t:ℕ):ℝ)=(k:ℝ)+t := by push_cast; rfl
    rw [he1]
    apply (mul_lt_mul_iff_right₀ hlr).mp
    rw [mul_add,mul_add,mul_div_cancel₀ _ hlr.ne',mul_div_cancel₀ _ hlr.ne']
    rw [hslabel]
    rw [hslabel] at hAnon
    nlinarith only [hmul,hAnon]
  apply rightInvCount_strict_drop
  · intro z hqz hz
    exact right_inversions_antitone (by omega) hk2 (by omega) hcop hlcop hmod'.symm R hR q z hqz hz
  · refine ⟨s,hqs,(hR k hk2 hcop s q).1 ?_,?_⟩
    · rw [B_eq,B_eq] at hstrict; linarith
    · intro hh
      have hw := (hR (k+t) (by omega) hlcop s q).2.1 hh
      rw [B_eq,B_eq] at hreverse
      linarith

#print axioms consecutive_switch_general
end BiasGrowth
```

### `BiasLiteralTail.lean`

```lean
import BiasNatPatterns
import BiasTailSupport
import BiasRelationDetermination

namespace BiasGrowth

def tailParams (q t H : ℕ) : Set ℕ :=
  {k | 2 ≤ k ∧ Nat.Coprime k t ∧ Nat.ModEq t k q ∧ (t : ℝ)^2 ≤ (k : ℝ)*H}

/-- Literal application to all admissible integer parameters in one residue class.
Arbitrary compatible tie decisions are included. -/
theorem literal_tail_count {q t H : ℕ} (ht : 0 < t) (hq : Nat.Coprime q t)
    (R : ℕ → Fin t → Fin t → Prop) (hR : Compatible t R) :
    (R '' tailParams q t H).ncard ≤ 2 * (H*H) + 1 := by
  classical
  apply le_trans (nat_reciprocal_patterns_ncard_le (tailPairs q t H)
    (tailParams q t H) pairC (pairD q t) R (Set.toFinite _) ?_ ?_ ?_)
    (by have := tailPairs_card_le (H := H) ht hq; omega)
  · intro p hp
    apply pairC_pos
    have : p.1 < p.2 ∧ rbar q t (p.1.val+1) ≤ H ∧ p.2.val-p.1.val ≤ H := by
      simpa [tailPairs] using hp
    exact this.1
  · intro k hk
    exact lt_of_lt_of_le (by decide : 0 < 2) hk.1
  · intro k hk l hl hnk hnl hs
    have hpos (a : ℕ) (ha : a ∈ tailParams q t H) (r s : Fin t) (hrs : r < s)
        (hn : ∀ p ∈ tailPairs q t H, pairC p + pairD q t p / (a : ℝ) ≠ 0) :
        B a t (s.val+1) - B a t (r.val+1) ≠ 0 := by
      by_cases hp : (r,s) ∈ tailPairs q t H
      · rw [pair_difference ha.2.2.1 (r,s)]
        exact hn (r,s) hp
      · have hstrict : B a t (r.val+1) < B a t (s.val+1) := by
          by_contra h
          exact hp (inversion_mem_tailPairs ht (lt_of_lt_of_le (by decide : 0 < 2) ha.1) ha.2.2.1 ha.2.2.2
            (r,s) hrs (le_of_not_gt h))
        linarith
    apply same_relation_of_pair_signs hR hk.1 hl.1 hk.2.1 hl.2.1
      (hpos k hk · · · hnk) (hpos l hl · · · hnl)
    intro r s hrs
    by_cases hp : (r,s) ∈ tailPairs q t H
    · rw [pair_difference hk.2.2.1 (r,s), pair_difference hl.2.2.1 (r,s)]
      exact hs (r,s) hp
    · have hn (a : ℕ) (ha : a ∈ tailParams q t H) :
          ¬ (B a t (s.val+1) - B a t (r.val+1) < 0) := by
        intro h
        exact hp (inversion_mem_tailPairs ht (lt_of_lt_of_le (by decide : 0 < 2) ha.1) ha.2.2.1 ha.2.2.2
          (r,s) hrs (by linarith))
      exact iff_of_false (hn k hk) (hn l hl)

#print axioms literal_tail_count
end BiasGrowth
```

### `BiasResidueSmall.lean`

```lean
import BiasDefinitions
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Tactic.Linarith

namespace BiasGrowth

def smallParams (q t H : ℕ) : Set ℕ :=
  {k | 2 ≤ k ∧ Nat.Coprime k t ∧ Nat.ModEq t k q ∧ (k : ℝ)*H < (t : ℝ)^2}

theorem smallParams_finite {q t H : ℕ} (hH : 0 < H) :
    (smallParams q t H).Finite := by
  apply (Set.finite_Iio (t*t)).subset
  intro k hk
  have hh : k*H < t*t := by
    exact_mod_cast (show (k : ℝ)*H < (t : ℝ)*t by nlinarith [hk.2.2.2])
  have : k ≤ k*H := Nat.le_mul_of_pos_right k hH
  exact lt_of_le_of_lt this hh

/-- Count the initial segment of a residue class using k/t, without enumerating k. -/
theorem small_class_count {q t H : ℕ} (ht : 0 < t) (hH : 0 < H) :
    (smallParams q t H).ncard ≤ t / H + 1 := by
  classical
  apply le_trans (Set.ncard_le_ncard_of_injOn (fun k : ℕ => k/t)
    (t := (↑(Finset.range (t/H+1)) : Set ℕ)) ?_ ?_ (Set.toFinite _))
    (by rw [Set.ncard_coe_finset, Finset.card_range])
  · intro k hk
    change k/t ∈ Finset.range (t/H+1)
    rw [Finset.mem_range]
    have hkt : k * H < t*t := by exact_mod_cast (show (k : ℝ)*H < (t : ℝ)*t by nlinarith [hk.2.2.2])
    have hdiv : (k/t)*H < t := by
      have hle : t * ((k/t)*H) ≤ k*H := by
        calc
          t * ((k/t)*H) = (k/t*t)*H := by ring
          _ ≤ k*H := Nat.mul_le_mul_right H (Nat.div_mul_le_self k t)
      nlinarith
    have : k/t ≤ t/H := (Nat.le_div_iff_mul_le hH).mpr hdiv.le
    omega
  · intro k hk l hl he
    have hmod : k % t = l % t := hk.2.2.1.trans hl.2.2.1.symm
    change k/t = l/t at he
    have hk' := Nat.mod_add_div k t
    rw [he] at hk'
    have hl' := Nat.mod_add_div l t
    omega

#print axioms small_class_count
end BiasGrowth
```

### `BiasUpperCount.lean`

```lean
import BiasLiteralTail
import BiasResidueSmall

namespace BiasGrowth

def classParams (q t : ℕ) : Set ℕ :=
  {k | 2 ≤ k ∧ Nat.Coprime k t ∧ Nat.ModEq t k q}

theorem class_order_count {q t H : ℕ} (ht : 0 < t) (hH : 0 < H)
    (hq : Nat.Coprime q t) (R : ℕ → Fin t → Fin t → Prop) (hR : Compatible t R) :
    (R '' classParams q t).ncard ≤ t/H + 2*(H*H) + 2 := by
  have he : classParams q t = smallParams q t H ∪ tailParams q t H := by
    ext k
    simp only [classParams, smallParams, tailParams, Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro h
      rcases lt_or_ge ((k : ℝ)*H) ((t : ℝ)^2) with hc | hc
      · exact Or.inl ⟨h.1, h.2.1, h.2.2, hc⟩
      · exact Or.inr ⟨h.1, h.2.1, h.2.2, hc⟩
    · rintro (h | h) <;> exact ⟨h.1,h.2.1,h.2.2.1⟩
  rw [he, Set.image_union]
  have hs : (R '' smallParams q t H).ncard ≤ t/H+1 := by
    exact le_trans (Set.ncard_image_le (smallParams_finite hH)) (small_class_count ht hH)
  have hb := literal_tail_count (H := H) ht hq R hR
  have hu := Set.ncard_union_le (R '' smallParams q t H) (R '' tailParams q t H)
  omega

/-- A fixed-cutoff quantitative estimate; adequate for the upper little-o limit. -/
theorem orderCount_upper_fixed (t H : ℕ) (ht : 2 ≤ t) (hH : 0 < H)
    (R : ℕ → Fin t → Fin t → Prop) (hR : Compatible t R) :
    orderCount t R ≤ Nat.totient t * (t/H + 2*(H*H) + 2) := by
  classical
  let Q := (Finset.range t).filter (fun q => Nat.Coprime t q)
  have hcover : orderings t R ⊆ ⋃ q ∈ Q, R '' classParams q t := by
    rintro S ⟨k,hk,hcop,rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨k%t, Set.mem_iUnion.mpr ⟨?_, k, ⟨hk,hcop,?_⟩,rfl⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt k (by omega)),
        by rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, ← Nat.gcd_rec]; exact hcop.symm.gcd_eq_one⟩
    · exact Nat.mod_mod k t |>.symm
  change (orderings t R).ncard ≤ _
  calc
    _ ≤ (⋃ q ∈ Q, R '' classParams q t).ncard := Set.ncard_le_ncard hcover
    _ ≤ ∑ q ∈ Q, (R '' classParams q t).ncard := Q.set_ncard_biUnion_le _
    _ ≤ ∑ _q ∈ Q, (t/H + 2*(H*H) + 2) := by
      apply Finset.sum_le_sum
      intro q hq
      exact class_order_count (by omega) hH (Finset.mem_filter.mp hq).2.symm R hR
    _ = Nat.totient t * (t/H + 2*(H*H) + 2) := by
      simp [Q, ← Nat.totient_eq_card_coprime, Nat.mul_comm]

#print axioms class_order_count
#print axioms orderCount_upper_fixed
end BiasGrowth
```

### `BiasUpperAsymptotic.lean`

```lean
import BiasUpperCount

open Filter Asymptotics
namespace BiasGrowth

/-- The upper half of the required endpoint, for every compatible family. -/
theorem conjecture_355348_upper (R : ∀ t : ℕ, ℕ → Fin t → Fin t → Prop)
    (hR : ∀ t, 2 ≤ t → Compatible t (R t)) :
    (fun t : ℕ => (orderCount t (R t) : ℝ) / Nat.totient t) =o[atTop]
      (fun t => (t : ℝ)) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  obtain ⟨H, hH⟩ := exists_nat_gt (2/c)
  have hHpos : 0 < H := by
    have : (0 : ℝ) < H := lt_trans (div_pos (by norm_num) hc) hH
    exact_mod_cast this
  have hHr : (0 : ℝ) < H := Nat.cast_pos.mpr hHpos
  have hch : 2 < c * H := by
    have := (div_lt_iff₀ hc).mp hH
    nlinarith
  let K : ℝ := 2*(H:ℝ)^2+2
  obtain ⟨T, hT⟩ := exists_nat_gt (2*K/c)
  filter_upwards [eventually_ge_atTop (max T 2)] with t ht
  have ht2 : 2 ≤ t := le_trans (le_max_right _ _) ht
  have htt : T ≤ t := le_trans (le_max_left _ _) ht
  have htr : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hphi : (0 : ℝ) < Nat.totient t := by
    exact_mod_cast (Nat.totient_pos.mpr (show 0 < t by omega))
  have hb := orderCount_upper_fixed t H ht2 hHpos (R t) (hR t ht2)
  have hbr : (orderCount t (R t) : ℝ) ≤
      (Nat.totient t : ℝ) * ((t/H : ℕ) + K) := by
    dsimp [K]
    norm_cast
    convert hb using 1; ring
  have hd : ((t/H : ℕ) : ℝ) ≤ (t:ℝ)/H := by
    apply (le_div_iff₀ hHr).mpr
    exact_mod_cast (Nat.div_mul_le_self t H)
  have hsmall : (t:ℝ)/H ≤ c/2*t := by
    apply (div_le_iff₀ hHr).mpr
    have hm := mul_le_mul_of_nonneg_right hch.le htr.le
    nlinarith
  have hK : K ≤ c/2*t := by
    have htt' : (T:ℝ) ≤ t := Nat.cast_le.mpr htt
    have := (div_lt_iff₀ hc).mp hT
    nlinarith
  have hfinal : (orderCount t (R t) : ℝ) / Nat.totient t ≤ c*t := by
    have hquot : (orderCount t (R t) : ℝ) / Nat.totient t ≤ (t/H : ℕ) + K :=
      (div_le_iff₀ hphi).mpr (by nlinarith [hbr])
    linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg
    (show 0 ≤ (orderCount t (R t) : ℝ) / Nat.totient t by positivity),
    abs_of_nonneg (show (0:ℝ) ≤ t by positivity)]
  exact hfinal

/-- The strict-score specialization of the independently proved upper half. -/
theorem conjecture_355348_strict_upper :
    let R := fun t k (r s : Fin t) => psiKT k t (s.val+1) < psiKT k t (r.val+1)
    (fun t : ℕ => (orderCount t (R t) : ℝ) / Nat.totient t) =o[atTop]
      (fun t => (t : ℝ)) := by
  exact conjecture_355348_upper (fun t => strictFamily t) (fun t _ => compatible_strict t)

#check conjecture_355348_upper
#check conjecture_355348_strict_upper
#print axioms conjecture_355348_upper
#print axioms conjecture_355348_strict_upper
end BiasGrowth
```

### `BiasSieveIdentity.lean`

```lean
import BiasDefinitions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Nat.Factorization.Basic

namespace BiasGrowth

theorem subset_primes_prod_dvd {P S : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (hS : S ⊆ P) (q : ℕ) : (∏ p ∈ S, p) ∣ q ↔ ∀ p ∈ S, p ∣ q := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem (fun p => p) hp).trans h
  · intro h
    apply Finset.prod_dvd_of_isRelPrime _ h
    intro p hp r hr hne
    apply Nat.coprime_iff_isRelPrime.mp
    exact (hP p (hS hp)).coprime_iff_not_dvd.mpr (by
      intro hd
      exact hne ((Nat.dvd_prime (hP r (hS hr))).mp hd |>.resolve_left (hP p (hS hp)).ne_one))

theorem sieve_indicator (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (q : ℕ) :
    (if ∀ p ∈ P, ¬p ∣ q then (1:ℝ) else 0) =
      ∑ S ∈ P.powerset, (-1:ℝ)^S.card * (if (∏ p ∈ S, p) ∣ q then 1 else 0) := by
  classical
  have hbool (S : Finset ℕ) (f : ℕ → Prop) [DecidablePred f] :
      (∏ p ∈ S, (if f p then (1:ℝ) else 0)) = if ∀ p ∈ S, f p then 1 else 0 := by
    by_cases h : ∀ p ∈ S, f p
    · rw [ite_eq_left h]
      apply Finset.prod_eq_one
      intro p hp
      exact ite_eq_left (h p hp)
    · push Not at h
      obtain ⟨p,hp,hpf⟩ := h
      rw [ite_eq_right (by push Not; exact ⟨p,hp,hpf⟩)]
      exact Finset.prod_eq_zero hp (ite_eq_right hpf)
  have he : (∏ p ∈ P, (1-(if p ∣ q then (1:ℝ) else 0))) =
      if ∀ p ∈ P, ¬p ∣ q then 1 else 0 := by
    convert hbool P (fun p => ¬p ∣ q) using 1
    apply Finset.prod_congr rfl
    intro p _
    by_cases h : p ∣ q <;> simp [h]
  rw [← he,Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.prod_const_one, mul_one,hbool]
  simp only [subset_primes_prod_dvd hP (Finset.mem_powerset.mp hS) q]

/-- Exact inclusion-exclusion for a finite interval, with the literal divisibility tests. -/
theorem sieve_interval_identity (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (x : ℕ) :
    (((Finset.Ioc 0 x).filter (fun q => ∀ p ∈ P, ¬p ∣ q)).card:ℝ) =
      ∑ S ∈ P.powerset, (-1:ℝ)^S.card * (x/(∏ p ∈ S, p):ℕ) := by
  classical
  calc
    _ = ∑ q ∈ Finset.Ioc 0 x, if ∀ p ∈ P, ¬p ∣ q then (1:ℝ) else 0 := by simp
    _ = ∑ q ∈ Finset.Ioc 0 x, ∑ S ∈ P.powerset,
        (-1:ℝ)^S.card * (if (∏ p ∈ S, p) ∣ q then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro q _
      exact sieve_indicator P hP q
    _ = ∑ S ∈ P.powerset, (-1:ℝ)^S.card *
        (∑ q ∈ Finset.Ioc 0 x, if (∏ p ∈ S, p) ∣ q then (1:ℝ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      congr 1
      simp [Nat.Ioc_filter_dvd_card_eq_div]

#print axioms subset_primes_prod_dvd
#print axioms sieve_indicator
#print axioms sieve_interval_identity
end BiasGrowth

```

### `BiasSieveError.lean`

```lean
import BiasSieveIdentity
import BiasNatPatterns

namespace BiasGrowth

noncomputable def sieveDensity (P : Finset ℕ) : ℝ :=
  ∑ S ∈ P.powerset, (-1:ℝ)^S.card / (∏ p ∈ S, p)

/-- The elementary discrepancy estimate for a prefix of the positive integers. -/
theorem sieve_prefix_error (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (x : ℕ) :
    |((((Finset.Ioc 0 x).filter (fun q => ∀ p ∈ P, ¬p ∣ q)).card:ℝ) -
      (x:ℝ)*sieveDensity P)| ≤ 2^P.card := by
  classical
  rw [sieve_interval_identity P hP x]
  have he : (∑ S ∈ P.powerset, (-1:ℝ)^S.card * (x/(∏ p ∈ S, p):ℕ)) -
      (x:ℝ)*sieveDensity P = ∑ S ∈ P.powerset, (-1:ℝ)^S.card *
        (((x/(∏ p ∈ S, p):ℕ):ℝ) - (x:ℝ)/(∏ p ∈ S, p)) := by
    unfold sieveDensity
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro S _
    ring
  rw [he]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  calc
    (∑ S ∈ P.powerset, |(-1:ℝ)^S.card *
        (((x/(∏ p ∈ S, p):ℕ):ℝ) - (x:ℝ)/(∏ p ∈ S, p))|) ≤
        ∑ _S ∈ P.powerset, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro S hS
      let d : ℕ := ∏ p ∈ S, p
      have hd : 0 < d := Finset.prod_pos (by
        intro p hp
        exact (hP p (Finset.mem_powerset.mp hS hp)).pos)
      have hdr : (0:ℝ) < d := Nat.cast_pos.mpr hd
      have hlow : ((x/d:ℕ):ℝ) ≤ (x:ℝ)/d := by
        apply (le_div_iff₀ hdr).mpr
        exact_mod_cast Nat.div_mul_le_self x d
      have hupp : (x:ℝ)/d < (x/d:ℕ)+1 := by
        apply (div_lt_iff₀ hdr).mpr
        exact_mod_cast (show x < (x/d+1)*d by simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ x hd)
      rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
      change |((x/d:ℕ):ℝ)-(x:ℝ)/d| ≤ 1
      rw [abs_of_nonpos (by linarith)]
      linarith
    _ = 2^P.card := by simp

#print axioms sieve_prefix_error
end BiasGrowth
```

### `BiasTotientLower.lean`

```lean
import BiasDefinitions
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith

namespace BiasGrowth

/-- The elementary prime-power estimate, with loss only at the prime two. -/
theorem prime_power_totient_square (p n : ℕ) (hp : Nat.Prime p) (hn : 0 < n) :
    p^n ≤ 2*(Nat.totient (p^n))^2 ∧
      (Odd (p^n) → p^n ≤ (Nat.totient (p^n))^2) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [Nat.totient_prime_pow_succ hp, pow_succ]
  have hb : 1 ≤ p^e := Nat.one_le_pow _ _ hp.pos
  have hp2 := hp.two_le
  have hsub : p-1+1 = p := by omega
  have hlarge (h3 : 3 ≤ p) : p^e*p ≤ (p^e*(p-1))^2 := by
    have hbase : p ≤ (p-1)^2 := by nlinarith
    calc
      p^e*p ≤ p^e*((p-1)^2) := Nat.mul_le_mul_left _ hbase
      _ ≤ (p^e)^2*((p-1)^2) := Nat.mul_le_mul_right _ (by nlinarith)
      _ = (p^e*(p-1))^2 := by ring
  constructor
  · by_cases h3 : 3 ≤ p
    · have := hlarge h3; omega
    · have heq : p=2 := by omega
      subst p
      simp only [Nat.reduceSub, mul_one]
      nlinarith
  · intro ho
    have ho' : Odd p := (Nat.odd_pow_iff (by omega : e+1 ≠ 0)).mp (by
      simpa only [pow_succ] using ho)
    have : p ≠ 2 := by intro h; subst p; rcases ho' with ⟨z,hz⟩; omega
    exact hlarge (by omega)

/-- A square-root lower bound, expressed polynomially to avoid rounding issues. -/
theorem totient_square_lower (n : ℕ) : n ≤ 2*(Nat.totient n)^2 := by
  have hall : ∀ n : ℕ, n ≤ 2*(Nat.totient n)^2 ∧
      (Odd n → n ≤ (Nat.totient n)^2) := by
    intro n
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => simp
    | one => simp
    | prime_pow p n hp hn => exact prime_power_totient_square p n hp hn
    | coprime a b ha hb hab ihA ihB =>
      rw [Nat.totient_mul hab]
      have haodd_or_hbodd : Odd a ∨ Odd b := by
        by_cases haodd : Odd a
        · exact Or.inl haodd
        · right
          have hea : 2 ∣ a := (even_iff_two_dvd).mp (Nat.not_odd_iff_even.mp haodd)
          have hnb : ¬ 2 ∣ b := by
            intro heb
            have := Nat.dvd_gcd hea heb
            rw [hab.gcd_eq_one] at this
            norm_num at this
          exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hnb)
      constructor
      · rcases haodd_or_hbodd with hao | hbo
        · have h := Nat.mul_le_mul (ihA.2 hao) ihB.1
          nlinarith only [h]
        · have h := Nat.mul_le_mul ihA.1 (ihB.2 hbo)
          nlinarith only [h]
      · intro ho
        obtain ⟨hao,hbo⟩ := Nat.odd_mul.mp ho
        have h := Nat.mul_le_mul (ihA.2 hao) (ihB.2 hbo)
        nlinarith only [h]
  exact (hall n).1

#print axioms prime_power_totient_square
#print axioms totient_square_lower
end BiasGrowth
```

### `BiasPrimeFactorError.lean`

```lean
import BiasTotientLower
import Mathlib.Data.Finset.Prod

namespace BiasGrowth

/-- Crude fourth-power bound for the inclusion-exclusion error. The constant
is deliberately loose; no prime distribution estimate is used. -/
theorem prime_factor_error_fourth {n : ℕ} (hn : 0 < n) :
    (2^n.primeFactors.card)^4 ≤ 16^16*n := by
  classical
  let S := n.primeFactors.filter (fun p => p < 16)
  let L := n.primeFactors.filter (fun p => ¬ p < 16)
  have hS : S.card ≤ 16 := by
    calc
      _ ≤ (Finset.range 16).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = 16 := Finset.card_range _
  have hprod : ∏ p ∈ n.primeFactors, 16 ≤ 16^S.card * ∏ p ∈ n.primeFactors, p := by
    calc
      _ = (∏ _p ∈ S, 16) * ∏ _p ∈ L, 16 := by
        exact (Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => p<16) (fun _ => 16)).symm
      _ ≤ 16^S.card * ∏ p ∈ L, p := by
        simp only [Finset.prod_const]
        apply Nat.mul_le_mul_left
        rw [← Finset.prod_const]
        apply Finset.prod_le_prod
        intro p hp
        exact Nat.le_of_not_gt (Finset.mem_filter.mp hp).2
      _ ≤ 16^S.card * ∏ p ∈ n.primeFactors, p := by
        apply Nat.mul_le_mul_left
        apply Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
        intro p hp _
        exact (Nat.prime_of_mem_primeFactors hp).pos
  have hrad : ∏ p ∈ n.primeFactors, p ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  calc
    _ = 16^n.primeFactors.card := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
    _ = ∏ _p ∈ n.primeFactors, 16 := (Finset.prod_const _).symm
    _ ≤ 16^S.card * ∏ p ∈ n.primeFactors, p := hprod
    _ ≤ 16^16*n := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hS) hrad

#print axioms prime_factor_error_fourth
end BiasGrowth
```

### `BiasUnitPrefix.lean`

```lean
import BiasSieveError
import BiasPrimeFactorError

namespace BiasGrowth

theorem avoids_primeFactors_iff {t q : ℕ} (ht : 0 < t) :
    (∀ p ∈ t.primeFactors, ¬p ∣ q) ↔ Nat.Coprime t q := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨p,hp,hpt,hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    exact h p (Nat.mem_primeFactors.mpr ⟨hp,hpt,ht.ne'⟩) hpq
  · intro h p hp hd
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hpt := Nat.dvd_of_mem_primeFactors hp
    have hdiv := Nat.dvd_gcd hpt hd
    rw [h.gcd_eq_one] at hdiv
    exact hp'.not_dvd_one hdiv

noncomputable def unitPrefix (t x : ℕ) : ℕ := by
  classical
  exact ((Finset.Ioc 0 x).filter (fun q => Nat.Coprime t q)).card

theorem unitPrefix_period (t : ℕ) : unitPrefix t t = Nat.totient t := by
  classical
  convert Nat.filter_coprime_Ico_eq_totient t 1 using 1
  unfold unitPrefix
  congr 1
  ext q
  simp only [Finset.mem_filter,Finset.mem_Ioc,Finset.mem_Ico]
  omega

theorem primeFactors_sieve_density {t : ℕ} (ht : 0 < t) :
    (t:ℝ)*sieveDensity t.primeFactors = Nat.totient t := by
  classical
  have hid := sieve_interval_identity t.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) t
  have hcount : ((Finset.Ioc 0 t).filter (fun q => ∀ p ∈ t.primeFactors, ¬p ∣ q)).card = Nat.totient t := by
    simpa only [avoids_primeFactors_iff ht,unitPrefix] using unitPrefix_period t
  rw [hcount] at hid
  rw [hid]
  unfold sieveDensity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hS' := Finset.mem_powerset.mp hS
  have hd : (∏ p ∈ S, p) ∣ t := (subset_primes_prod_dvd
    (fun p hp => Nat.prime_of_mem_primeFactors hp) hS' t).mpr
    (fun p hp => Nat.dvd_of_mem_primeFactors (hS' hp))
  have he : ((t/(∏ p ∈ S, p):ℕ):ℝ) = (t:ℝ)/(∏ p ∈ S, p) := Nat.cast_div hd (by
    have hdpos : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors (hS' hp)).pos)
    exact_mod_cast hdpos.ne')
  rw [he]
  ring

theorem unitPrefix_error {t : ℕ} (ht : 0 < t) (x : ℕ) :
    |(unitPrefix t x:ℝ)-(x:ℝ)*(Nat.totient t:ℝ)/t| ≤ (2:ℝ)^t.primeFactors.card := by
  classical
  have hh := sieve_prefix_error t.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp) x
  have he : sieveDensity t.primeFactors = (Nat.totient t:ℝ)/t := by
    apply (eq_div_iff (by exact_mod_cast ht.ne' : (t:ℝ) ≠ 0)).mpr
    nlinarith [primeFactors_sieve_density ht]
  simpa only [avoids_primeFactors_iff ht, unitPrefix, he, mul_div_assoc] using hh

#print axioms avoids_primeFactors_iff
#print axioms unitPrefix_period
#print axioms primeFactors_sieve_density
#print axioms unitPrefix_error
end BiasGrowth
```

### `BiasErrorSmall.lean`

```lean
import BiasPrimeFactorError

open Filter
namespace BiasGrowth

theorem prime_factor_error_small : ∀ᶠ t : ℕ in atTop,
    160*2^t.primeFactors.card ≤ Nat.totient t := by
  let K : ℕ := 51200^2*16^16
  filter_upwards [eventually_ge_atTop (K+1)] with t ht
  have ht0 : 0 < t := by omega
  let E := 2^t.primeFactors.card
  have hE : E^4 ≤ 16^16*t := prime_factor_error_fourth ht0
  have hp := totient_square_lower t
  by_contra h
  have hlt : Nat.totient t < 160*E := by omega
  have hs := Nat.pow_lt_pow_left hlt (by decide : 2 ≠ 0)
  have hlt' : t < 51200*E^2 := by nlinarith
  have hs' := Nat.pow_lt_pow_left hlt' (by decide : 2 ≠ 0)
  have hh : t*t < K*t := by
    dsimp [K]
    nlinarith only [hs',hE]
  have hge : K*t ≤ t*t := Nat.mul_le_mul_right t (by omega)
  omega

#print axioms prime_factor_error_small
end BiasGrowth
```

### `BiasUnitDensity.lean`

```lean
import BiasUnitPrefix
import BiasErrorSmall

open Filter
namespace BiasGrowth

noncomputable def goodUnits (t : ℕ) : Finset (Fin t) := by
  classical
  exact Finset.univ.filter (fun q => Nat.Coprime (q.val+1) t ∧
    9*t ≤ 10*(q.val+1) ∧ 20*(q.val+1) ≤ 19*t)

/-- Positive proportion of units in the one short interval used by class recovery. -/
theorem good_unit_density : ∀ᶠ t : ℕ in atTop,
    (Nat.totient t:ℝ)/40 ≤ (goodUnits t).card := by
  classical
  filter_upwards [prime_factor_error_small,eventually_ge_atTop 2] with t herr ht
  have ht0 : 0 < t := by omega
  have htr : (0:ℝ) < t := Nat.cast_pos.mpr ht0
  let a := 9*t/10
  let b := 19*t/20
  let J := (Finset.Ioc a b).filter (fun q => Nat.Coprime t q)
  have hab : a ≤ b := by dsimp [a,b]; omega
  have hsub : (Finset.Ioc 0 a).filter (fun q => Nat.Coprime t q) ⊆
      (Finset.Ioc 0 b).filter (fun q => Nat.Coprime t q) := by
    intro q hq
    simp only [Finset.mem_filter,Finset.mem_Ioc] at hq ⊢
    exact ⟨⟨hq.1.1,le_trans hq.1.2 hab⟩,hq.2⟩
  have hcard : unitPrefix t b = unitPrefix t a + J.card := by
    have he : ((Finset.Ioc 0 b).filter (fun q => Nat.Coprime t q)) \
        ((Finset.Ioc 0 a).filter (fun q => Nat.Coprime t q)) = J := by
      ext q
      simp only [Finset.mem_sdiff,Finset.mem_filter,Finset.mem_Ioc,J]
      omega
    have hh := Finset.card_sdiff_add_card_eq_card hsub
    rw [he] at hh
    dsimp [unitPrefix]
    omega
  have hJa : J.card ≤ (goodUnits t).card := by
    apply Finset.card_le_card_of_injOn (fun q : ℕ => (⟨(q-1)%t,Nat.mod_lt _ ht0⟩ : Fin t))
    · intro q hq
      obtain ⟨hqI,hcop⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqa,hqb⟩ := Finset.mem_Ioc.mp hqI
      have hq0 : 0 < q := by omega
      change (⟨(q-1)%t,Nat.mod_lt _ ht0⟩ : Fin t) ∈ goodUnits t
      simp only [goodUnits,Finset.mem_filter,Finset.mem_univ,true_and]
      have hpred : q-1+1=q := by omega
      change Nat.Coprime ((q-1)%t+1) t ∧ _
      have hqt : q-1 < t := by dsimp [b] at hqb; omega
      rw [Nat.mod_eq_of_lt hqt]
      rw [hpred]
      refine ⟨hcop.symm,?_,?_⟩ <;> dsimp [a,b] at * <;> omega
    · intro q hq r hr he
      have hq' := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1
      have hr' := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hr).1).1
      have := congrArg Fin.val he
      dsimp at this
      have hqb := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).2
      have hrb := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hr).1).2
      have hqt : q-1 < t := by dsimp [b] at hqb; omega
      have hrt : r-1 < t := by dsimp [b] at hrb; omega
      rw [Nat.mod_eq_of_lt hqt,Nat.mod_eq_of_lt hrt] at this
      omega
  have hA := abs_le.mp (unitPrefix_error ht0 a)
  have hB := abs_le.mp (unitPrefix_error ht0 b)
  have hphi : (0:ℝ) ≤ Nat.totient t := Nat.cast_nonneg _
  have hphit : (Nat.totient t:ℝ) ≤ t := Nat.cast_le.mpr (Nat.totient_le t)
  have hdiva : (a:ℝ)*10 ≤ 9*(t:ℝ) := by
    exact_mod_cast (show a*10 ≤ 9*t from Nat.div_mul_le_self _ _)
  have hdivb : 19*(t:ℝ) < ((b:ℝ)+1)*20 := by
    exact_mod_cast (show 19*t < (b+1)*20 by dsimp [b]; omega)
  have hmain : (Nat.totient t:ℝ)/20-1 ≤
      (b:ℝ)*Nat.totient t/t-(a:ℝ)*Nat.totient t/t := by
    have hm := mul_le_mul_of_nonneg_right (show (t:ℝ)/20-1 ≤ (b:ℝ)-a by linarith) hphi
    apply (le_of_mul_le_mul_right (a := (t:ℝ)))
    · field_simp
      nlinarith only [hm,hphit]
    · exact htr
  have hE : (1:ℝ) ≤ (2:ℝ)^t.primeFactors.card := one_le_pow₀ (by norm_num)
  have herr' : (160:ℝ)*(2:ℝ)^t.primeFactors.card ≤ Nat.totient t := by exact_mod_cast herr
  have hcard' : (unitPrefix t b:ℝ) = (unitPrefix t a:ℝ)+(J.card:ℝ) := by exact_mod_cast hcard
  have hJa' : (J.card:ℝ) ≤ (goodUnits t).card := Nat.cast_le.mpr hJa
  linarith

#print axioms good_unit_density
end BiasGrowth
```

### `BiasLowerCount.lean`

```lean
import BiasConsecutiveSwitch
import BiasUnitDensity
import Mathlib.Order.Interval.Set.Monotone

namespace BiasGrowth

def selectedK {t : ℕ} (q : Fin t) (i : ℕ) : ℕ := (20+i)*t+(q.val+1)

theorem selectedK_coprime {t : ℕ} {q : Fin t} (hq : Nat.Coprime (q.val+1) t) (i : ℕ) :
    Nat.Coprime (selectedK q i) t := by
  unfold selectedK
  rw [Nat.add_comm,Nat.coprime_add_mul_right_left]
  exact hq

theorem selectedK_recovery {t M i : ℕ} (q : Fin t)
    (ht : 100*(M+22)^3 < t) (hi : i ≤ M)
    (hq : q ∈ goodUnits t) (R : ℕ → Fin t → Fin t → Prop) (hR : Compatible t R) :
    ∀ r : Fin t, r ≠ q → rightInvCount (R (selectedK q i)) r <
      rightInvCount (R (selectedK q i)) q := by
  classical
  have hq' : Nat.Coprime (q.val+1) t ∧ 9*t ≤ 10*(q.val+1) ∧ 20*(q.val+1) ≤ 19*t := by
    simpa [goodUnits] using hq
  have ht40 : 40 < t := by nlinarith [sq_nonneg (M+22)]
  have ht0 : (0:ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hk2 : 2 ≤ selectedK q i := by unfold selectedK; nlinarith
  apply class_recovery_general q ht40 hk2 (selectedK_coprime hq'.1 i)
    (by unfold selectedK; nlinarith) ?_ hq'.2.1 hq'.2.2 ?_ R hR
  · change ((20+i)*t+(q.val+1))%t=(q.val+1)%t
    simp [Nat.add_mod]
  · have hkr : (0:ℝ) < selectedK q i := by exact_mod_cast (show 0 < selectedK q i by omega)
    apply (lt_div_iff₀ hkr).mpr
    have hkt : selectedK q i ≤ (M+21)*t := by unfold selectedK; have := q.isLt; nlinarith
    have htlarge : 60*(M+21) < t := by nlinarith [sq_nonneg (M+22)]
    have hkt' : (selectedK q i:ℝ) ≤ ((M:ℝ)+21)*t := by exact_mod_cast hkt
    have htlarge' : (60:ℝ)*((M:ℝ)+21) < t := by exact_mod_cast htlarge
    nlinarith only [hkt',htlarge',ht0]

theorem selectedK_strictAnti {t M : ℕ} (q : Fin t)
    (ht : 100*(M+22)^3 < t) (hq : q ∈ goodUnits t)
    (R : ℕ → Fin t → Fin t → Prop) (hR : Compatible t R) :
    StrictAntiOn (fun i => rightInvCount (R (selectedK q i)) q) (Set.Iic M) := by
  classical
  have hq' : Nat.Coprime (q.val+1) t ∧ 9*t ≤ 10*(q.val+1) ∧ 20*(q.val+1) ≤ 19*t := by
    simpa [goodUnits] using hq
  apply strictAntiOn_Iic_of_succ_lt
  intro i hi
  have hbound : 100*(20+i+2)^3 < t := by
    have hh : (20+i+2)^3 ≤ (M+22)^3 := Nat.pow_le_pow_left (by omega) 3
    omega
  have he : selectedK q (i+1) = selectedK q i + t := by unfold selectedK; ring
  change rightInvCount (R (selectedK q (i+1))) q < _
  rw [he]
  apply consecutive_switch_general q (by omega) hbound hq'.2.1 hq'.2.2 rfl
    (selectedK_coprime hq'.1 i) ?_ R hR
  change Nat.Coprime (selectedK q i+t) t
  rw [← he]
  exact selectedK_coprime hq'.1 (i+1)

/-- Inject all selected classes and parameters into the full unbounded relation set. -/
theorem orderCount_lower_fixed (t M : ℕ) (ht : 100*(M+22)^3 < t)
    (R : ℕ → Fin t → Fin t → Prop) (hR : Compatible t R) :
    (goodUnits t).card*M ≤ orderCount t R := by
  classical
  let D := (goodUnits t) ×ˢ (Finset.univ : Finset (Fin M))
  let f : Fin t × Fin M → (Fin t → Fin t → Prop) := fun p => R (selectedK p.1 p.2.val)
  have hfinj : Set.InjOn f (↑D) := by
    intro p hp z hz he
    have hpq := (Finset.mem_product.mp hp).1
    have hzq := (Finset.mem_product.mp hz).1
    have hqeq : p.1=z.1 := recover_label_of_unique_maxima _ _ p.1 z.1
      (selectedK_recovery p.1 ht (by have := p.2.isLt; omega) hpq R hR)
      (selectedK_recovery z.1 ht (by have := z.2.isLt; omega) hzq R hR) he
    obtain ⟨q,i⟩ := p
    obtain ⟨r,j⟩ := z
    dsimp at hqeq
    subst r
    apply Prod.ext
    · rfl
    · apply Fin.ext
      have hanti := selectedK_strictAnti q ht hpq R hR
      have hec : rightInvCount (R (selectedK q i.val)) q =
          rightInvCount (R (selectedK q j.val)) q := congrArg (fun S => rightInvCount S q) he
      exact hanti.injOn (by have := i.isLt; change i.val ≤ M; omega)
        (by have := j.isLt; change j.val ≤ M; omega) hec
  have hsubset : f '' (↑D : Set (Fin t × Fin M)) ⊆ orderings t R := by
    rintro S ⟨⟨q,i⟩,hp,rfl⟩
    have hq := (Finset.mem_product.mp hp).1
    have hcop : Nat.Coprime (q.val+1) t := by
      have : Nat.Coprime (q.val+1) t ∧ 9*t ≤ 10*(q.val+1) ∧ 20*(q.val+1) ≤ 19*t := by simpa [goodUnits] using hq
      exact this.1
    refine ⟨selectedK q i.val,?_,selectedK_coprime hcop i.val,rfl⟩
    have ht0 : 0 < t := Nat.zero_lt_of_lt q.isLt
    unfold selectedK
    nlinarith
  have hh := Set.ncard_le_ncard hsubset (orderings_finite t R)
  rw [hfinj.ncard_image,Set.ncard_coe_finset] at hh
  simpa [D,Finset.card_product,orderCount,orderings] using hh

#print axioms selectedK_coprime
#print axioms selectedK_recovery
#print axioms selectedK_strictAnti
#print axioms orderCount_lower_fixed
end BiasGrowth
```

### `BiasLowerAsymptotic.lean`

```lean
import BiasLowerCount
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Asymptotics
namespace BiasGrowth

/-- A deliberately weaker fourth-root lower bound suffices for the conjecture.
The cube-root range of the written proof is not needed for this assembly. -/
theorem orderCount_lower_eventually (R : ∀ t : ℕ, ℕ → Fin t → Fin t → Prop)
    (hR : ∀ t, 2 ≤ t → Compatible t (R t)) :
    ∀ᶠ t : ℕ in atTop, (t:ℝ)^(1/4:ℝ)/80 ≤
      (orderCount t (R t):ℝ)/Nat.totient t := by
  have hroot : Tendsto (fun t : ℕ => (t:ℝ)^(1/4:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).comp tendsto_natCast_atTop_atTop
  filter_upwards [good_unit_density,hroot.eventually (eventually_ge_atTop (1000:ℝ)),
    eventually_ge_atTop 2] with t hd hbig ht
  let x : ℝ := (t:ℝ)^(1/4:ℝ)
  let M : ℕ := ⌊x⌋₊
  have hx : 0 < x := by change 1000 ≤ x at hbig; linarith
  have hM : (M:ℝ) ≤ x := Nat.floor_le hx.le
  have hM' : x < (M:ℝ)+1 := Nat.lt_floor_add_one x
  have hpow : x^4=(t:ℝ) := by
    dsimp [x]
    simpa using Real.rpow_inv_natCast_pow (n := 4) (Nat.cast_nonneg t : (0:ℝ) ≤ t) (by decide)
  have hcube : ((M:ℝ)+22)^3 ≤ (2*x)^3 :=
    pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (M:ℝ)+22)
      (by change 1000 ≤ x at hbig; linarith : (M:ℝ)+22 ≤ 2*x) 3
  have hsmall : 800*x^3 < x^4 := by
    have hprod := mul_pos (show 0 < x-800 by change 1000 ≤ x at hbig; linarith) (pow_pos hx 3)
    nlinarith only [hprod]
  have hcut : 100*(M+22)^3 < t := by
    have : (100:ℝ)*((M:ℝ)+22)^3 < t := by nlinarith only [hcube,hsmall,hpow]
    exact_mod_cast this
  have hcount := orderCount_lower_fixed t M hcut (R t) (hR t ht)
  have hcount' : (goodUnits t).card*(M:ℝ) ≤ (orderCount t (R t):ℝ) := by exact_mod_cast hcount
  have hphi : (0:ℝ) < Nat.totient t := by exact_mod_cast (Nat.totient_pos.mpr (show 0 < t by omega))
  have hMd : x/2 ≤ (M:ℝ) := by change 1000 ≤ x at hbig; linarith
  apply (le_div_iff₀ hphi).mpr
  have hmul := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg M : (0:ℝ) ≤ M)
  have hmul' := mul_le_mul_of_nonneg_right hMd hphi.le
  change x/80*(Nat.totient t:ℝ) ≤ _
  nlinarith only [hcount',hmul,hmul']

/-- The lower half of the required literal endpoint. -/
theorem conjecture_355348_lower (R : ∀ t : ℕ, ℕ → Fin t → Fin t → Prop)
    (hR : ∀ t, 2 ≤ t → Compatible t (R t)) :
    (fun t : ℕ => Real.log t) =o[atTop]
      (fun t => (orderCount t (R t):ℝ)/Nat.totient t) := by
  have hlog : (fun t : ℕ => Real.log t) =o[atTop] (fun t => (t:ℝ)^(1/4:ℝ)) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).comp_tendsto tendsto_natCast_atTop_atTop
  apply IsLittleO.of_bound
  intro c hc
  filter_upwards [hlog.bound (show 0 < c/80 by positivity),orderCount_lower_eventually R hR]
    with t ht hb
  have hpos : (0:ℝ) ≤ (orderCount t (R t):ℝ)/Nat.totient t := by positivity
  have hx : (0:ℝ) ≤ (t:ℝ)^(1/4:ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  simp only [Real.norm_eq_abs,abs_of_nonneg hx] at ht
  simp only [Real.norm_eq_abs,abs_of_nonneg hpos]
  have hmul := mul_le_mul_of_nonneg_left hb hc.le
  nlinarith only [ht,hmul]

#print axioms orderCount_lower_eventually
#print axioms conjecture_355348_lower
end BiasGrowth
```

### `BiasEndpoint.lean`

```lean
import BiasUpperAsymptotic
import BiasLowerAsymptotic

open Filter Asymptotics
namespace BiasGrowth

theorem conjecture_355348 (R : ∀ t : ℕ, ℕ → Fin t → Fin t → Prop)
    (hR : ∀ t, 2 ≤ t → Compatible t (R t)) :
    (fun t : ℕ => (orderCount t (R t) : ℝ) / Nat.totient t) =o[atTop] (fun t => (t : ℝ)) ∧
    (fun t : ℕ => Real.log t) =o[atTop] (fun t => (orderCount t (R t) : ℝ) / Nat.totient t) :=
  ⟨conjecture_355348_upper R hR,conjecture_355348_lower R hR⟩

theorem conjecture_355348_strict :
    let R := fun t k (r s : Fin t) => psiKT k t (s.val+1) < psiKT k t (r.val+1)
    (fun t : ℕ => (orderCount t (R t) : ℝ) / Nat.totient t) =o[atTop] (fun t => (t : ℝ)) ∧
    (fun t : ℕ => Real.log t) =o[atTop] (fun t => (orderCount t (R t) : ℝ) / Nat.totient t) := by
  exact conjecture_355348 (fun t => strictFamily t) (fun t _ => compatible_strict t)

/-- Machine-checked comparison with the fixed stage-1 endpoint proposition. -/
theorem endpoint_matches_fixed_proposition : Conjecture355348 := conjecture_355348

#check conjecture_355348
#check conjecture_355348_strict
#print axioms conjecture_355348
#print axioms conjecture_355348_strict
#print axioms endpoint_matches_fixed_proposition
end BiasGrowth
```

### `BiasStage2Audit.lean`

```lean
import BiasDefinitions
import BiasTailCombinatorics
import BiasDigamma
import BiasTailRange
import BiasResidues
import BiasEstimates
import BiasScoreSupport
import BiasInversions
import BiasSlopeUpper
import BiasAudit
import BiasNatPatterns
import BiasRelationDetermination
import BiasTailSupport
import BiasResidueSmall
import BiasLiteralTail
import BiasUpperCount
import BiasLowerResidues
import BiasLowerScores
import BiasUpperAsymptotic
import BiasTotientLower
import BiasClassRecovery
import BiasPrimeFactorError
import BiasMesh
import BiasSwitchBounds
import BiasConsecutiveSwitch
import BiasSieveIdentity
import BiasSieveError
import BiasUnitPrefix
import BiasErrorSmall
import BiasUnitDensity
import BiasLowerCount
import BiasLowerAsymptotic
import BiasEndpoint

namespace BiasGrowth
#check compatible_strict
#print axioms compatible_strict
#check compatible_satisfiable
#print axioms compatible_satisfiable
#check psi_one
#print axioms psi_one
#check orderings_finite
#print axioms orderings_finite
#check orderings_nonempty
#print axioms orderings_nonempty
#check orderCount_pos
#print axioms orderCount_pos
#check rbar_pos
#print axioms rbar_pos
#check rbar_le
#print axioms rbar_le
#check rbar_cast
#print axioms rbar_cast
#check rbar_correct
#print axioms rbar_correct
#check rbar_modEq
#print axioms rbar_modEq
#check subset_chain_card_le
#print axioms subset_chain_card_le
#check reciprocal_crossing_unique
#print axioms reciprocal_crossing_unique
#check reciprocal_negative_antitone
#print axioms reciprocal_negative_antitone
#check exceptional_card_le
#print axioms exceptional_card_le
#check chain_with_exceptions_card_le
#print axioms chain_with_exceptions_card_le
#check reciprocal_patterns_card_le
#print axioms reciprocal_patterns_card_le
#check psi_eq_deriv_logGamma
#print axioms psi_eq_deriv_logGamma
#check psi_monotoneOn
#print axioms psi_monotoneOn
#check psi_add_nat
#print axioms psi_add_nat
#check psi_add_one
#print axioms psi_add_one
#check shifted_psi_gap_bounds
#print axioms shifted_psi_gap_bounds
#check shifted_psi_gap_tendsto
#print axioms shifted_psi_gap_tendsto
#check psi_gap_partial_sum
#print axioms psi_gap_partial_sum
#check psi_gap_hasSum
#print axioms psi_gap_hasSum
#check psi_gap_series
#print axioms psi_gap_series
#check image_ncard_le_of_finset_bound
#print axioms image_ncard_le_of_finset_bound
#check reciprocal_patterns_ncard_le
#print axioms reciprocal_patterns_ncard_le
#check positive_representative_injective
#print axioms positive_representative_injective
#check rbar_eq_iff
#print axioms rbar_eq_iff
#check rbar_injectiveOn
#print axioms rbar_injectiveOn
#check rbar_surjectiveOn
#print axioms rbar_surjectiveOn
#check rbar_bijOn
#print axioms rbar_bijOn
#check rbar_distinguished
#print axioms rbar_distinguished
#check rbar_congr
#print axioms rbar_congr
#check A_bounds
#print axioms A_bounds
#check A_nonneg
#print axioms A_nonneg
#check psi_difference_hasSum
#print axioms psi_difference_hasSum
#check reciprocal_difference
#print axioms reciprocal_difference
#check psi_slope_lower
#print axioms psi_slope_lower
#check B_eq
#print axioms B_eq
#check score_inversion_support
#print axioms score_inversion_support
#check recover_label_of_unique_maxima
#print axioms recover_label_of_unique_maxima
#check rightInvCount_strict_drop
#print axioms rightInvCount_strict_drop
#check reciprocal_difference_succ_le
#print axioms reciprocal_difference_succ_le
#check psi_slope_upper_general
#print axioms psi_slope_upper_general
#check psi_slope_upper
#print axioms psi_slope_upper
#check nat_reciprocal_patterns_ncard_le
#print axioms nat_reciprocal_patterns_ncard_le
#check compatible_iff_B
#print axioms compatible_iff_B
#check same_relation_of_pair_signs
#print axioms same_relation_of_pair_signs
#check pairC_pos
#print axioms pairC_pos
#check pair_difference
#print axioms pair_difference
#check tailPairs_card_le
#print axioms tailPairs_card_le
#check inversion_mem_tailPairs
#print axioms inversion_mem_tailPairs
#check smallParams_finite
#print axioms smallParams_finite
#check small_class_count
#print axioms small_class_count
#check literal_tail_count
#print axioms literal_tail_count
#check class_order_count
#print axioms class_order_count
#check orderCount_upper_fixed
#print axioms orderCount_upper_fixed
#check low_inverse_residue_label_le
#print axioms low_inverse_residue_label_le
#check right_label_inverse_ge_ten
#print axioms right_label_inverse_ge_ten
#check distinguished_gap_lower
#print axioms distinguished_gap_lower
#check forced_right_inversion
#print axioms forced_right_inversion
#check right_inversions_antitone
#print axioms right_inversions_antitone
#check conjecture_355348_upper
#print axioms conjecture_355348_upper
#check conjecture_355348_strict_upper
#print axioms conjecture_355348_strict_upper
#check prime_power_totient_square
#print axioms prime_power_totient_square
#check totient_square_lower
#print axioms totient_square_lower
#check other_inverse_ge_two
#print axioms other_inverse_ge_two
#check other_inversion_count_le
#print axioms other_inversion_count_le
#check class_recovery_general
#print axioms class_recovery_general
#check prime_factor_error_fourth
#print axioms prime_factor_error_fourth
#check mesh_point
#print axioms mesh_point
#check mesh_avoids_small_labels
#print axioms mesh_avoids_small_labels
#check switch_scalar_bounds
#print axioms switch_scalar_bounds
#check consecutive_switch_general
#print axioms consecutive_switch_general
#check subset_primes_prod_dvd
#print axioms subset_primes_prod_dvd
#check sieve_indicator
#print axioms sieve_indicator
#check sieve_interval_identity
#print axioms sieve_interval_identity
#check sieve_prefix_error
#print axioms sieve_prefix_error
#check avoids_primeFactors_iff
#print axioms avoids_primeFactors_iff
#check unitPrefix_period
#print axioms unitPrefix_period
#check primeFactors_sieve_density
#print axioms primeFactors_sieve_density
#check unitPrefix_error
#print axioms unitPrefix_error
#check prime_factor_error_small
#print axioms prime_factor_error_small
#check good_unit_density
#print axioms good_unit_density
#check selectedK_coprime
#print axioms selectedK_coprime
#check selectedK_recovery
#print axioms selectedK_recovery
#check selectedK_strictAnti
#print axioms selectedK_strictAnti
#check orderCount_lower_fixed
#print axioms orderCount_lower_fixed
#check orderCount_lower_eventually
#print axioms orderCount_lower_eventually
#check conjecture_355348_lower
#print axioms conjecture_355348_lower
#check conjecture_355348
#print axioms conjecture_355348
#check conjecture_355348_strict
#print axioms conjecture_355348_strict
#check endpoint_matches_fixed_proposition
#print axioms endpoint_matches_fixed_proposition
end BiasGrowth
```

