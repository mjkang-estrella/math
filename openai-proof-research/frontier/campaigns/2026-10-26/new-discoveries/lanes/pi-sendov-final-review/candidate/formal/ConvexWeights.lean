/-
Copyright (c) 2026 pi implementation sub-agent, pi-sendov-selection-formal lane.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Positive convex weights from a vanishing deleted-product derivative

Standalone companion module to `Selection.lean` (no dependency on it).  For a
cubic with three continuous complex "roots" `a 0, a 1, a 2 : X → ℂ` on a
topological space `X`, if a continuous `B : X → ℂ` never meets any `a j` and the
*literal deleted-product derivative* vanishes at `B` pointwise, then `B` is a
genuine convex combination of the `a j` with continuous, strictly positive,
real-valued coefficients summing to one:

* `CStarSendov.deletedProductDeriv`: the literal deleted-product derivative
  `∑_j ∏_{k≠j} (B - a_k)` as a continuous function.
* `CStarSendov.exists_convex_weights`: the main existence theorem, with the
  explicit formula `ω j x = r j x / (∑ i, r i x)` where
  `r j x = 1 / |B x - a j x|²` (reciprocal squared distances).

## Scope and the remaining bridge to the C\*-order

Everything here is pointwise/functional: the coefficients are continuous
real-valued functions on `X`, strictly positive at every point, summing to `1`
pointwise, and `B = ∑_j ω_j • a_j` holds as an identity of functions (hence in
`C(X, ℂ)`).  The parent lane must still bridge "pointwise strictly positive
continuous real function" to the positive cone of the C\*-algebra `C(X, ℂ)`
(for the parent's compact `X = [0,1]` this is the standard fact that a
self-adjoint element of `C(X)` is positive iff its spectrum — the closed range —
is nonnegative, equivalently iff it is pointwise nonnegative); that bridge is
**not** formalized here and no full source statement is claimed.

The proof mirrors the parent's hand argument: the vanishing deleted-product
derivative, divided by the nonvanishing product `∏_k (B - a_k)`, gives the
harmonic identity `∑_j (B x - a_j x)⁻¹ = 0`; conjugating turns it into
`∑_j r j x • (B x - a_j x) = 0` with `r j x = 1 / |B x - a_j x|² > 0`, whence
`B x = ∑_j ω_j x • a_j x` with `ω_j = r_j / (∑_i r_i)`.
-/

namespace CStarSendov

open Finset

variable {X : Type*} [TopologicalSpace X]

/-- The literal deleted-product (logarithmic) derivative of the cubic with
continuous roots `a : Fin 3 → X → ℂ`, evaluated at the continuous point `B`:

`deletedProductDeriv B a x = ∑_j ∏_{k ≠ j} (B x - a_k x)`. -/
def deletedProductDeriv (B : X → ℂ) (a : Fin 3 → X → ℂ) : X → ℂ :=
  fun x => ∑ j : Fin 3, ∏ k ∈ univ.erase j, (B x - a k x)

omit [TopologicalSpace X] in
theorem deletedProductDeriv_apply (B : X → ℂ) (a : Fin 3 → X → ℂ) (x : X) :
    deletedProductDeriv B a x = ∑ j : Fin 3, ∏ k ∈ univ.erase j, (B x - a k x) :=
  rfl

/-- If all three `c j` are nonzero and the deleted product vanishes, then the
harmonic sum `∑_j (c j)⁻¹` vanishes.  This is the division of the derivative by
the nonvanishing product `∏_k c k`, done termwise. -/
theorem harmonic_sum_zero {c : Fin 3 → ℂ} (hc : ∀ j, c j ≠ 0)
    (h : ∑ j : Fin 3, ∏ k ∈ univ.erase j, c k = 0) :
    ∑ j : Fin 3, (c j)⁻¹ = 0 := by
  have hprod : ∏ k : Fin 3, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hc j)
  have hexpand : (∏ k : Fin 3, c k) * ∑ j : Fin 3, (c j)⁻¹
      = ∑ j : Fin 3, ∏ k ∈ univ.erase j, c k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_prod_erase (a := j) (univ : Finset (Fin 3)) c (mem_univ j),
      mul_comm (c j) (∏ k ∈ univ.erase j, c k), mul_assoc, mul_inv_cancel₀ (hc j), mul_one]
  have h0 : (∏ k : Fin 3, c k) * ∑ j : Fin 3, (c j)⁻¹ = 0 := by rw [hexpand, h]
  exact ((mul_eq_zero).mp h0).resolve_left hprod

/-- Conjugate-of-inverse identity: `(⋆c⁻¹) = (1 / |c|²) • c` for `c ≠ 0`.
This is `(B - a_j)⁻¹ = conj (B - a_j) / |B - a_j|²` conjugated once. -/
theorem conj_inv_eq_rmul (c : ℂ) (hc : c ≠ 0) :
    (starRingEnd ℂ) (c⁻¹) = ((1 / Complex.normSq c : ℝ) : ℂ) * c := by
  have hcc : (starRingEnd ℂ) c ≠ 0 := by
    intro h
    have h1 : Complex.normSq ((starRingEnd ℂ) c) = 0 := by rw [h, Complex.normSq_zero]
    rw [Complex.normSq_conj] at h1
    exact hc (Complex.normSq_eq_zero.mp h1)
  have hcoe : ((1 / Complex.normSq c : ℝ) : ℂ) = ((Complex.normSq c : ℝ) : ℂ)⁻¹ := by simp
  have hmul : ((Complex.normSq c : ℝ) : ℂ) = c * (starRingEnd ℂ) c := (Complex.mul_conj c).symm
  rw [Complex.conj_inv, hcoe, hmul, mul_inv_rev]
  field_simp [hc, hcc]

/-- **Positive convex weights from a vanishing deleted-product derivative.**
Let `B : X → ℂ` and `a : Fin 3 → X → ℂ` be continuous with `B x ≠ a j x` for
every `x` and `j`.  If the literal deleted-product derivative vanishes at `B`
pointwise, then there are continuous functions `ω : Fin 3 → X → ℝ` such that

* `0 < ω j x` for every `x` and `j` (strictly positive real coefficients),
* `∑_j ω j x = 1` for every `x`, and
* `B = ∑_j ω j • a j` as functions (hence as elements of `C(X, ℂ)`).

The witness is `ω j x = r j x / (∑_i r i x)` with `r j x = 1 / |B x - a j x|²`.
No connectedness or nonemptiness assumption on `X` is needed. -/
theorem exists_convex_weights {B : X → ℂ} {a : Fin 3 → X → ℂ}
    (hB : Continuous B) (ha : ∀ j, Continuous (a j))
    (hne : ∀ (x : X) (j : Fin 3), B x ≠ a j x)
    (hderiv : ∀ x, deletedProductDeriv B a x = 0) :
    ∃ ω : Fin 3 → X → ℝ,
      (∀ j, Continuous (ω j)) ∧
      (∀ (x : X) (j : Fin 3), 0 < ω j x) ∧
      (∀ x, ∑ j : Fin 3, ω j x = 1) ∧
      B = ∑ j : Fin 3, ω j • a j := by
  -- Reciprocal squared distances `r j x = 1 / |B x - a j x|²`.
  obtain ⟨r, hrdef, hrpos, hrcont⟩ :
      ∃ r : Fin 3 → X → ℝ,
        (∀ (j : Fin 3) (x : X), r j x = 1 / Complex.normSq (B x - a j x)) ∧
        (∀ (x : X) (j : Fin 3), 0 < r j x) ∧
        (∀ j, Continuous (r j)) := by
    refine ⟨fun j x => 1 / Complex.normSq (B x - a j x), fun _ _ => rfl, ?_, ?_⟩
    · intro x j
      exact one_div_pos.mpr (Complex.normSq_pos.mpr (sub_ne_zero_of_ne (hne x j)))
    · intro j
      have h2 : Continuous fun x => (‖B x - a j x‖ : ℝ) ^ 2 := (hB.sub (ha j)).norm.pow 2
      have h3 : Continuous fun x => Complex.normSq (B x - a j x) := by
        refine h2.congr fun x => ?_
        rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _)]
      exact continuous_const.div h3
        fun x => (Complex.normSq_pos.mpr (sub_ne_zero_of_ne (hne x j))).ne'
  have hsumpos : ∀ x, 0 < ∑ i : Fin 3, r i x := fun x =>
    Finset.sum_pos (fun j _ => hrpos x j) ⟨0, mem_univ 0⟩
  refine ⟨fun j x => r j x / ∑ i, r i x, ?_, ?_, ?_, ?_⟩
  · -- Continuity of the weights
    intro j
    exact (hrcont j).div (continuous_finsetSum univ fun i _ => hrcont i)
      fun x => (hsumpos x).ne'
  · -- Strict positivity
    intro x j
    exact div_pos (hrpos x j) (hsumpos x)
  · -- The weights sum to one
    intro x
    rw [← Finset.sum_div, div_self (ne_of_gt (hsumpos x))]
  · -- The convex-combination identity
    funext x
    -- Step 1: the harmonic sum vanishes (derivative divided by the product).
    have hzero : ∑ j : Fin 3, ((B x - a j x)⁻¹) = 0 :=
      harmonic_sum_zero (fun j => sub_ne_zero_of_ne (hne x j)) (hderiv x)
    -- Step 2: conjugate once; each `(⋆(B x - a_j x)⁻¹)` becomes `r j x • (B x - a_j x)`.
    have h2 : ∀ j : Fin 3, (starRingEnd ℂ) ((B x - a j x)⁻¹)
        = ((r j x : ℝ) : ℂ) * (B x - a j x) := by
      intro j
      rw [hrdef j x]
      exact conj_inv_eq_rmul _ (sub_ne_zero_of_ne (hne x j))
    have hconj : ∑ j : Fin 3, ((r j x : ℝ) : ℂ) * (B x - a j x) = 0 := by
      have h1 : (starRingEnd ℂ) (∑ j : Fin 3, ((B x - a j x)⁻¹)) = 0 := by
        rw [hzero, map_zero]
      rw [map_sum] at h1
      simp only [h2] at h1
      exact h1
    -- Step 3: expand the weighted sum around `B x`.
    have hkey : ((∑ i : Fin 3, r i x : ℝ) : ℂ) * B x
        = ∑ j : Fin 3, ((r j x : ℝ) : ℂ) * a j x := by
      have h4 : ∑ j : Fin 3, ((r j x : ℝ) : ℂ) * (B x - a j x)
          = ((∑ i : Fin 3, r i x : ℝ) : ℂ) * B x
            - ∑ j : Fin 3, ((r j x : ℝ) : ℂ) * a j x := by
        trans ∑ j : Fin 3, (((r j x : ℝ) : ℂ) * B x - ((r j x : ℝ) : ℂ) * a j x)
        · exact Finset.sum_congr rfl fun _ _ => mul_sub _ _ _
        · rw [Finset.sum_sub_distrib]
          congr 1
          · rw [← Finset.sum_mul univ (fun k => ((r k x : ℝ) : ℂ)) (B x),
              ← Complex.ofReal_sum]
      have h0 : ∑ j : Fin 3, ((r j x : ℝ) : ℂ) * (B x - a j x) = 0 := hconj
      rw [h4] at h0
      exact sub_eq_zero.mp h0
    -- Step 4: divide by the (nonzero) total weight.
    have hS : ∑ i : Fin 3, r i x ≠ 0 := ne_of_gt (hsumpos x)
    have hSc : ((∑ i : Fin 3, r i x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS
    have hscal : ∀ j : Fin 3, ((∑ i : Fin 3, r i x : ℝ) : ℂ)⁻¹ * ((r j x : ℝ) : ℂ)
        = ((r j x / (∑ i : Fin 3, r i x) : ℝ) : ℂ) := by
      intro j
      rw [div_eq_inv_mul, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    have hfin : B x = ∑ j : Fin 3, ((r j x / (∑ i : Fin 3, r i x) : ℝ) : ℂ) * a j x := by
      have h5 : B x = ((∑ i : Fin 3, r i x : ℝ) : ℂ)⁻¹
          * (((∑ i : Fin 3, r i x : ℝ) : ℂ) * B x) :=
        (inv_mul_cancel_left₀ hSc (B x)).symm
      rw [h5, hkey, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hscal j, mul_assoc]
    -- Convert to the pointwise `•` form of the Pi-smul statement.
    refine hfin.trans ?_
    rw [Finset.sum_apply]
    exact (Finset.sum_congr rfl fun _ _ => by simp).symm

end CStarSendov
