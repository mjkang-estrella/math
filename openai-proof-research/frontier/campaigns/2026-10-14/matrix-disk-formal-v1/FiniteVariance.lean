/-
Copyright (c) 2026 Myeongjin Kang. All rights reserved.
Released under MIT license (see README of this campaign directory).

Authors: Myeongjin Kang (no affiliation)
-/
import Mathlib

/-!
# Finite scalar bistochastic variance identity

A bounded supporting component of
`frontier/campaigns/2026-10-14/matrix-disk-discovery/analysis.md` (variance section only).

That section records, for Hilbert-space-valued `u_j` and Markov (bistochastic)
kernels `K_j`, the *exact variance formula*

```
2δ_j = ∫∫∫ K_j(λ,μ) K_j(ν,μ) ‖u_j(λ) - u_j(ν)‖²_HS dτ(λ) dτ(ν) dτ(μ).
```

This file proves the **finite real scalar** algebraic core of that identity,
with nothing analytical.  For an arbitrary finite index type `I` (the empty
type included, since all sums over `Finset.univ` are then empty), a kernel
`K : I → I → ℝ` with row sums and column sums equal to 1, and any vector
`u : I → ℝ`,

```
∑ j, ∑ i, ∑ k, K i j * K k j * (u i - u k)²
  = 2 * (∑ i, u i² - ∑ j, (∑ i, K i j * u i)²).
```

Both normalizations are used: the column sums `∑ i, K i j = 1` collapse the
inner double sum at each fixed `j` to a per-column variance, and the row sums
`∑ j, K i j = 1` identify `∑ j, ∑ i, K i j * u i²` with `∑ i, u i²`.
Positivity of `K` is *not* needed for the identity; it is used only in the
corollary, where the triple sum is nonnegative termwise.

**Scope limits (explicit).**  This finite scalar certificate does *not* cover
Hilbert-valued integrals, moving kernels `K_j`, the Fatou limiting argument,
positivity on curved arcs, or any part of the Crouzeix theorem.  It is only
the finite algebraic variance identity above, plus the nonnegativity
corollary.  No axiom merely restating the target equality is introduced; the
only axioms used are the standard Lean ones (`propext`, `Classical.choice`,
`Quot.sound`), verified by `#print axioms` at the end of this file.

## Main results

* `tripleSum_column`: per-column expansion of the triple sum into
  `2 * (weighted second moment - squared weighted mean)`.
* `bistochastic_variance`: the exact finite scalar variance identity.
* `variance_deficit_nonneg`: under `∀ i j, 0 ≤ K i j`, the variance deficit
  `∑ i, u i² - ∑ j, (∑ i, K i j * u i)²` is nonnegative.
-/

open Finset

-- `DecidableEq I` is part of the required hypothesis profile of the main
-- theorems (per the task statement) even though the algebraic proof never
-- case-splits on it; suppress the corresponding linter warning.
set_option linter.unusedSectionVars false

/-! ### Helper lemmas -/

/-- Finite linearity: distributing a sum of `X + Y - 2 * Z` over a double
index set.  (Stated for `ι → ι → ℝ` to match the triple sum below; the empty
type is allowed, in which case both sides are `0`.) -/
private theorem sum_add_sub_two_mul {ι : Type*} [Fintype ι] {X Y Z : ι → ι → ℝ} :
    (∑ i, ∑ k, (X i k + Y i k - 2 * Z i k))
      = (∑ i, ∑ k, X i k) + (∑ i, ∑ k, Y i k) - 2 * (∑ i, ∑ k, Z i k) := by
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Collapse `∑ i, ∑ k, K i j * K k j * u i²` to the column-weighted second
moment, using the column normalization `∑ k, K k j = 1`. -/
private theorem weighted_moment2 {I : Type*} [Fintype I] (K : I → I → ℝ) (u : I → ℝ)
    (hcol : ∀ j, ∑ i, K i j = 1) (j : I) :
    (∑ i, ∑ k, K i j * K k j * u i ^ 2) = (∑ i, K i j * u i ^ 2) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (∑ k, K i j * K k j * u i ^ 2) = ∑ k, (K i j * u i ^ 2) * K k j :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [h, ← Finset.mul_sum, hcol j, mul_one]

/-- The symmetric half-moment, with the roles of the two summation indices
exchanged; still uses the column normalization `∑ i, K i j = 1`. -/
private theorem weighted_moment2' {I : Type*} [Fintype I] (K : I → I → ℝ) (u : I → ℝ)
    (hcol : ∀ j, ∑ i, K i j = 1) (j : I) :
    (∑ i, ∑ k, K i j * K k j * u k ^ 2) = (∑ k, K k j * u k ^ 2) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : (∑ i, K i j * K k j * u k ^ 2) = ∑ i, (K k j * u k ^ 2) * K i j :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [h, ← Finset.mul_sum, hcol j, mul_one]

/-- The weighted cross moment factorizes as a product of weighted first
moments. -/
private theorem weighted_prod {I : Type*} [Fintype I] (K : I → I → ℝ) (u : I → ℝ)
    (j : I) :
    (∑ i, ∑ k, K i j * K k j * (u i * u k))
      = (∑ i, K i j * u i) * (∑ i, K i j * u i) := by
  have e1 : (∑ i, ∑ k, K i j * K k j * (u i * u k))
      = ∑ i, ∑ k, (K i j * u i) * (K k j * u k) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [e1]
  exact (Finset.sum_mul_sum (Finset.univ) (Finset.univ)
    (fun i => K i j * u i) (fun k => K k j * u k)).symm

/-! ### Main results -/

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Per-column expansion: for any kernel `K` with column sums `1` and any `u`,
the triple sum at fixed column `j` equals twice the difference of the
column-weighted second moment and the squared column-weighted mean.  This is
the algebraic core `(u i - u k)² = u i² + u k² - 2 u i u k` plus the column
normalization; row sums are not needed here. -/
theorem tripleSum_column {K : I → I → ℝ} {u : I → ℝ}
    (hcol : ∀ j, ∑ i, K i j = 1) (j : I) :
    (∑ i, ∑ k, K i j * K k j * (u i - u k) ^ 2)
      = 2 * ((∑ i, K i j * u i ^ 2) - (∑ i, K i j * u i) ^ 2) := by
  have expand : ∀ i k : I, K i j * K k j * (u i - u k) ^ 2
      = K i j * K k j * u i ^ 2 + K i j * K k j * u k ^ 2
        - 2 * (K i j * K k j * (u i * u k)) := by
    intro i k; ring
  calc (∑ i, ∑ k, K i j * K k j * (u i - u k) ^ 2)
      = ∑ i, ∑ k, (K i j * K k j * u i ^ 2 + K i j * K k j * u k ^ 2
          - 2 * (K i j * K k j * (u i * u k))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by
          rw [expand i k]
    _ = (∑ i, ∑ k, K i j * K k j * u i ^ 2)
        + (∑ i, ∑ k, K i j * K k j * u k ^ 2)
        - 2 * (∑ i, ∑ k, K i j * K k j * (u i * u k)) :=
        sum_add_sub_two_mul
          (X := fun i k => K i j * K k j * u i ^ 2)
          (Y := fun i k => K i j * K k j * u k ^ 2)
          (Z := fun i k => K i j * K k j * (u i * u k))
    _ = 2 * ((∑ i, K i j * u i ^ 2) - (∑ i, K i j * u i) ^ 2) := by
        simp only [weighted_moment2 K u hcol j, weighted_moment2' K u hcol j,
          weighted_prod K u j]
        ring

/-- **Finite scalar bistochastic variance identity.**  For any finite type `I`
(with decidable equality, though decidability is not used in the algebra), any
kernel `K : I → I → ℝ` whose row sums and column sums are all `1`, and any
`u : I → ℝ`,

```
∑ j, ∑ i, ∑ k, K i j * K k j * (u i - u k)²
  = 2 * (∑ i, u i² - ∑ j, (∑ i, K i j * u i)²).
```

Both Markov normalizations are used: `hcol` in `tripleSum_column`, and `hrow`
to identify `∑ j, ∑ i, K i j * u i²` with `∑ i, u i²`.  The empty type is
covered (all sums are `0`).  Positivity of `K` is not assumed. -/
theorem bistochastic_variance {K : I → I → ℝ} {u : I → ℝ}
    (hrow : ∀ i, ∑ j, K i j = 1)
    (hcol : ∀ j, ∑ i, K i j = 1) :
    (∑ j, ∑ i, ∑ k, K i j * K k j * (u i - u k) ^ 2)
      = 2 * ((∑ i, u i ^ 2) - (∑ j, (∑ i, K i j * u i) ^ 2)) := by
  simp only [tripleSum_column hcol]
  rw [← Finset.mul_sum (a := (2 : ℝ)), Finset.sum_sub_distrib]
  -- collapse the weighted second moment via the row sums
  have hB : (∑ j, ∑ i, K i j * u i ^ 2) = ∑ i, u i ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (∑ j, K i j * u i ^ 2) = ∑ j, (u i ^ 2) * K i j :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [h1, ← Finset.mul_sum (a := u i ^ 2), hrow i, mul_one]
  rw [hB]

/-- **Nonnegativity of the variance deficit.**  Under the same hypotheses plus
entrywise nonnegativity `0 ≤ K i j`, each summand
`K i j * K k j * (u i - u k)²` is nonnegative, so the triple sum is
nonnegative, and the exact identity forces the deficit
`∑ i, u i² - ∑ j, (∑ i, K i j * u i)²` to be nonnegative as well. -/
theorem variance_deficit_nonneg {K : I → I → ℝ} {u : I → ℝ}
    (hrow : ∀ i, ∑ j, K i j = 1)
    (hcol : ∀ j, ∑ i, K i j = 1)
    (hK : ∀ i j, 0 ≤ K i j) :
    0 ≤ (∑ i, u i ^ 2) - (∑ j, (∑ i, K i j * u i) ^ 2) := by
  have h1 : (∑ j, ∑ i, ∑ k, K i j * K k j * (u i - u k) ^ 2)
      = 2 * ((∑ i, u i ^ 2) - (∑ j, (∑ i, K i j * u i) ^ 2)) :=
    bistochastic_variance hrow hcol
  have h2 : 0 ≤ (∑ j, ∑ i, ∑ k, K i j * K k j * (u i - u k) ^ 2) := by
    refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun k _ => ?_
    exact mul_nonneg (mul_nonneg (hK i j) (hK k j)) (sq_nonneg (u i - u k))
  linarith

/-! ### Axiom audit -/

#print axioms tripleSum_column
#print axioms bistochastic_variance
#print axioms variance_deficit_nonneg
