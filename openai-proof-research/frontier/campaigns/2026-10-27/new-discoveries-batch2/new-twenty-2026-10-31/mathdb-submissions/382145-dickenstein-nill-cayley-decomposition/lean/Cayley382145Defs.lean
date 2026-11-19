import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# MathDB 382145: native definitions and literal statement

Dickenstein–Nill Cayley decomposition conjecture (DRHNP arXiv:1105.2415v3 Conjecture 3 =
Garzón Mora–Haase arXiv:2302.04074v1 Conjecture 1.1). All notions are defined from the
polytope itself: facets are the `(n-1)`-dimensional faces cut out by primitive inward integral
normals, the Q-codegree is the reciprocal of the supremal uniform inward facet shift, and a
Cayley sum is an image under an integral affine lattice isomorphism (with its real extension).
-/

namespace Cayley382145

open scoped Matrix

/-- Pairing of an integral covector with a real point. -/
def intDot {n : ℕ} (a : Fin n → ℤ) (x : Fin n → ℝ) : ℝ := ∑ i, (a i : ℝ) * x i

/-- Coordinatewise cast of a lattice point. -/
def castPt {ι : Type*} (v : ι → ℤ) : ι → ℝ := fun i => (v i : ℝ)

/-- Convex hull of finitely many lattice points (a lattice polytope). -/
def latticeHull {k : ℕ} (V : Finset (Fin k → ℤ)) : Set (Fin k → ℝ) :=
  convexHull ℝ (castPt '' (V : Set (Fin k → ℤ)))

/-- A primitive integral vector: its entries have no common non-unit divisor. -/
def IsPrimitive {n : ℕ} (a : Fin n → ℤ) : Prop := ∀ d : ℤ, (∀ i, d ∣ a i) → IsUnit d

/-- `min_P ⟨a, ·⟩`. -/
noncomputable def facetOffset {n : ℕ} (P : Set (Fin n → ℝ)) (a : Fin n → ℤ) : ℝ :=
  sInf (intDot a '' P)

/-- The face of `P` on which `⟨a, ·⟩` is minimal. -/
def facetFace {n : ℕ} (P : Set (Fin n → ℝ)) (a : Fin n → ℤ) : Set (Fin n → ℝ) :=
  {x | x ∈ P ∧ intDot a x = facetOffset P a}

/-- `a` is the primitive inward normal of an actual facet (a nonempty face of dimension
`n - 1`) of `P`. -/
def IsFacetNormal {n : ℕ} (P : Set (Fin n → ℝ)) (a : Fin n → ℤ) : Prop :=
  IsPrimitive a ∧ (∀ x ∈ P, facetOffset P a ≤ intDot a x) ∧ (facetFace P a).Nonempty ∧
    Module.finrank ℝ (affineSpan ℝ (facetFace P a)).direction = n - 1

/-- The adjoint polytope `P^(s) = {x : ⟨a_F, x⟩ ≥ b_F + s for every facet F}`. -/
def adjointSet {n : ℕ} (P : Set (Fin n → ℝ)) (s : ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ a, IsFacetNormal P a → facetOffset P a + s ≤ intDot a x}

/-- The Q-codegree `μ(P) = (sup {s > 0 : P^(s) ≠ ∅})⁻¹`. -/
noncomputable def qCodegree {n : ℕ} (P : Set (Fin n → ℝ)) : ℝ :=
  (sSup {s : ℝ | 0 < s ∧ (adjointSet P s).Nonempty})⁻¹

/-- Vertices `0, e_1, …, e_t` of the standard simplex in `ℝ^t`. -/
def cayleyVertex {t : ℕ} : Option (Fin t) → Fin t → ℝ
  | none => 0
  | some j => Pi.single j 1

/-- `p ↦ (p, e_i) ∈ ℝ^k × ℝ^t`. -/
def cayleyEmbed {k t : ℕ} (i : Option (Fin t)) (p : Fin k → ℝ) : Fin k ⊕ Fin t → ℝ :=
  Sum.elim p (cayleyVertex i)

/-- Real extension (matrix over `ℝ`) of an integral linear map. -/
noncomputable def realExt {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → ℤ) →ₗ[ℤ] (κ → ℤ)) : Matrix κ ι ℝ :=
  (LinearMap.toMatrix' g).map (Int.cast : ℤ → ℝ)

/-- `P` is a nontrivial Cayley sum `P_0 * ⋯ * P_t` (`t ≥ 1`) of lattice polytopes
`P_i ⊆ ℝ^k`: an affine lattice isomorphism `ℤ^n ≅ ℤ^k × ℤ^t` maps `P` onto
`conv (⋃ i, P_i × {e_i})`. -/
def IsCayleySumIn {n : ℕ} (P : Set (Fin n → ℝ)) (k t : ℕ) : Prop :=
  1 ≤ t ∧ ∃ (g : (Fin n → ℤ) ≃ₗ[ℤ] (Fin k ⊕ Fin t → ℤ)) (z : Fin n → ℤ)
    (Q : Option (Fin t) → Finset (Fin k → ℤ)),
    (∀ i, (Q i).Nonempty) ∧
    (fun x => realExt (g : (Fin n → ℤ) →ₗ[ℤ] (Fin k ⊕ Fin t → ℤ)) *ᵥ (x - castPt z)) '' P =
      convexHull ℝ (⋃ i, cayleyEmbed i '' latticeHull (Q i))

/-- MathDB 382145 (literal): every `n`-dimensional lattice polytope with
`μ(P) > (n+1)/2` is a Cayley sum of lattice polytopes of dimension at most
`⌊2(n+1-μ(P))⌋`. -/
def DickensteinNillCayleyConjecture : Prop :=
  ∀ (n : ℕ) (P : Set (Fin n → ℝ)) (V : Finset (Fin n → ℤ)), P = latticeHull V →
    affineSpan ℝ P = ⊤ → ((n : ℝ) + 1) / 2 < qCodegree P →
    ∃ k t : ℕ, (k : ℤ) ≤ ⌊2 * ((n : ℝ) + 1 - qCodegree P)⌋ ∧ IsCayleySumIn P k t

end Cayley382145
