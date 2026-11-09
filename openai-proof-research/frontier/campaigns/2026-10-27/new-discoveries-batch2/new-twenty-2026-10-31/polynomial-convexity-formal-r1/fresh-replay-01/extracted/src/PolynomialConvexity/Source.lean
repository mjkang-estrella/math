import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Mul
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Union

/-! Literal definitions for MathDB 347913, arXiv:2009.04510 Eq. (2).
Fin n uses zero-based vertex names; the bijection i ↦ i+1 identifies [n].
No moment representation is built into these definitions. -/
namespace PolynomialConvexity
noncomputable section
open Finset

abbrev Edge (n L : ℕ) := {e : Finset (Fin n) // e.card = L}

/-- The union includes position j itself. -/
def prefixUnion {n L d : ℕ} (e : Fin d → Edge n L) (j : Fin d) : Finset (Fin n) :=
  univ.biUnion fun i => if i ≤ j then (e i).val else ∅

def coefficient {n L d : ℕ} (e : Fin d → Edge n L) : ℝ :=
  ∏ j, ((prefixUnion e j).card : ℝ)⁻¹

/-- All functions Fin d → Edge n L occur, so repetitions are allowed. -/
def weight {n L d : ℕ} (x : Edge n L → ℝ) (e : Fin d → Edge n L) : ℝ :=
  ∏ i, x (e i)

def sourcePolynomial (n L d : ℕ) (x : Edge n L → ℝ) : ℝ :=
  ∑ e : Fin d → Edge n L, weight x e * coefficient e

def simplex (n L : ℕ) : Set (Edge n L → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ ∑ e, x e = 1}

/-- This is a proposition to prove, NOT a theorem. -/
def SourceConjecture : Prop :=
  ∀ n L d : ℕ, 2 ≤ n → 2 ≤ L → 2 ≤ d →
    ConvexOn ℝ (simplex n L) (sourcePolynomial n L d)

theorem mem_prefixUnion {n L d : ℕ} (e : Fin d → Edge n L)
    (j : Fin d) (v : Fin n) :
    v ∈ prefixUnion e j ↔ ∃ i, i ≤ j ∧ v ∈ (e i).val := by
  simp only [prefixUnion, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    by_cases h : i ≤ j
    · exact ⟨i, h, by simpa [h] using hi⟩
    · simp [h] at hi
  · rintro ⟨i, hi, hv⟩
    exact ⟨i, by simpa [hi] using hv⟩

theorem edge_subset_prefix {n L d : ℕ} (e : Fin d → Edge n L) (j : Fin d) :
    (e j).val ⊆ prefixUnion e j := by
  intro v hv
  exact (mem_prefixUnion e j v).2 ⟨j, le_rfl, hv⟩

theorem prefix_card_pos {n L d : ℕ} (hL : 0 < L)
    (e : Fin d → Edge n L) (j : Fin d) : 0 < (prefixUnion e j).card := by
  have h := card_le_card (edge_subset_prefix e j)
  rw [(e j).property] at h
  omega

theorem coefficient_pos {n L d : ℕ} (hL : 0 < L) (e : Fin d → Edge n L) :
    0 < coefficient e := by
  apply prod_pos
  intro j _
  exact inv_pos.mpr (Nat.cast_pos.mpr (prefix_card_pos hL e j))

theorem edge_isEmpty {n L : ℕ} (h : n < L) : IsEmpty (Edge n L) := by
  refine ⟨fun e => ?_⟩
  have hc := card_le_univ e.val
  rw [e.property, Fintype.card_fin] at hc
  omega

theorem simplex_empty {n L : ℕ} (h : n < L) : simplex n L = ∅ := by
  let := edge_isEmpty h
  ext x
  simp [simplex]

theorem source_convex_empty {n L d : ℕ} (h : n < L) :
    ConvexOn ℝ (simplex n L) (sourcePolynomial n L d) := by
  rw [simplex_empty h]
  exact ⟨convex_empty, by simp⟩

theorem prefixUnion_constant {n L d : ℕ} (e : Edge n L) (j : Fin d) :
    prefixUnion (fun _ : Fin d => e) j = e.val := by
  ext v
  rw [mem_prefixUnion]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨j, le_rfl, h⟩⟩

/-- Control on repeated-edge coefficients: no stabilizer or factorial appears. -/
theorem coefficient_constant {n L d : ℕ} (e : Edge n L) :
    coefficient (fun _ : Fin d => e) = (L : ℝ)⁻¹ ^ d := by
  simp [coefficient, prefixUnion_constant, e.property]

end
end PolynomialConvexity
