import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

open scoped BigOperators
namespace MonochromaticBox

variable {α C : Type*} [Fintype α] [DecidableEq α] [Fintype C] [DecidableEq C]

/-- Positions at which both colorings use the specified color. -/
def commonFiber (f g : α → C) (c : C) : Finset α :=
  Finset.univ.filter (fun a => f a = c ∧ g a = c)

/-- The source matrix, generalized from two colors and pairs to any finite color set and k. -/
def boxMatrix (k : ℕ) : Matrix (α → C) (α → C) ℝ :=
  fun f g => ∑ c : C, ((commonFiber f g c).card.choose k : ℝ)

/-- Incidence of a coloring with a monochromatic k-element feature. -/
def incidence (k : ℕ) : Matrix (α → C) (C × Finset α) ℝ :=
  fun f p => if p.2.card = k ∧ ∀ a ∈ p.2, f a = p.1 then 1 else 0

omit [Fintype C] in
theorem feature_count (k : ℕ) (f g : α → C) (c : C) :
    (∑ t : Finset α, incidence k f (c,t) * incidence k g (c,t)) =
      ((commonFiber f g c).card.choose k : ℝ) := by
  have ht (t : Finset α) :
      incidence k f (c,t) * incidence k g (c,t) =
      if t ∈ (commonFiber f g c).powersetCard k then (1 : ℝ) else 0 := by
    simp only [incidence, Finset.mem_powersetCard, commonFiber, Finset.subset_iff,
      Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : t.card = k <;> simp only [h, false_and, ite_false, zero_mul, and_false]
    · by_cases hf : ∀ a ∈ t, f a = c <;> by_cases hg : ∀ a ∈ t, g a = c <;>
        simp_all
      all_goals aesop
  simp_rw [ht]
  rw [Finset.sum_boole]
  have hf : (Finset.univ.filter fun t => t ∈ (commonFiber f g c).powersetCard k) =
      (commonFiber f g c).powersetCard k := by ext; simp
  rw [hf, Finset.card_powersetCard]

theorem gram_identity (k : ℕ) :
    boxMatrix (α := α) (C := C) k = incidence k * (incidence k).conjTranspose := by
  ext f g
  simp only [boxMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun c _ => (feature_count k f g c).symm)

theorem boxMatrix_posSemidef (k : ℕ) :
    (boxMatrix (α := α) (C := C) k).PosSemidef := by
  rw [gram_identity]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- Literal two-summand entry formula of the source, with colors relabeled 0 and 1. -/
def sourceMatrix (r : ℕ) : Matrix (Fin r → Fin 2) (Fin r → Fin 2) ℝ :=
  fun f g => ((Finset.univ.filter (fun a => f a = 0 ∧ g a = 0)).card.choose 2 : ℝ) +
    ((Finset.univ.filter (fun a => f a = 1 ∧ g a = 1)).card.choose 2 : ℝ)

theorem sourceMatrix_eq_boxMatrix (r : ℕ) :
    sourceMatrix r = boxMatrix (α := Fin r) (C := Fin 2) 2 := by
  ext f g
  simp [sourceMatrix, boxMatrix, commonFiber, Fin.sum_univ_two]

/-- Exact source conjecture, with the unnecessary restriction r ≥ 3 removed. -/
theorem mathdb317856 (r : ℕ) : (sourceMatrix r).PosSemidef := by
  rw [sourceMatrix_eq_boxMatrix]
  exact boxMatrix_posSemidef 2

end MonochromaticBox
