import Finite
import Mathlib.LinearAlgebra.Pi
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option warningAsError true
namespace Cube
def point (v : V) : Fin 5 → ℝ := fun i => (zcoord v i : ℝ)
theorem point_injective : Function.Injective point := by
  have h : ∀ x y : V, (∀ i, zcoord x i = zcoord y i) → x = y := by decide
  intro x y he
  apply h x y
  intro i
  have hi := congrFun he i
  change (zcoord x i : ℝ) = (zcoord y i : ℝ) at hi
  exact_mod_cast hi
theorem pairRel_real (x y u v : V) :
    pairRel x y u v ↔ point x + point y = point u + point v := by
  simp only [pairRel, funext_iff, Pi.add_apply, point]
  constructor <;> intro h i <;> exact_mod_cast h i
theorem rel_preserved (e : V ≃ V) (A : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ))
    (ha : ∀ v, A (point v) = point (e v)) (x y u v : V) :
    pairRel (e x) (e y) (e u) (e v) ↔ pairRel x y u v := by
  rw [pairRel_real, pairRel_real, ← ha, ← ha, ← ha, ← ha, ← map_add, ← map_add]
  exact A.injective.eq_iff
theorem weight_preserved (e : V ≃ V) (hr : ∀ x y u v, pairRel (e x) (e y) (e u) (e v) ↔ pairRel x y u v)
    (x y : V) : weight (e x) (e y) = weight x y := by
  unfold weight
  symm
  apply Finset.card_bij (fun p _ => (e p.1, e p.2))
  · intro p hp
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hr] using hp
  · intro p hp q hq h
    exact Prod.ext (e.injective (congrArg Prod.fst h)) (e.injective (congrArg Prod.snd h))
  · intro q hq
    refine ⟨(e.symm q.1, e.symm q.2), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply (hr x y (e.symm q.1) (e.symm q.2)).mp
      simpa using (Finset.mem_filter.mp hq).2
    · simp
end Cube
