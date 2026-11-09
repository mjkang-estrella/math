import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.Pi

/-!
# MathDB 343790: failure of degree-and-type uniqueness for code loops

Literal endpoint for MathDB problem 343790 (Miguel Pires, Grishkov, Rasskazova,
arXiv:1909.05143, Conjecture 1): two representations of one code loop with equal
degree and equal type need not be isomorphic as binary codes.
-/

/-- standard dot product on `Fin n → ZMod 2` -/
def dot {n : ℕ} (v w : Fin n → ZMod 2) : ZMod 2 := ∑ i, v i * w i

theorem dot_add (v w u : Fin n → ZMod 2) : dot v (w + u) = dot v w + dot v u := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The module instance underlying `Submodule ZMod 2 (Fin 50 → ZMod 2)`. -/
example : Module (ZMod 2) (Fin 50 → ZMod 2) := inferInstance
