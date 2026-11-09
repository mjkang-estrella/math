import Foundation
set_option autoImplicit false
open scoped BigOperators
namespace WheelFormal

/-- Unnormalised dual weight in the ordinary proof. -/
def vertexWeight (t : ℕ) (v : Option (ZMod (2*t+1)) × Option (ZMod (2*t+1))) : ℝ :=
  match v with
  | (none, none) => 2
  | (some _, none) => (t:ℝ)+1
  | (none, some _) => (t:ℝ)+1
  | (some _, some _) => 2

theorem vertexWeight_nonnegative (t : ℕ)
    (v : Option (ZMod (2*t+1)) × Option (ZMod (2*t+1))) :
    0 ≤ vertexWeight t v := by
  rcases v with ⟨a,b⟩
  cases a <;> cases b <;> simp [vertexWeight] <;> positivity

theorem vertexWeight_total (t : ℕ) :
    (∑ v, vertexWeight t v) = 2*(6*(t:ℝ)^2+7*(t:ℝ)+3) := by
  classical
  simp [Fintype.sum_prod_type, Fintype.sum_option, vertexWeight, ZMod.card]
  ring

theorem hub_excludes_mixed (t : ℕ)
    (s : Finset (Option (ZMod (2*t+1)) × Option (ZMod (2*t+1))))
    (hs : Independent (wheelSquare t) s) (hh : (none,none) ∈ s)
    (i : ZMod (2*t+1)) :
    (some i,none) ∉ s ∧ (none,some i) ∉ s := by
  constructor
  · intro hi
    have h := hs (none,none) hh (some i,none) hi (by simp)
    exact h (by simp [wheelSquare, SimpleGraph.boxProd, wheel])
  · intro hi
    have h := hs (none,none) hh (none,some i) hi (by simp)
    exact h (by simp [wheelSquare, SimpleGraph.boxProd, wheel])

/-- Restriction to every rim fibre is independent in the actual cyclic rim graph. -/
theorem rim_fibre_independent (t : ℕ)
    (s : Finset (Option (ZMod (2*t+1)) × Option (ZMod (2*t+1))))
    (hs : Independent (wheelSquare t) s)
    (i j k : ZMod (2*t+1))
    (hj : (some i,some j) ∈ s) (hk : (some i,some k) ∈ s)
    (hjk : j ≠ k) : ¬ rimAdj (2*t+1) j k := by
  intro h
  exact hs _ hj _ hk (by simpa using hjk)
    (by simp [wheelSquare, SimpleGraph.boxProd, wheel, h])
end WheelFormal
