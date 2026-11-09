import Signed
open MathDB364205
example : signedDist (cubeEquiv 2 (fun _ => false)) (cubeEquiv 2 (fun _ => true)) = 2 := by decide
example : signedDist (cubeEquiv 0 (fun _ => false)) (cubeEquiv 0 (fun _ => true)) = 0 := by decide
example : dist (vertex 0) (vertex 217) = 5 := by decide
example {n r : ℕ} {S : Finset (Cube n)} (h : MaximalDiameter S r) :
    (∃ x ∈ S, ∃ y ∈ S, dist x y = r) := h.2.1
example {n r : ℕ} {S T : Finset (Cube n)} (h : MaximalDiameter S r)
    (hst : S ⊆ T) (ht : ∀ x ∈ T, ∀ y ∈ T, dist x y ≤ r) : T = S := by
  apply Finset.Subset.antisymm
  · intro x hx
    by_contra hn
    obtain ⟨y, hy, hd⟩ := h.2.2 x hn
    exact Nat.not_lt_of_ge (ht x hx y (hst hy)) hd
  · exact hst
example : MaximalDiameter ({fun _ : Fin 0 => false} : Finset (Cube 0)) 0 := by unfold MaximalDiameter MathDB364205.dist; decide
example : Rigid ({fun _ : Fin 0 => false} : Finset (Cube 0)) 0 := by unfold Rigid MathDB364205.dist; decide
example : ¬ MaximalDiameter (∅ : Finset (Cube 0)) 0 := by unfold MaximalDiameter MathDB364205.dist; decide
