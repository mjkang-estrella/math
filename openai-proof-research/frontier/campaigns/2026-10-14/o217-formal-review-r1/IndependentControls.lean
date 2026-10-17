/- Independent reviewer controls. Original code MIT. -/
import O217
namespace IndependentO217
open O217

def e01 : Edge 2 := ⟨(0, 1), by decide⟩
theorem edge2_unique (e : Edge 2) : e = e01 := by
  exact (by decide : ∀ f : Edge 2, f = e01) e

theorem empty_star (x : Edge 2 → ℝ) : flipStar 0 e01 x = x := by
  funext e
  rw [edge2_unique e]
  simp [flipStar]

theorem n2_observable_cubic_zero (Ψ : ℝ → ℝ) (q : ℝ) (x : Edge 2 → ℝ) :
    thirdDerivObservable Ψ q x e01 = 0 := by
  have h := thirdDerivObservable_flipStar_odd Ψ q x 0 e01 (by decide)
  rw [empty_star] at h
  linarith

theorem n2_log_cubic_zero (q : ℝ) (x : Edge 2 → ℝ) :
    thirdDerivLog q x e01 = 0 := by
  have h := thirdDerivLog_flipStar_odd q x 0 e01 (by decide)
  rw [empty_star] at h
  linarith

def e12 : Edge 3 := ⟨(1,2), by decide⟩
theorem nonincident_not_negated :
    edgeSpin (flipSpin 0 (fun _ : Fin 3 => false)) e12 = 1 := by
  norm_num [edgeSpin,flipSpin,spinSign,e12]

theorem square_negative_z_endpoint :
    |((-1 : ℝ) + (-1)^2)^2 - 1^2*(-1)^2 - 1*2*(-1)^3| ≤ (2*1*0+1^2)*|-1|^4 := by
  norm_num

theorem zero_constant_bootstrap (M V : ℝ) (hM : 0 ≤ M) (hV : 0 ≤ V)
    (h : M ≤ V) : Real.sqrt M ≤ Real.sqrt V := by
  simpa using quadratic_bootstrap M V 0 hM hV (by norm_num) (by simpa using h)

theorem low_size_cardinalities :
    Fintype.card (Edge 0) = 0 ∧ Fintype.card (Edge 1) = 0 ∧ Fintype.card (Edge 2) = 1 := by
  norm_num [edge_card]

#print axioms edge2_unique
#print axioms empty_star
#print axioms n2_observable_cubic_zero
#print axioms n2_log_cubic_zero
#print axioms nonincident_not_negated
#print axioms square_negative_z_endpoint
#print axioms zero_constant_bootstrap
#print axioms low_size_cardinalities
end IndependentO217
