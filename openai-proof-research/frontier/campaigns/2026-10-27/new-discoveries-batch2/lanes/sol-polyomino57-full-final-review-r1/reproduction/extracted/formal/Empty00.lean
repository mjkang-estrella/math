import FiniteBridge
set_option autoImplicit false
namespace Polyomino57.Diagonal.FiniteProof
open Polyomino57
theorem empty_1_1_0 : ∅ ∈ groups 1 1 0 := by
  have hc : (-4,-4) ∈ centers 1 1 0 := by decide
  have hg : collisionGroup 1 1 0 (-4,-4) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hd := (mem_domain (by omega) (by omega) (by omega) p).mp
      ((mem_collisionGroup 1 1 0 (-4,-4) p).mp hp).1
    have hh := ((mem_collisionGroup 1 1 0 (-4,-4) p).mp hp).2
    dsimp [Collision,u,v] at *
    omega
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(-4,-4),hc,rfl⟩)
theorem case_1_1_0 : ∀ Q : Finset GridPoint, Q ⊆ domain 1 1 0 →
    EdgeConnected Q → Q.card = 11 → ¬ HitsAll Q (groups 1 1 0) := by
  intro Q _ _ _
  exact empty_group_impossible empty_1_1_0
end Polyomino57.Diagonal.FiniteProof
