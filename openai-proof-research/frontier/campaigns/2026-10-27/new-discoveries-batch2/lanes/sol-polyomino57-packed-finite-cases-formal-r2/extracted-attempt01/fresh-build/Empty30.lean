import FiniteBridge
set_option autoImplicit false
namespace Polyomino57.Diagonal.FiniteProof
open Polyomino57
theorem empty_8_2_1 : ∅ ∈ groups 8 2 1 := by
  have hc : (4,0) ∈ centers 8 2 1 := by decide
  have hg : collisionGroup 8 2 1 (4,0) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hd := (mem_domain (by omega) (by omega) (by omega) p).mp
      ((mem_collisionGroup 8 2 1 (4,0) p).mp hp).1
    have hh := ((mem_collisionGroup 8 2 1 (4,0) p).mp hp).2
    dsimp [Collision,u,v] at *
    omega
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(4,0),hc,rfl⟩)
theorem case_8_2_1 : ∀ Q : Finset GridPoint, Q ⊆ domain 8 2 1 →
    EdgeConnected Q → Q.card = 11 → ¬ HitsAll Q (groups 8 2 1) := by
  intro Q _ _ _
  exact empty_group_impossible empty_8_2_1
end Polyomino57.Diagonal.FiniteProof
