import ForcedBridge
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace F830
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof
def forced : Finset GridPoint := {(1,0),(2,-1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,3),(5,2)}
def free : Finset GridPoint := {(0,0),(1,-1),(1,1),(2,0),(3,3),(4,2),(4,4),(5,3)}
def miss : Finset GridPoint := {(2,-1)}
theorem single0 : ({(1,0)} : Finset GridPoint) ∈ groups 8 3 0 := by
  have hc : (5,1) ∈ centers 8 3 0 := by decide
  have hg : collisionGroup 8 3 0 (5,1) = {(1,0)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hc,rfl⟩)
theorem single1 : ({(2,-1)} : Finset GridPoint) ∈ groups 8 3 0 := by
  have hc : (5,3) ∈ centers 8 3 0 := by decide
  have hg : collisionGroup 8 3 0 (5,3) = {(2,-1)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hc,rfl⟩)
theorem single2 : ({(2,1)} : Finset GridPoint) ∈ groups 8 3 0 := by
  have hc : (3,5) ∈ centers 8 3 0 := by decide
  have hg : collisionGroup 8 3 0 (3,5) = {(2,1)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hc,rfl⟩)
theorem single3 : ({(2,2)} : Finset GridPoint) ∈ groups 8 3 0 := by
  have hc : (4,4) ∈ centers 8 3 0 := by decide
  have hg : collisionGroup 8 3 0 (4,4) = {(2,2)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hc,rfl⟩)
theorem single4 : ({(3,0)} : Finset GridPoint) ∈ groups 8 3 0 := by
  have hc : (3,-1) ∈ centers 8 3 0 := by decide
  have hg : collisionGroup 8 3 0 (3,-1) = {(3,0)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hc,rfl⟩)
theorem single5 : ({(3,1)} : Finset GridPoint) ∈ groups 8 3 0 := by
  have hc : (4,-2) ∈ centers 8 3 0 := by decide
  have hg : collisionGroup 8 3 0 (4,-2) = {(3,1)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hc,rfl⟩)
theorem single6 : ({(3,2)} : Finset GridPoint) ∈ groups 8 3 0 := by
  have hc : (5,5) ∈ centers 8 3 0 := by decide
  have hg : collisionGroup 8 3 0 (5,5) = {(3,2)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hc,rfl⟩)
theorem single7 : ({(4,1)} : Finset GridPoint) ∈ groups 8 3 0 := by
  have hc : (5,-1) ∈ centers 8 3 0 := by decide
  have hg : collisionGroup 8 3 0 (5,-1) = {(4,1)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hc,rfl⟩)
theorem single8 : ({(4,3)} : Finset GridPoint) ∈ groups 8 3 0 := by
  have hc : (3,1) ∈ centers 8 3 0 := by decide
  have hg : collisionGroup 8 3 0 (3,1) = {(4,3)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hc,rfl⟩)
theorem single9 : ({(5,2)} : Finset GridPoint) ∈ groups 8 3 0 := by
  have hc : (3,3) ∈ centers 8 3 0 := by decide
  have hg : collisionGroup 8 3 0 (3,3) = {(5,2)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hc,rfl⟩)
theorem forced_sub {Q : Finset GridPoint} (hh : HitsAll Q (groups 8 3 0)) : forced ⊆ Q := by
  have hs : ∀ p ∈ forced, ({p} : Finset GridPoint) ∈ groups 8 3 0 := by
    intro p hp
    simp only [forced, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact single0
    · exact single1
    · exact single2
    · exact single3
    · exact single4
    · exact single5
    · exact single6
    · exact single7
    · exact single8
    · exact single9
  intro p hp
  obtain ⟨q,hq,hqp⟩ := hh {p} (hs p hp)
  exact (Finset.mem_singleton.mp hqp) ▸ hq
theorem domain_parts : domain 8 3 0 = forced ∪ free := by decide
theorem parts_disjoint : Disjoint forced free := by decide
theorem forced_card : forced.card = 10 := by decide
theorem miss_group : miss ∈ groups 8 3 0 := by decide

end F830
