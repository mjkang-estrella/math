import FiniteBridge
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Polyomino57.Diagonal.FiniteProof
open Polyomino57
theorem forced_single0 : ({(0,0)} : Finset GridPoint) ∈ groups 7 3 0 := by
  have hc : (4,0) ∈ centers 7 3 0 := by decide
  have hg : collisionGroup 7 3 0 (4,0) = {(0,0)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(4,0),hc,rfl⟩)
theorem forced_single1 : ({(1,-1)} : Finset GridPoint) ∈ groups 7 3 0 := by
  have hc : (4,2) ∈ centers 7 3 0 := by decide
  have hg : collisionGroup 7 3 0 (4,2) = {(1,-1)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(4,2),hc,rfl⟩)
theorem forced_single2 : ({(1,0)} : Finset GridPoint) ∈ groups 7 3 0 := by
  have hc : (5,1) ∈ centers 7 3 0 := by decide
  have hg : collisionGroup 7 3 0 (5,1) = {(1,0)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(5,1),hc,rfl⟩)
theorem forced_single3 : ({(1,1)} : Finset GridPoint) ∈ groups 7 3 0 := by
  have hc : (2,4) ∈ centers 7 3 0 := by decide
  have hg : collisionGroup 7 3 0 (2,4) = {(1,1)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(2,4),hc,rfl⟩)
theorem forced_single4 : ({(2,-1)} : Finset GridPoint) ∈ groups 7 3 0 := by
  have hc : (5,3) ∈ centers 7 3 0 := by decide
  have hg : collisionGroup 7 3 0 (5,3) = {(2,-1)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(5,3),hc,rfl⟩)
theorem forced_single5 : ({(2,0)} : Finset GridPoint) ∈ groups 7 3 0 := by
  have hc : (2,-2) ∈ centers 7 3 0 := by decide
  have hg : collisionGroup 7 3 0 (2,-2) = {(2,0)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(2,-2),hc,rfl⟩)
theorem forced_single6 : ({(2,1)} : Finset GridPoint) ∈ groups 7 3 0 := by
  have hc : (3,5) ∈ centers 7 3 0 := by decide
  have hg : collisionGroup 7 3 0 (3,5) = {(2,1)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(3,5),hc,rfl⟩)
theorem forced_single7 : ({(2,2)} : Finset GridPoint) ∈ groups 7 3 0 := by
  have hc : (4,4) ∈ centers 7 3 0 := by decide
  have hg : collisionGroup 7 3 0 (4,4) = {(2,2)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(4,4),hc,rfl⟩)
theorem forced_single8 : ({(3,0)} : Finset GridPoint) ∈ groups 7 3 0 := by
  have hc : (3,-1) ∈ centers 7 3 0 := by decide
  have hg : collisionGroup 7 3 0 (3,-1) = {(3,0)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(3,-1),hc,rfl⟩)
theorem forced_single9 : ({(3,1)} : Finset GridPoint) ∈ groups 7 3 0 := by
  have hc : (4,-2) ∈ centers 7 3 0 := by decide
  have hg : collisionGroup 7 3 0 (4,-2) = {(3,1)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(4,-2),hc,rfl⟩)
theorem forced_single10 : ({(3,2)} : Finset GridPoint) ∈ groups 7 3 0 := by
  have hc : (5,5) ∈ centers 7 3 0 := by decide
  have hg : collisionGroup 7 3 0 (5,5) = {(3,2)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(5,5),hc,rfl⟩)
theorem forced_single11 : ({(3,3)} : Finset GridPoint) ∈ groups 7 3 0 := by
  have hc : (2,0) ∈ centers 7 3 0 := by decide
  have hg : collisionGroup 7 3 0 (2,0) = {(3,3)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(2,0),hc,rfl⟩)
theorem forced_single12 : ({(4,1)} : Finset GridPoint) ∈ groups 7 3 0 := by
  have hc : (5,-1) ∈ centers 7 3 0 := by decide
  have hg : collisionGroup 7 3 0 (5,-1) = {(4,1)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(5,-1),hc,rfl⟩)
theorem forced_single13 : ({(4,2)} : Finset GridPoint) ∈ groups 7 3 0 := by
  have hc : (2,2) ∈ centers 7 3 0 := by decide
  have hg : collisionGroup 7 3 0 (2,2) = {(4,2)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(2,2),hc,rfl⟩)
theorem forced_single14 : ({(4,3)} : Finset GridPoint) ∈ groups 7 3 0 := by
  have hc : (3,1) ∈ centers 7 3 0 := by decide
  have hg : collisionGroup 7 3 0 (3,1) = {(4,3)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(3,1),hc,rfl⟩)
theorem forced_single15 : ({(5,2)} : Finset GridPoint) ∈ groups 7 3 0 := by
  have hc : (3,3) ∈ centers 7 3 0 := by decide
  have hg : collisionGroup 7 3 0 (3,3) = {(5,2)} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(3,3),hc,rfl⟩)
def forced : Finset GridPoint := {(0,0),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3),(5,2)}
theorem forced_sub {Q : Finset GridPoint} (hh : HitsAll Q (groups 7 3 0)) : forced ⊆ Q := by
  intro p hp
  have h : ∀ p ∈ forced, ({p} : Finset GridPoint) ∈ groups 7 3 0 := by
    intro p hp
    simp only [forced, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact forced_single0
    · exact forced_single1
    · exact forced_single2
    · exact forced_single3
    · exact forced_single4
    · exact forced_single5
    · exact forced_single6
    · exact forced_single7
    · exact forced_single8
    · exact forced_single9
    · exact forced_single10
    · exact forced_single11
    · exact forced_single12
    · exact forced_single13
    · exact forced_single14
    · exact forced_single15
  obtain ⟨q,hq,hqp⟩ := hh {p} (h p hp)
  have he : q = p := Finset.mem_singleton.mp hqp
  exact he ▸ hq
theorem case_7_3_0 : ∀ Q : Finset GridPoint, Q ⊆ domain 7 3 0 → EdgeConnected Q →
    Q.card = 11 → ¬ HitsAll Q (groups 7 3 0) := by
  intro Q _ _ hn hh
  have h := Finset.card_le_card (forced_sub hh)
  have hf : forced.card = 16 := by decide
  omega
end Polyomino57.Diagonal.FiniteProof
