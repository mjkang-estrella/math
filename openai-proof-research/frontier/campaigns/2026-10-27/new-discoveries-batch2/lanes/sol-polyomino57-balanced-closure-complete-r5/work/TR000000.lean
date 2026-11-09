import Terminal079
import F11B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem tr0_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(0,-5), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10)],(0,-5)) (.leaf Terminal079c30) := List.mem_of_getElem? (i := 23) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c30) Terminal079c30_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10)],(0,-5)) hm
  have he : translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10)] : List GridPoint).toFinset = translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr1_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,0)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(0,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,0)],(0,-4)) (.leaf Terminal079c30) := List.mem_of_getElem? (i := 24) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c30) Terminal079c30_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,0)],(0,-4)) hm
  have he : translate (0,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,0)] : List GridPoint).toFinset = translate (0,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,0)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr2_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,1)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(0,-5), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,1)],(0,-5)) (.leaf Terminal079c30) := List.mem_of_getElem? (i := 25) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c30) Terminal079c30_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,1)],(0,-5)) hm
  have he : translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,1)] : List GridPoint).toFinset = translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,1)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr3_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,2)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(0,-5), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,2)],(0,-5)) (.leaf Terminal079c30) := List.mem_of_getElem? (i := 26) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c30) Terminal079c30_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,2)],(0,-5)) hm
  have he : translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,2)] : List GridPoint).toFinset = translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,2)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr4_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,3)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(0,-5), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,3)],(0,-5)) (.leaf Terminal079c30) := List.mem_of_getElem? (i := 27) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c30) Terminal079c30_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,3)],(0,-5)) hm
  have he : translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,3)] : List GridPoint).toFinset = translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,3)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr5_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,4)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(0,-5), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,4)],(0,-5)) (.leaf Terminal079c30) := List.mem_of_getElem? (i := 28) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c30) Terminal079c30_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,4)],(0,-5)) hm
  have he : translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,4)] : List GridPoint).toFinset = translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,4)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr6_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,5)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(0,-5), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,5)],(0,-5)) (.leaf Terminal079c30) := List.mem_of_getElem? (i := 29) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c30) Terminal079c30_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,5)],(0,-5)) hm
  have he : translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,5)] : List GridPoint).toFinset = translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,5)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr7_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,6)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(0,-5), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,6)],(0,-5)) (.leaf Terminal079c30) := List.mem_of_getElem? (i := 30) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c30) Terminal079c30_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,6)],(0,-5)) hm
  have he : translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,6)] : List GridPoint).toFinset = translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,6)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr8_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,7)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(0,-5), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,7)],(0,-5)) (.leaf Terminal079c30) := List.mem_of_getElem? (i := 31) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c30) Terminal079c30_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,7)],(0,-5)) hm
  have he : translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,7)] : List GridPoint).toFinset = translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,7)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr9_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,8)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(0,-5), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,8)],(0,-5)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 0) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,8)],(0,-5)) hm
  have he : translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,8)] : List GridPoint).toFinset = translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,8)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr10_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,9)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(0,-5), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,9)],(0,-5)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 1) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,9)],(0,-5)) hm
  have he : translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,9)] : List GridPoint).toFinset = translate (0,-5) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,9)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr11_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 2) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr12_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,2)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,2)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 3) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,2)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,2)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,2)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr13_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,3)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,3)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 4) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,3)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,3)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,3)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr14_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,4)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,4)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 5) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,4)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,4)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,4)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr15_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,5)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,5)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 6) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,5)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,5)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,5)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr16_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,6)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,6)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 7) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,6)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,6)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,6)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr17_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,7)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,7)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 8) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,7)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,7)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,7)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr18_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,8)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,8)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 9) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,8)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,8)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,8)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr19_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(2,0)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(2,0)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 10) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(2,0)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(2,0)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(2,0)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr20_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,2)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,2)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 11) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,2)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,2)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,2)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr21_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,3)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,3)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 12) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,3)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,3)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,3)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr22_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,4)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,4)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 13) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,4)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,4)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,4)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr23_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,5)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,5)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 14) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,5)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,5)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,5)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr24_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,6)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,6)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 15) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,6)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,6)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,6)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr25_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,7)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,7)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 16) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,7)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,7)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,7)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr26_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,8)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,8)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 17) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,8)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,8)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,8)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr27_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(2,1)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(2,1)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 18) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(2,1)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(2,1)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(2,1)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr28_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,3)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,3)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 19) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,3)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,3)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,3)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr29_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,4)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,4)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 20) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,4)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,4)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,4)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr30_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,5)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,5)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 21) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,5)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,5)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,5)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem tr31_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,6)] : List GridPoint).toFinset ⊆ witness := by
  refine ⟨(-1,-4), ?_⟩
  have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,6)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 22) (by rfl)
  have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,6)],(-1,-4)) hm
  have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,6)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,6)] : List GridPoint).toFinset := by decide
  rw [he]
  exact hs
theorem TR000000_placed (row : List GridPoint) (h : FamilyMember row F11B000L0) : ∃ t, translate t row.toFinset ⊆ witness := by
  simp only [F11B000L0, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact tr0_placed
  · subst row; exact tr1_placed
  · subst row; exact tr2_placed
  · subst row; exact tr3_placed
  · subst row; exact tr4_placed
  · subst row; exact tr5_placed
  · subst row; exact tr6_placed
  · subst row; exact tr7_placed
  · subst row; exact tr8_placed
  · subst row; exact tr9_placed
  · subst row; exact tr10_placed
  · subst row; exact tr11_placed
  · subst row; exact tr12_placed
  · subst row; exact tr13_placed
  · subst row; exact tr14_placed
  · subst row; exact tr15_placed
  · subst row; exact tr16_placed
  · subst row; exact tr17_placed
  · subst row; exact tr18_placed
  · subst row; exact tr19_placed
  · subst row; exact tr20_placed
  · subst row; exact tr21_placed
  · subst row; exact tr22_placed
  · subst row; exact tr23_placed
  · subst row; exact tr24_placed
  · subst row; exact tr25_placed
  · subst row; exact tr26_placed
  · subst row; exact tr27_placed
  · subst row; exact tr28_placed
  · subst row; exact tr29_placed
  · subst row; exact tr30_placed
  · subst row; exact tr31_placed
end Polyomino57
