import Terminal079
import Terminal080
import F11B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem TR000032_placed (row : List GridPoint) (h : FamilyMember row F11B000L1) : ∃ t, translate t row.toFinset ⊆ witness := by
  have tr32_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,7)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,7)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 23) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,7)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,7)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,7)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr33_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,8)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,8)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 24) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,8)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,8)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,8)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr34_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(2,2)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(2,2)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 25) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(2,2)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(2,2)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(2,2)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr35_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,4)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,4)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 26) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,4)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,4)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,4)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr36_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,5)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,5)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 27) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,5)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,5)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,5)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr37_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,6)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,6)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 28) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,6)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,6)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,6)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr38_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,7)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,7)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 29) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,7)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,7)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,7)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr39_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,8)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,8)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 30) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,8)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,8)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,8)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr40_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(2,3)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(2,3)],(-1,-4)) (.leaf Terminal079c31) := List.mem_of_getElem? (i := 31) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal079c31) Terminal079c31_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(2,3)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(2,3)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(2,3)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr41_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,5)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,5)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 0) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,5)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,5)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,5)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr42_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,6)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,6)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 1) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,6)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,6)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,6)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr43_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,7)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,7)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 2) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,7)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,7)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,7)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr44_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,8)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,8)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 3) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,8)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,8)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,8)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr45_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(2,4)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(2,4)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 4) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(2,4)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(2,4)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(2,4)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr46_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,6)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,6)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 5) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,6)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,6)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,6)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr47_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,7)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,7)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 6) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,7)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,7)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,7)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr48_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,8)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,8)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 7) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,8)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,8)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,8)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr49_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(2,5)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(2,5)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 8) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(2,5)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(2,5)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(2,5)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr50_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(1,7)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(1,7)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 9) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(1,7)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(1,7)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(1,7)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr51_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(1,8)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(1,8)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 10) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(1,8)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(1,8)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(1,8)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr52_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(2,6)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(2,6)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 11) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(2,6)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(2,6)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(2,6)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr53_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,7),(1,8)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,7),(1,8)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 12) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,7),(1,8)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,7),(1,8)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,7),(1,8)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr54_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,7),(2,7)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,7),(2,7)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 13) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,7),(2,7)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,7),(2,7)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,7),(2,7)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr55_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,8),(1,9)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,8),(1,9)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 14) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,8),(1,9)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,8),(1,9)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,8),(1,9)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr56_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,8),(2,8)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,8),(2,8)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 15) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,8),(2,8)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,8),(2,8)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,8),(2,8)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr57_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 16) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr58_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,3)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,3)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 17) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,3)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,3)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,3)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr59_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,4)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,4)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 18) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,4)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,4)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,4)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr60_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,5)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,5)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 19) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,5)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,5)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,5)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr61_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,6)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,6)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 20) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,6)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,6)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,6)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr62_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,7)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,7)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 21) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,7)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,7)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,7)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  have tr63_placed : ∃ t, translate t ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(2,0)] : List GridPoint).toFinset ⊆ witness := by
    refine ⟨(-1,-4), ?_⟩
    have hm : TreeMember ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(2,0)],(-1,-4)) (.leaf Terminal080c0) := List.mem_of_getElem? (i := 22) (by rfl)
    have hs := treeCheck_sound (.leaf Terminal080c0) Terminal080c0_checked ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(2,0)],(-1,-4)) hm
    have he : translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(2,0)] : List GridPoint).toFinset = translate (-1,-4) ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(2,0)] : List GridPoint).toFinset := by decide
    rw [he]
    exact hs
  simp only [F11B000L1, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact tr32_placed
  · subst row; exact tr33_placed
  · subst row; exact tr34_placed
  · subst row; exact tr35_placed
  · subst row; exact tr36_placed
  · subst row; exact tr37_placed
  · subst row; exact tr38_placed
  · subst row; exact tr39_placed
  · subst row; exact tr40_placed
  · subst row; exact tr41_placed
  · subst row; exact tr42_placed
  · subst row; exact tr43_placed
  · subst row; exact tr44_placed
  · subst row; exact tr45_placed
  · subst row; exact tr46_placed
  · subst row; exact tr47_placed
  · subst row; exact tr48_placed
  · subst row; exact tr49_placed
  · subst row; exact tr50_placed
  · subst row; exact tr51_placed
  · subst row; exact tr52_placed
  · subst row; exact tr53_placed
  · subst row; exact tr54_placed
  · subst row; exact tr55_placed
  · subst row; exact tr56_placed
  · subst row; exact tr57_placed
  · subst row; exact tr58_placed
  · subst row; exact tr59_placed
  · subst row; exact tr60_placed
  · subst row; exact tr61_placed
  · subst row; exact tr62_placed
  · subst row; exact tr63_placed
end Polyomino57
