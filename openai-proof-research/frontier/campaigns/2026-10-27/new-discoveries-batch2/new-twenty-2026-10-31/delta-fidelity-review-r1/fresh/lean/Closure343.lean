import Closure342
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1372 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1372 : ∀ h, Pure node1372 h → 11 ≤ h.length := by
  apply indexed_extend node1372 [(1, node847), (2, node840), (7, node600)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower847
  · exact lower840
  · exact lower600
def node1373 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 1, 0]]
theorem lower1373 : ∀ h, Pure node1373 h → 11 ≤ h.length := by
  apply indexed_extend node1373 [(1, node848), (2, node841), (7, node601), (9, node586)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower848
  · exact lower841
  · exact lower601
  · exact lower586
def node1374 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 2, 0, 0]]
theorem lower1374 : ∀ h, Pure node1374 h → 11 ≤ h.length := by
  apply indexed_extend node1374 [(1, node849), (2, node842), (4, node641), (7, node602), (10, node586), (12, node596)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower849
  · exact lower842
  · exact lower641
  · exact lower602
  · exact lower586
  · exact lower596
def node1375 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 1, 0], [1, 0, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower1375 : ∀ h, Pure node1375 h → 11 ≤ h.length := by
  apply indexed_extend node1375 [(2, node843), (6, node599), (9, node587), (13, node597)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower843
  · exact lower599
  · exact lower587
  · exact lower597
def entries343 : List Graph := [node1372, node1373, node1374, node1375]
theorem entries_count343 : entries343.length = 4 := by decide +kernel
theorem arc_count343 : (entries343.map (fun g => ((verts g).filter (wye g)).length)).sum = 17 := by decide +kernel
end RawCert
