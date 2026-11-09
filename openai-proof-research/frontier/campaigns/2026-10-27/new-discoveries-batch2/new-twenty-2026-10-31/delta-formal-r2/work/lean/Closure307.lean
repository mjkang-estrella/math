import Closure306
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1228 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 2], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [2, 0, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower1228 : ∀ h, Pure node1228 h → 11 ≤ h.length := by
  apply indexed_extend node1228 [(0, node921), (2, node734), (3, node376), (6, node483)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower921
  · exact lower734
  · exact lower376
  · exact lower483
def node1229 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower1229 : ∀ h, Pure node1229 h → 11 ≤ h.length := by
  apply indexed_extend node1229 [(0, node922), (2, node735), (3, node377), (7, node484), (10, node588)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower922
  · exact lower735
  · exact lower377
  · exact lower484
  · exact lower588
def node1230 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1230 : ∀ h, Pure node1230 h → 11 ≤ h.length := by
  apply indexed_extend node1230 [(0, node923), (2, node736), (9, node483), (12, node481), (13, node478)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower923
  · exact lower736
  · exact lower483
  · exact lower481
  · exact lower478
def node1231 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 2, 0, 0]]
theorem lower1231 : ∀ h, Pure node1231 h → 11 ≤ h.length := by
  apply indexed_extend node1231 [(0, node924), (2, node737), (3, node378), (9, node484), (10, node602), (12, node482)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower924
  · exact lower737
  · exact lower378
  · exact lower484
  · exact lower602
  · exact lower482
def entries307 : List Graph := [node1228, node1229, node1230, node1231]
theorem entries_count307 : entries307.length = 4 := by decide +kernel
theorem arc_count307 : (entries307.map (fun g => ((verts g).filter (wye g)).length)).sum = 20 := by decide +kernel
end RawCert
