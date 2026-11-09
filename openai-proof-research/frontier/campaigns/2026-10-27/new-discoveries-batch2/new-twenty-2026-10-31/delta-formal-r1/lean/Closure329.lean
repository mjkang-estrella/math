import Closure328
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1316 : Graph := [[0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0], [0, 0, 0, 2, 1, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower1316 : ∀ h, Pure node1316 h → 11 ≤ h.length := by
  apply indexed_extend node1316 [(0, node906), (1, node792), (3, node521), (10, node641), (12, node559)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower906
  · exact lower792
  · exact lower521
  · exact lower641
  · exact lower559
def node1317 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 1, 0], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 2], [0, 0, 0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower1317 : ∀ h, Pure node1317 h → 11 ≤ h.length := by
  apply indexed_extend node1317 [(1, node796), (2, node793), (5, node577), (13, node560)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower796
  · exact lower793
  · exact lower577
  · exact lower560
def node1318 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 1], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1], [2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 1, 0]]
theorem lower1318 : ∀ h, Pure node1318 h → 11 ≤ h.length := by
  apply indexed_extend node1318 [(1, node797), (2, node794), (8, node561), (9, node563)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower797
  · exact lower794
  · exact lower561
  · exact lower563
def node1319 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1], [2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 1, 0]]
theorem lower1319 : ∀ h, Pure node1319 h → 11 ≤ h.length := by
  apply indexed_extend node1319 [(1, node798), (2, node795), (8, node562)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower798
  · exact lower795
  · exact lower562
def entries329 : List Graph := [node1316, node1317, node1318, node1319]
theorem entries_count329 : entries329.length = 4 := by decide +kernel
theorem arc_count329 : (entries329.map (fun g => ((verts g).filter (wye g)).length)).sum = 16 := by decide +kernel
end RawCert
