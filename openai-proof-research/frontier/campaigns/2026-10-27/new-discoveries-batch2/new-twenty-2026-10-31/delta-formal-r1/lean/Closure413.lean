import Closure412
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1652 : Graph := [[0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 2], [2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower1652 : ∀ h, Pure node1652 h → 11 ≤ h.length := by
  apply indexed_extend node1652 [(0, node446), (1, node383), (6, node890)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower446
  · exact lower383
  · exact lower890
def node1653 : Graph := [[0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 0, 1, 2, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower1653 : ∀ h, Pure node1653 h → 11 ≤ h.length := by
  apply indexed_extend node1653 [(0, node447), (1, node384), (7, node892)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower447
  · exact lower384
  · exact lower892
def node1654 : Graph := [[0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 0], [2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [0, 0, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1654 : ∀ h, Pure node1654 h → 11 ≤ h.length := by
  apply indexed_extend node1654 [(0, node283), (3, node895), (5, node894), (9, node886), (13, node927)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower283
  · exact lower895
  · exact lower894
  · exact lower886
  · exact lower927
def node1655 : Graph := [[0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 0, 1, 2, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [0, 0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1655 : ∀ h, Pure node1655 h → 11 ≤ h.length := by
  apply indexed_extend node1655 [(0, node284), (3, node896), (9, node887), (13, node928)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower284
  · exact lower896
  · exact lower887
  · exact lower928
def entries413 : List Graph := [node1652, node1653, node1654, node1655]
theorem entries_count413 : entries413.length = 4 := by decide +kernel
theorem arc_count413 : (entries413.map (fun g => ((verts g).filter (wye g)).length)).sum = 15 := by decide +kernel
end RawCert
