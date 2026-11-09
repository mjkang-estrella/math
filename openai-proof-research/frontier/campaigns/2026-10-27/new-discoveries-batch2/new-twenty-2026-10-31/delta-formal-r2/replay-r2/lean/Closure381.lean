import Closure380
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1524 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 2], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1524 : ∀ h, Pure node1524 h → 11 ≤ h.length := by
  apply indexed_extend node1524 [(0, node687), (2, node515), (5, node736), (9, node734), (13, node725)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower687
  · exact lower515
  · exact lower736
  · exact lower734
  · exact lower725
def node1525 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0], [0, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1525 : ∀ h, Pure node1525 h → 11 ≤ h.length := by
  apply indexed_extend node1525 [(0, node688), (2, node516), (6, node737), (9, node735), (10, node845), (13, node726)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower688
  · exact lower516
  · exact lower737
  · exact lower735
  · exact lower845
  · exact lower726
def node1526 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0, 0], [2, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1526 : ∀ h, Pure node1526 h → 11 ≤ h.length := by
  apply indexed_extend node1526 [(0, node691), (2, node517), (5, node738)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower691
  · exact lower517
  · exact lower738
def node1527 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0, 0], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1527 : ∀ h, Pure node1527 h → 11 ≤ h.length := by
  apply indexed_extend node1527 [(0, node692), (2, node518), (6, node739), (10, node832)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower692
  · exact lower518
  · exact lower739
  · exact lower832
def entries381 : List Graph := [node1524, node1525, node1526, node1527]
theorem entries_count381 : entries381.length = 4 := by decide +kernel
theorem arc_count381 : (entries381.map (fun g => ((verts g).filter (wye g)).length)).sum = 18 := by decide +kernel
end RawCert
