import Closure568
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node2276 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0]]
theorem lower2276 : ∀ h, Pure node2276 h → 11 ≤ h.length := by
  apply indexed_extend node2276 [(0, node1825), (2, node1780), (4, node2075), (5, node2097), (6, node2045), (7, node2046), (9, node2042), (10, node2043), (12, node2041), (13, node2118)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1825
  · exact lower1780
  · exact lower2075
  · exact lower2097
  · exact lower2045
  · exact lower2046
  · exact lower2042
  · exact lower2043
  · exact lower2041
  · exact lower2118
def node2277 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0]]
theorem lower2277 : ∀ h, Pure node2277 h → 11 ≤ h.length := by
  apply indexed_extend node2277 [(0, node1808), (2, node1786), (3, node2083), (5, node2098), (6, node2052), (7, node2055), (8, node2058), (9, node2047), (10, node2048), (11, node2049), (12, node2112), (13, node2030)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1808
  · exact lower1786
  · exact lower2083
  · exact lower2098
  · exact lower2052
  · exact lower2055
  · exact lower2058
  · exact lower2047
  · exact lower2048
  · exact lower2049
  · exact lower2112
  · exact lower2030
def node2278 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower2278 : ∀ h, Pure node2278 h → 11 ≤ h.length := by
  apply indexed_extend node2278 [(0, node1809), (2, node1787), (3, node2084), (5, node2103), (6, node2054), (8, node2061), (10, node2050), (11, node2047), (13, node2031), (15, node2027)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1809
  · exact lower1787
  · exact lower2084
  · exact lower2103
  · exact lower2054
  · exact lower2061
  · exact lower2050
  · exact lower2047
  · exact lower2031
  · exact lower2027
def node2279 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower2279 : ∀ h, Pure node2279 h → 11 ≤ h.length := by
  apply indexed_extend node2279 [(0, node1810), (2, node1788), (3, node2085), (7, node2056), (8, node2062), (10, node2051), (11, node2048), (12, node2114), (13, node2032), (15, node2028)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1810
  · exact lower1788
  · exact lower2085
  · exact lower2056
  · exact lower2062
  · exact lower2051
  · exact lower2048
  · exact lower2114
  · exact lower2032
  · exact lower2028
def entries569 : List Graph := [node2276, node2277, node2278, node2279]
theorem entries_count569 : entries569.length = 4 := by decide +kernel
theorem arc_count569 : (entries569.map (fun g => ((verts g).filter (wye g)).length)).sum = 42 := by decide +kernel
end RawCert
