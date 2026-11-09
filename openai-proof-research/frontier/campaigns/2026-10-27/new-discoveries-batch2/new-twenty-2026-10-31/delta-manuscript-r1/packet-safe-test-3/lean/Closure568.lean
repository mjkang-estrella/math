import Closure567
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node2272 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0]]
theorem lower2272 : ∀ h, Pure node2272 h → 11 ≤ h.length := by
  apply indexed_extend node2272 [(1, node2130), (2, node2129), (5, node2018), (6, node2019), (7, node2020), (8, node2021), (11, node2016), (12, node2014), (13, node2015), (14, node2017), (15, node2013)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower2130
  · exact lower2129
  · exact lower2018
  · exact lower2019
  · exact lower2020
  · exact lower2021
  · exact lower2016
  · exact lower2014
  · exact lower2015
  · exact lower2017
  · exact lower2013
def node2273 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower2273 : ∀ h, Pure node2273 h → 11 ≤ h.length := by
  apply indexed_extend node2273 [(0, node1806), (2, node1777), (3, node2076), (5, node2094), (6, node2033), (8, node2036), (9, node2027), (10, node2028), (11, node2029), (13, node2111)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1806
  · exact lower1777
  · exact lower2076
  · exact lower2094
  · exact lower2033
  · exact lower2036
  · exact lower2027
  · exact lower2028
  · exact lower2029
  · exact lower2111
def node2274 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 1, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0]]
theorem lower2274 : ∀ h, Pure node2274 h → 11 ≤ h.length := by
  apply indexed_extend node2274 [(0, node1807), (2, node1778), (5, node2095), (6, node2034), (7, node2035), (8, node2037), (9, node2031), (10, node2032), (12, node2030), (13, node2113)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1807
  · exact lower1778
  · exact lower2095
  · exact lower2034
  · exact lower2035
  · exact lower2037
  · exact lower2031
  · exact lower2032
  · exact lower2030
  · exact lower2113
def node2275 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 3], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]]
theorem lower2275 : ∀ h, Pure node2275 h → 11 ≤ h.length := by
  apply indexed_extend node2275 [(0, node1824), (2, node1779), (3, node2077), (4, node2074), (5, node2096), (6, node2044), (9, node2038), (10, node2039), (11, node2040), (13, node2116)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1824
  · exact lower1779
  · exact lower2077
  · exact lower2074
  · exact lower2096
  · exact lower2044
  · exact lower2038
  · exact lower2039
  · exact lower2040
  · exact lower2116
def entries568 : List Graph := [node2272, node2273, node2274, node2275]
theorem entries_count568 : entries568.length = 4 := by decide +kernel
theorem census_node2272 : ((verts node2272).filter (wye node2272)).length = 11 := by decide +kernel
theorem census_node2273 : ((verts node2273).filter (wye node2273)).length = 10 := by decide +kernel
theorem census_node2274 : ((verts node2274).filter (wye node2274)).length = 10 := by decide +kernel
theorem census_node2275 : ((verts node2275).filter (wye node2275)).length = 10 := by decide +kernel
theorem arc_count568 : (entries568.map (fun g => ((verts g).filter (wye g)).length)).sum = 41 := by
  simp only [entries568, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node2272, census_node2273, census_node2274, census_node2275]
  decide +kernel
end RawCert
