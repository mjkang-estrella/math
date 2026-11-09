import Closure403
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1616 : Graph := [[0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 1, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0]]
theorem lower1616 : ∀ h, Pure node1616 h → 11 ≤ h.length := by
  apply indexed_extend node1616 [(3, node882), (4, node858), (5, node833), (9, node825), (10, node826)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower882
  · exact lower858
  · exact lower833
  · exact lower825
  · exact lower826
def node1617 : Graph := [[0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 3, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0]]
theorem lower1617 : ∀ h, Pure node1617 h → 11 ≤ h.length := by
  apply indexed_extend node1617 [(4, node859), (5, node834), (6, node835), (9, node827)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower859
  · exact lower834
  · exact lower835
  · exact lower827
def node1618 : Graph := [[0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [1, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0]]
theorem lower1618 : ∀ h, Pure node1618 h → 11 ≤ h.length := by
  apply indexed_extend node1618 [(3, node883), (6, node837), (9, node828), (11, node827), (13, node825)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower883
  · exact lower837
  · exact lower828
  · exact lower827
  · exact lower825
def node1619 : Graph := [[0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0]]
theorem lower1619 : ∀ h, Pure node1619 h → 11 ≤ h.length := by
  apply indexed_extend node1619 [(4, node860), (5, node836), (6, node838), (9, node828), (13, node826)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower860
  · exact lower836
  · exact lower838
  · exact lower828
  · exact lower826
def entries404 : List Graph := [node1616, node1617, node1618, node1619]
theorem entries_count404 : entries404.length = 4 := by decide +kernel
theorem arc_count404 : (entries404.map (fun g => ((verts g).filter (wye g)).length)).sum = 19 := by decide +kernel
end RawCert
