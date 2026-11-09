import Closure420
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1684 : Graph := [[0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 2, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower1684 : ∀ h, Pure node1684 h → 11 ≤ h.length := by
  apply indexed_extend node1684 [(0, node296), (3, node906), (8, node901), (11, node899), (12, node949)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower296
  · exact lower906
  · exact lower901
  · exact lower899
  · exact lower949
def node1685 : Graph := [[0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower1685 : ∀ h, Pure node1685 h → 11 ≤ h.length := by
  apply indexed_extend node1685 [(0, node297), (8, node901), (12, node950)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower297
  · exact lower901
  · exact lower950
def node1686 : Graph := [[0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1686 : ∀ h, Pure node1686 h → 11 ≤ h.length := by
  apply indexed_extend node1686 [(0, node298), (4, node905), (12, node951), (13, node895)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower298
  · exact lower905
  · exact lower951
  · exact lower895
def node1687 : Graph := [[0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0], [0, 0, 2, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1687 : ∀ h, Pure node1687 h → 11 ≤ h.length := by
  apply indexed_extend node1687 [(0, node299), (5, node906), (12, node952), (13, node896)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower299
  · exact lower906
  · exact lower952
  · exact lower896
def entries421 : List Graph := [node1684, node1685, node1686, node1687]
theorem entries_count421 : entries421.length = 4 := by decide +kernel
theorem arc_count421 : (entries421.map (fun g => ((verts g).filter (wye g)).length)).sum = 16 := by decide +kernel
end RawCert
