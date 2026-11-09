import Closure413
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1656 : Graph := [[0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [0, 0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1656 : ∀ h, Pure node1656 h → 11 ≤ h.length := by
  apply indexed_extend node1656 [(0, node285), (5, node893), (8, node886), (9, node887), (13, node931)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower285
  · exact lower893
  · exact lower886
  · exact lower887
  · exact lower931
def node1657 : Graph := [[0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 1, 0, 1, 0], [2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [0, 0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1657 : ∀ h, Pure node1657 h → 11 ≤ h.length := by
  apply indexed_extend node1657 [(0, node449), (1, node385), (4, node893), (8, node888), (13, node932)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower449
  · exact lower385
  · exact lower893
  · exact lower888
  · exact lower932
def node1658 : Graph := [[0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 1, 1, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1658 : ∀ h, Pure node1658 h → 11 ≤ h.length := by
  apply indexed_extend node1658 [(0, node450), (1, node386), (3, node897), (4, node894), (7, node911), (9, node888), (13, node933)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower450
  · exact lower386
  · exact lower897
  · exact lower894
  · exact lower911
  · exact lower888
  · exact lower933
def node1659 : Graph := [[0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1659 : ∀ h, Pure node1659 h → 11 ≤ h.length := by
  apply indexed_extend node1659 [(0, node689), (1, node644), (3, node895), (5, node897), (7, node917), (13, node936)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower689
  · exact lower644
  · exact lower895
  · exact lower897
  · exact lower917
  · exact lower936
def entries414 : List Graph := [node1656, node1657, node1658, node1659]
theorem entries_count414 : entries414.length = 4 := by decide +kernel
theorem arc_count414 : (entries414.map (fun g => ((verts g).filter (wye g)).length)).sum = 23 := by decide +kernel
end RawCert
