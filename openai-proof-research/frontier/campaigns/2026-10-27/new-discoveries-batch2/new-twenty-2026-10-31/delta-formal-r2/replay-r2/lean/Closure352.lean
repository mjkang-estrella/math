import Closure351
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1408 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0]]
theorem lower1408 : ∀ h, Pure node1408 h → 11 ≤ h.length := by
  apply indexed_extend node1408 [(1, node878), (9, node626), (11, node624), (12, node633), (13, node623)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower878
  · exact lower626
  · exact lower624
  · exact lower633
  · exact lower623
def node1409 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [1, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 2, 0, 0]]
theorem lower1409 : ∀ h, Pure node1409 h → 11 ≤ h.length := by
  apply indexed_extend node1409 [(1, node879), (9, node627), (11, node625), (12, node634)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower879
  · exact lower627
  · exact lower625
  · exact lower634
def node1410 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [1, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0]]
theorem lower1410 : ∀ h, Pure node1410 h → 11 ≤ h.length := by
  apply indexed_extend node1410 [(2, node880), (10, node629), (11, node630), (12, node635), (13, node628)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower880
  · exact lower629
  · exact lower630
  · exact lower635
  · exact lower628
def node1411 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0, 0, 1], [1, 0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 0, 0]]
theorem lower1411 : ∀ h, Pure node1411 h → 11 ≤ h.length := by
  apply indexed_extend node1411 [(2, node881), (10, node631), (11, node632), (12, node636)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower881
  · exact lower631
  · exact lower632
  · exact lower636
def entries352 : List Graph := [node1408, node1409, node1410, node1411]
theorem entries_count352 : entries352.length = 4 := by decide +kernel
theorem arc_count352 : (entries352.map (fun g => ((verts g).filter (wye g)).length)).sum = 18 := by decide +kernel
end RawCert
