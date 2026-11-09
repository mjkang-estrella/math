import Closure332
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1332 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2], [1, 0, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 1, 0]]
theorem lower1332 : ∀ h, Pure node1332 h → 11 ≤ h.length := by
  apply indexed_extend node1332 [(2, node807), (6, node612), (7, node569), (8, node570), (10, node563)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower807
  · exact lower612
  · exact lower569
  · exact lower570
  · exact lower563
def node1333 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 1, 0], [1, 0, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 2], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 2, 1, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower1333 : ∀ h, Pure node1333 h → 11 ≤ h.length := by
  apply indexed_extend node1333 [(2, node808), (4, node587), (13, node567)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower808
  · exact lower587
  · exact lower567
def node1334 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [2, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2], [1, 0, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 1, 0]]
theorem lower1334 : ∀ h, Pure node1334 h → 11 ≤ h.length := by
  apply indexed_extend node1334 [(2, node809), (4, node588), (8, node571), (11, node563)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower809
  · exact lower588
  · exact lower571
  · exact lower563
def node1335 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2], [1, 0, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 2, 0, 0]]
theorem lower1335 : ∀ h, Pure node1335 h → 11 ≤ h.length := by
  apply indexed_extend node1335 [(2, node810), (8, node572), (11, node563), (12, node568)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower810
  · exact lower572
  · exact lower563
  · exact lower568
def entries333 : List Graph := [node1332, node1333, node1334, node1335]
theorem entries_count333 : entries333.length = 4 := by decide +kernel
theorem arc_count333 : (entries333.map (fun g => ((verts g).filter (wye g)).length)).sum = 16 := by decide +kernel
end RawCert
