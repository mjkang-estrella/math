import Closure078
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node316 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 1], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 2, 1, 0]]
theorem lower316 : ∀ h, Pure node316 h → 11 ≤ h.length := by
  apply indexed_extend node316 [(2, node54), (3, node56), (10, node36)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower54
  · exact lower56
  · exact lower36
def node317 : Graph := [[0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0], [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower317 : ∀ h, Pure node317 h → 11 ≤ h.length := by
  apply indexed_extend node317 [(5, node38), (12, node37)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower38
  · exact lower37
def node318 : Graph := [[0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1], [0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0], [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 2, 0, 0]]
theorem lower318 : ∀ h, Pure node318 h → 11 ≤ h.length := by
  apply indexed_extend node318 [(6, node39)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower39
def node319 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0]]
theorem lower319 : ∀ h, Pure node319 h → 11 ≤ h.length := by
  apply indexed_extend node319 [(3, node91), (4, node69), (9, node40)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower91
  · exact lower69
  · exact lower40
def entries79 : List Graph := [node316, node317, node318, node319]
theorem entries_count79 : entries79.length = 4 := by decide +kernel
theorem arc_count79 : (entries79.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by decide +kernel
end RawCert
