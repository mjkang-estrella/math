import Closure080
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node324 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1], [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3], [0, 1, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0]]
theorem lower324 : ∀ h, Pure node324 h → 11 ≤ h.length := by
  apply indexed_extend node324 [(3, node91), (7, node43)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower91
  · exact lower43
def node325 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1], [1, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1], [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3], [0, 1, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0]]
theorem lower325 : ∀ h, Pure node325 h → 11 ≤ h.length := by
  apply indexed_extend node325 [(3, node92), (7, node44)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower92
  · exact lower44
def node326 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2, 0, 0]]
theorem lower326 : ∀ h, Pure node326 h → 11 ≤ h.length := by
  apply indexed_extend node326 [(4, node71), (8, node42)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower71
  · exact lower42
def node327 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 3, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 3], [0, 1, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0]]
theorem lower327 : ∀ h, Pure node327 h → 11 ≤ h.length := by
  apply indexed_extend node327 [(7, node43), (8, node44)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower43
  · exact lower44
def entries81 : List Graph := [node324, node325, node326, node327]
theorem entries_count81 : entries81.length = 4 := by decide +kernel
theorem arc_count81 : (entries81.map (fun g => ((verts g).filter (wye g)).length)).sum = 8 := by decide +kernel
end RawCert
