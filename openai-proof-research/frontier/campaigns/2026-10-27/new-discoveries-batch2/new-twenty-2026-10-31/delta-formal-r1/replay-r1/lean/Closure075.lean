import Closure074
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node300 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0], [0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0]]
theorem lower300 : ∀ h, Pure node300 h → 11 ≤ h.length := by
  apply indexed_extend node300 [(4, node40), (5, node62)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower40
  · exact lower62
def node301 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0], [0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0]]
theorem lower301 : ∀ h, Pure node301 h → 11 ≤ h.length := by
  apply indexed_extend node301 [(4, node41)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower41
def node302 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 1], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 2, 0, 0]]
theorem lower302 : ∀ h, Pure node302 h → 11 ≤ h.length := by
  apply indexed_extend node302 [(4, node42), (7, node35)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower42
  · exact lower35
def node303 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 1, 1], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2], [0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 2, 1, 0, 0]]
theorem lower303 : ∀ h, Pure node303 h → 11 ≤ h.length := by
  apply indexed_extend node303 [(3, node43), (5, node63)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower43
  · exact lower63
def entries75 : List Graph := [node300, node301, node302, node303]
theorem entries_count75 : entries75.length = 4 := by decide +kernel
theorem arc_count75 : (entries75.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by decide +kernel
end RawCert
