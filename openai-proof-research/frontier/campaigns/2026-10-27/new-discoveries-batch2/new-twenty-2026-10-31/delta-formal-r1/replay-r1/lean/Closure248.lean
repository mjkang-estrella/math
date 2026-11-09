import Closure247
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node992 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0]]
theorem lower992 : ∀ h, Pure node992 h → 11 ≤ h.length := by
  apply indexed_extend node992 [(1, node345), (2, node333), (4, node348), (7, node312), (10, node308), (12, node302)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower345
  · exact lower333
  · exact lower348
  · exact lower312
  · exact lower308
  · exact lower302
def node993 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower993 : ∀ h, Pure node993 h → 11 ≤ h.length := by
  apply indexed_extend node993 [(2, node334), (5, node406), (7, node309), (8, node310), (9, node311)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower334
  · exact lower406
  · exact lower309
  · exact lower310
  · exact lower311
def node994 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 1, 1, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower994 : ∀ h, Pure node994 h → 11 ≤ h.length := by
  apply indexed_extend node994 [(2, node335), (3, node349), (5, node411), (13, node303)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower335
  · exact lower349
  · exact lower411
  · exact lower303
def node995 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower995 : ∀ h, Pure node995 h → 11 ≤ h.length := by
  apply indexed_extend node995 [(2, node336), (3, node350), (13, node304)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower336
  · exact lower350
  · exact lower304
def entries248 : List Graph := [node992, node993, node994, node995]
theorem entries_count248 : entries248.length = 4 := by decide +kernel
theorem arc_count248 : (entries248.map (fun g => ((verts g).filter (wye g)).length)).sum = 18 := by decide +kernel
end RawCert
