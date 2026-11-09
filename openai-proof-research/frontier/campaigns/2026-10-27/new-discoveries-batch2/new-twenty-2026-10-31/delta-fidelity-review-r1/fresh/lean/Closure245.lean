import Closure244
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node980 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0]]
theorem lower980 : ∀ h, Pure node980 h → 11 ≤ h.length := by
  apply indexed_extend node980 [(3, node325), (4, node320), (8, node304), (10, node301)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower325
  · exact lower320
  · exact lower304
  · exact lower301
def node981 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower981 : ∀ h, Pure node981 h → 11 ≤ h.length := by
  apply indexed_extend node981 [(4, node321), (5, node399), (8, node306)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower321
  · exact lower399
  · exact lower306
def node982 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower982 : ∀ h, Pure node982 h → 11 ≤ h.length := by
  apply indexed_extend node982 [(4, node322), (7, node302), (8, node307)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower322
  · exact lower302
  · exact lower307
def node983 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0], [0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0]]
theorem lower983 : ∀ h, Pure node983 h → 11 ≤ h.length := by
  apply indexed_extend node983 [(4, node323), (5, node397), (9, node300), (10, node301)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower323
  · exact lower397
  · exact lower300
  · exact lower301
def entries245 : List Graph := [node980, node981, node982, node983]
theorem entries_count245 : entries245.length = 4 := by decide +kernel
theorem arc_count245 : (entries245.map (fun g => ((verts g).filter (wye g)).length)).sum = 14 := by decide +kernel
end RawCert
