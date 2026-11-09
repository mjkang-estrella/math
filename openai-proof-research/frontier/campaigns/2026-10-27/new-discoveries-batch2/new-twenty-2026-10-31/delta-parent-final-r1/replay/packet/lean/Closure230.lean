import Closure229
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node920 : Graph := [[0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 2, 1, 0]]
theorem lower920 : ∀ h, Pure node920 h → 11 ≤ h.length := by
  apply indexed_extend node920 [(1, node172), (7, node259)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower172
  · exact lower259
def node921 : Graph := [[0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0], [0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 2], [0, 0, 0, 0, 2, 2, 1, 0, 0, 1, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower921 : ∀ h, Pure node921 h → 11 ≤ h.length := by
  apply indexed_extend node921 [(1, node173), (5, node258)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower173
  · exact lower258
def node922 : Graph := [[0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower922 : ∀ h, Pure node922 h → 11 ≤ h.length := by
  apply indexed_extend node922 [(1, node174), (6, node259)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower174
  · exact lower259
def node923 : Graph := [[0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 1, 1, 0, 0, 3, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower923 : ∀ h, Pure node923 h → 11 ≤ h.length := by
  apply indexed_extend node923 [(1, node175), (8, node258), (11, node281), (12, node257)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower175
  · exact lower258
  · exact lower281
  · exact lower257
def entries230 : List Graph := [node920, node921, node922, node923]
theorem entries_count230 : entries230.length = 4 := by decide +kernel
theorem arc_count230 : (entries230.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by decide +kernel
end RawCert
