import Closure241
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node968 : Graph := [[0, 3, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 1], [0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 2, 0]]
theorem lower968 : ∀ h, Pure node968 h → 11 ≤ h.length := by
  apply indexed_extend node968 [(7, node282)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower282
def node969 : Graph := [[0, 3, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower969 : ∀ h, Pure node969 h → 11 ≤ h.length := by
  apply indexed_extend node969 [(5, node281), (12, node279)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower281
  · exact lower279
def node970 : Graph := [[0, 3, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0], [0, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower970 : ∀ h, Pure node970 h → 11 ≤ h.length := by
  apply indexed_extend node970 [(6, node282), (12, node280)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower282
  · exact lower280
def node971 : Graph := [[0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 0], [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]]
theorem lower971 : ∀ h, Pure node971 h → 11 ≤ h.length := by
  apply indexed_extend node971 [(2, node291), (4, node290), (7, node283), (8, node284), (9, node285)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower291
  · exact lower290
  · exact lower283
  · exact lower284
  · exact lower285
def entries242 : List Graph := [node968, node969, node970, node971]
theorem entries_count242 : entries242.length = 4 := by decide +kernel
theorem census_node968 : ((verts node968).filter (wye node968)).length = 1 := by decide +kernel
theorem census_node969 : ((verts node969).filter (wye node969)).length = 2 := by decide +kernel
theorem census_node970 : ((verts node970).filter (wye node970)).length = 2 := by decide +kernel
theorem census_node971 : ((verts node971).filter (wye node971)).length = 5 := by decide +kernel
theorem arc_count242 : (entries242.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by
  simp only [entries242, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node968, census_node969, census_node970, census_node971]
  decide +kernel
end RawCert
