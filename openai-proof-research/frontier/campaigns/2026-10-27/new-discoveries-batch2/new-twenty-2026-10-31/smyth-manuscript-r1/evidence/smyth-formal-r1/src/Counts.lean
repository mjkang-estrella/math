import Bridges
import S00
import S01
import S02
import S03
import S04
import S05
import S06
import S07
import S08
import S09
import S10
import S11
import S12
import S13
import S14
import S15
import S16
import S17
import S18
import S19
import T00
import T01
import T02
import T03
import T04
import T05
import T06
import T07
import T08
import T09
import T10
import T11
import T12
import T13
import T14
import T15
import T16
import T17
import T18
import T19
import T20
namespace Smyth1512
theorem SL_length : SL.length = 1137 := by
  change (((comps 3 19) ×ˢ comps 2 20).filter _).length = _
  rw [count_rows]
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, count_S00, count_S01, count_S02, count_S03, count_S04, count_S05, count_S06, count_S07, count_S08, count_S09, count_S10, count_S11, count_S12, count_S13, count_S14, count_S15, count_S16, count_S17, count_S18, count_S19]
  norm_num
theorem TL_length : TL.length = 1134 := by
  change (((comps 3 20) ×ˢ comps 2 19).filter _).length = _
  rw [count_rows]
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, count_T00, count_T01, count_T02, count_T03, count_T04, count_T05, count_T06, count_T07, count_T08, count_T09, count_T10, count_T11, count_T12, count_T13, count_T14, count_T15, count_T16, count_T17, count_T18, count_T19, count_T20]
  norm_num
theorem TL_nodup : TL.Nodup :=
  ((nodup_comps 3 20).product (nodup_comps 2 19)).filter _
theorem card_S : SL.toFinset.card = 1137 := by
  rw [List.toFinset_card_of_nodup SL_nodup, SL_length]
theorem card_T : TL.toFinset.card = 1134 := by
  rw [List.toFinset_card_of_nodup TL_nodup, TL_length]
end Smyth1512
