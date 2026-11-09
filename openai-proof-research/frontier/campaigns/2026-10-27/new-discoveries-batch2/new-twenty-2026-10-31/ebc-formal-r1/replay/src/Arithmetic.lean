import Rows0
import Rows1
import Rows2
import Rows3
import Rows4
import Rows5
import Rows6
import Rows7
namespace EBC337062

theorem rational_total_1 : ((List.range 32).map (rationalRow 0 1)).sum = (15169 : ℚ) / 615 := by
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, rational_row_1_0, rational_row_1_1, rational_row_1_2, rational_row_1_3, rational_row_1_4, rational_row_1_5, rational_row_1_6, rational_row_1_7, rational_row_1_8, rational_row_1_9, rational_row_1_10, rational_row_1_11, rational_row_1_12, rational_row_1_13, rational_row_1_14, rational_row_1_15, rational_row_1_16, rational_row_1_17, rational_row_1_18, rational_row_1_19, rational_row_1_20, rational_row_1_21, rational_row_1_22, rational_row_1_23, rational_row_1_24, rational_row_1_25, rational_row_1_26, rational_row_1_27, rational_row_1_28, rational_row_1_29, rational_row_1_30, rational_row_1_31]
  norm_num


theorem rational_total_9 : ((List.range 32).map (rationalRow 0 9)).sum = (15172 : ℚ) / 615 := by
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, rational_row_9_0, rational_row_9_1, rational_row_9_2, rational_row_9_3, rational_row_9_4, rational_row_9_5, rational_row_9_6, rational_row_9_7, rational_row_9_8, rational_row_9_9, rational_row_9_10, rational_row_9_11, rational_row_9_12, rational_row_9_13, rational_row_9_14, rational_row_9_15, rational_row_9_16, rational_row_9_17, rational_row_9_18, rational_row_9_19, rational_row_9_20, rational_row_9_21, rational_row_9_22, rational_row_9_23, rational_row_9_24, rational_row_9_25, rational_row_9_26, rational_row_9_27, rational_row_9_28, rational_row_9_29, rational_row_9_30, rational_row_9_31]
  norm_num

end EBC337062
