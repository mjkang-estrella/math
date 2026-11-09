import FullCE
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
namespace TraceSamples
open TraceFormal
abbrev Data := List (List ℤ)
def matrix (a : Data) : Mat ℤ := fun i j => (a[i.val]?.getD [])[j.val]?.getD 0
def sample0_0 : Data := [[2, 1, -1], [1, -1, 0], [0, -2, -1]]
def sample0_1 : Data := [[1, 0, -2], [1, 2, -2], [0, 0, -3]]
def sample0_2 : Data := [[2, -2, 2], [2, 0, 2], [-1, -1, -2]]
def value0 (g : ℕ) : ℤ := sourceE (matrix sample0_0) (matrix sample0_1) (matrix sample0_2) g
theorem evaluated0_1 : value0 1 = 8 := by decide
theorem evaluated0_2 : value0 2 = 14 := by decide
theorem evaluated0_3 : value0 3 = -8 := by decide
theorem evaluated0_4 : value0 4 = 8 := by decide
theorem evaluated0_5 : value0 5 = 3 := by decide
theorem evaluated0_6 : value0 6 = 10 := by decide
theorem evaluated0_7 : value0 7 = 15 := by decide
theorem evaluated0_8 : value0 8 = -18 := by decide
theorem evaluated0_9 : value0 9 = -12 := by decide
theorem evaluated0_10 : value0 10 = 5 := by decide
theorem evaluated0_11 : value0 11 = 18 := by decide
theorem evaluated0_12 : value0 12 = -8 := by decide
theorem evaluated0_13 : value0 13 = -26 := by decide
theorem evaluated0_14 : value0 14 = 0 := by decide
theorem evaluated0_15 : value0 15 = -24 := by decide
theorem evaluated0_16 : value0 16 = -3 := by decide
theorem evaluated0_17 : value0 17 = -23 := by decide
theorem evaluated0_18 : value0 18 = -51 := by decide
theorem evaluated0_19 : value0 19 = -25 := by decide
theorem evaluated0_20 : value0 20 = -200 := by decide
theorem evaluated0_21 : value0 21 = 52 := by decide
theorem evaluated0_22 : value0 22 = -295 := by decide
theorem evaluated0_23 : value0 23 = -26 := by decide
theorem evaluated0_24 : value0 24 = 84 := by decide
theorem evaluated0_25 : value0 25 = -49 := by decide
theorem evaluated0_26 : value0 26 = 58 := by decide
theorem evaluated0_27 : value0 27 = 101 := by decide
theorem evaluated0_28 : value0 28 = -342 := by decide
theorem evaluated0_29 : value0 29 = -248 := by decide
theorem evaluated0_30 : value0 30 = 316 := by decide
theorem evaluated0_31 : value0 31 = -241 := by decide
theorem evaluated0_32 : value0 32 = -150 := by decide
theorem evaluated0_33 : value0 33 = 336 := by decide
theorem evaluated0_34 : value0 34 = -437 := by decide
theorem evaluated0_35 : value0 35 = 266 := by decide
theorem evaluated0_36 : value0 36 = -204 := by decide
theorem evaluated0_37 : value0 37 = 264 := by decide
theorem evaluated0_38 : value0 38 = 456 := by decide
theorem evaluated0_39 : value0 39 = -46 := by decide
theorem evaluated0_40 : value0 40 = -1012 := by decide
theorem evaluated0_41 : value0 41 = -672 := by decide
theorem evaluated0_42 : value0 42 = -994 := by decide
theorem evaluated0_43 : value0 43 = -1186 := by decide
theorem evaluated0_44 : value0 44 = -246 := by decide
theorem evaluated0_45 : value0 45 = -1634 := by decide
theorem traceless0 : tr (matrix sample0_0) = 0 ∧ tr (matrix sample0_1) = 0 ∧ tr (matrix sample0_2) = 0 := by decide
def sample1_0 : Data := [[0, -1, 0], [-2, -1, -1], [2, -1, 1]]
def sample1_1 : Data := [[0, -1, 2], [-2, 1, 1], [0, -2, -1]]
def sample1_2 : Data := [[-1, -2, -2], [-1, 1, 0], [1, -2, 0]]
def value1 (g : ℕ) : ℤ := sourceE (matrix sample1_0) (matrix sample1_1) (matrix sample1_2) g
theorem evaluated1_1 : value1 1 = 8 := by decide
theorem evaluated1_2 : value1 2 = 2 := by decide
theorem evaluated1_3 : value1 3 = 2 := by decide
theorem evaluated1_4 : value1 4 = 7 := by decide
theorem evaluated1_5 : value1 5 = 2 := by decide
theorem evaluated1_6 : value1 6 = 6 := by decide
theorem evaluated1_7 : value1 7 = 0 := by decide
theorem evaluated1_8 : value1 8 = 30 := by decide
theorem evaluated1_9 : value1 9 = -6 := by decide
theorem evaluated1_10 : value1 10 = 6 := by decide
theorem evaluated1_11 : value1 11 = -6 := by decide
theorem evaluated1_12 : value1 12 = 8 := by decide
theorem evaluated1_13 : value1 13 = 5 := by decide
theorem evaluated1_14 : value1 14 = -7 := by decide
theorem evaluated1_15 : value1 15 = -9 := by decide
theorem evaluated1_16 : value1 16 = -5 := by decide
theorem evaluated1_17 : value1 17 = 7 := by decide
theorem evaluated1_18 : value1 18 = -45 := by decide
theorem evaluated1_19 : value1 19 = 33 := by decide
theorem evaluated1_20 : value1 20 = 22 := by decide
theorem evaluated1_21 : value1 21 = -1 := by decide
theorem evaluated1_22 : value1 22 = -49 := by decide
theorem evaluated1_23 : value1 23 = 85 := by decide
theorem evaluated1_24 : value1 24 = 1 := by decide
theorem evaluated1_25 : value1 25 = 49 := by decide
theorem evaluated1_26 : value1 26 = 7 := by decide
theorem evaluated1_27 : value1 27 = -98 := by decide
theorem evaluated1_28 : value1 28 = 95 := by decide
theorem evaluated1_29 : value1 29 = 26 := by decide
theorem evaluated1_30 : value1 30 = -197 := by decide
theorem evaluated1_31 : value1 31 = 114 := by decide
theorem evaluated1_32 : value1 32 = 24 := by decide
theorem evaluated1_33 : value1 33 = 241 := by decide
theorem evaluated1_34 : value1 34 = 52 := by decide
theorem evaluated1_35 : value1 35 = -160 := by decide
theorem evaluated1_36 : value1 36 = 180 := by decide
theorem evaluated1_37 : value1 37 = -14 := by decide
theorem evaluated1_38 : value1 38 = 165 := by decide
theorem evaluated1_39 : value1 39 = -147 := by decide
theorem evaluated1_40 : value1 40 = 131 := by decide
theorem evaluated1_41 : value1 41 = 142 := by decide
theorem evaluated1_42 : value1 42 = 141 := by decide
theorem evaluated1_43 : value1 43 = 97 := by decide
theorem evaluated1_44 : value1 44 = 19 := by decide
theorem evaluated1_45 : value1 45 = 326 := by decide
theorem traceless1 : tr (matrix sample1_0) = 0 ∧ tr (matrix sample1_1) = 0 ∧ tr (matrix sample1_2) = 0 := by decide
def sample2_0 : Data := [[-1, 2, 1], [1, -2, 1], [2, 0, 3]]
def sample2_1 : Data := [[1, 1, -2], [0, 2, 1], [-1, 1, -3]]
def sample2_2 : Data := [[-1, 0, 0], [0, 2, 2], [-2, -1, -1]]
def value2 (g : ℕ) : ℤ := sourceE (matrix sample2_0) (matrix sample2_1) (matrix sample2_2) g
theorem evaluated2_1 : value2 1 = 22 := by decide
theorem evaluated2_2 : value2 2 = 20 := by decide
theorem evaluated2_3 : value2 3 = 2 := by decide
theorem evaluated2_4 : value2 4 = -17 := by decide
theorem evaluated2_5 : value2 5 = -9 := by decide
theorem evaluated2_6 : value2 6 = 11 := by decide
theorem evaluated2_7 : value2 7 = 24 := by decide
theorem evaluated2_8 : value2 8 = -36 := by decide
theorem evaluated2_9 : value2 9 = 0 := by decide
theorem evaluated2_10 : value2 10 = -23 := by decide
theorem evaluated2_11 : value2 11 = -6 := by decide
theorem evaluated2_12 : value2 12 = 32 := by decide
theorem evaluated2_13 : value2 13 = -18 := by decide
theorem evaluated2_14 : value2 14 = -13 := by decide
theorem evaluated2_15 : value2 15 = -3 := by decide
theorem evaluated2_16 : value2 16 = 26 := by decide
theorem evaluated2_17 : value2 17 = 26 := by decide
theorem evaluated2_18 : value2 18 = 97 := by decide
theorem evaluated2_19 : value2 19 = 53 := by decide
theorem evaluated2_20 : value2 20 = -99 := by decide
theorem evaluated2_21 : value2 21 = 202 := by decide
theorem evaluated2_22 : value2 22 = -25 := by decide
theorem evaluated2_23 : value2 23 = 172 := by decide
theorem evaluated2_24 : value2 24 = 74 := by decide
theorem evaluated2_25 : value2 25 = 11 := by decide
theorem evaluated2_26 : value2 26 = 44 := by decide
theorem evaluated2_27 : value2 27 = 33 := by decide
theorem evaluated2_28 : value2 28 = 286 := by decide
theorem evaluated2_29 : value2 29 = 204 := by decide
theorem evaluated2_30 : value2 30 = 236 := by decide
theorem evaluated2_31 : value2 31 = -218 := by decide
theorem evaluated2_32 : value2 32 = 129 := by decide
theorem evaluated2_33 : value2 33 = -206 := by decide
theorem evaluated2_34 : value2 34 = 48 := by decide
theorem evaluated2_35 : value2 35 = 146 := by decide
theorem evaluated2_36 : value2 36 = -218 := by decide
theorem evaluated2_37 : value2 37 = 630 := by decide
theorem evaluated2_38 : value2 38 = 60 := by decide
theorem evaluated2_39 : value2 39 = 614 := by decide
theorem evaluated2_40 : value2 40 = 361 := by decide
theorem evaluated2_41 : value2 41 = 10 := by decide
theorem evaluated2_42 : value2 42 = -85 := by decide
theorem evaluated2_43 : value2 43 = -760 := by decide
theorem evaluated2_44 : value2 44 = -950 := by decide
theorem evaluated2_45 : value2 45 = 1177 := by decide
theorem traceless2 : tr (matrix sample2_0) = 0 ∧ tr (matrix sample2_1) = 0 ∧ tr (matrix sample2_2) = 0 := by decide
def sample3_0 : Data := [[0, 1, -2], [2, -1, 2], [0, -1, 1]]
def sample3_1 : Data := [[0, -1, -1], [1, -1, -1], [-1, 0, 1]]
def sample3_2 : Data := [[1, 2, 2], [-2, 1, 2], [0, 1, -2]]
def value3 (g : ℕ) : ℤ := sourceE (matrix sample3_0) (matrix sample3_1) (matrix sample3_2) g
theorem evaluated3_1 : value3 1 = 2 := by decide
theorem evaluated3_2 : value3 2 = 2 := by decide
theorem evaluated3_3 : value3 3 = 2 := by decide
theorem evaluated3_4 : value3 4 = 4 := by decide
theorem evaluated3_5 : value3 5 = -1 := by decide
theorem evaluated3_6 : value3 6 = -2 := by decide
theorem evaluated3_7 : value3 7 = 6 := by decide
theorem evaluated3_8 : value3 8 = 3 := by decide
theorem evaluated3_9 : value3 9 = -48 := by decide
theorem evaluated3_10 : value3 10 = 3 := by decide
theorem evaluated3_11 : value3 11 = -9 := by decide
theorem evaluated3_12 : value3 12 = 9 := by decide
theorem evaluated3_13 : value3 13 = -7 := by decide
theorem evaluated3_14 : value3 14 = 23 := by decide
theorem evaluated3_15 : value3 15 = 18 := by decide
theorem evaluated3_16 : value3 16 = -29 := by decide
theorem evaluated3_17 : value3 17 = 15 := by decide
theorem evaluated3_18 : value3 18 = -42 := by decide
theorem evaluated3_19 : value3 19 = -90 := by decide
theorem evaluated3_20 : value3 20 = -3 := by decide
theorem evaluated3_21 : value3 21 = 114 := by decide
theorem evaluated3_22 : value3 22 = -3 := by decide
theorem evaluated3_23 : value3 23 = 15 := by decide
theorem evaluated3_24 : value3 24 = 4 := by decide
theorem evaluated3_25 : value3 25 = -17 := by decide
theorem evaluated3_26 : value3 26 = -39 := by decide
theorem evaluated3_27 : value3 27 = -9 := by decide
theorem evaluated3_28 : value3 28 = -19 := by decide
theorem evaluated3_29 : value3 29 = -74 := by decide
theorem evaluated3_30 : value3 30 = -76 := by decide
theorem evaluated3_31 : value3 31 = -91 := by decide
theorem evaluated3_32 : value3 32 = 57 := by decide
theorem evaluated3_33 : value3 33 = -42 := by decide
theorem evaluated3_34 : value3 34 = -71 := by decide
theorem evaluated3_35 : value3 35 = -2 := by decide
theorem evaluated3_36 : value3 36 = -31 := by decide
theorem evaluated3_37 : value3 37 = 312 := by decide
theorem evaluated3_38 : value3 38 = 6 := by decide
theorem evaluated3_39 : value3 39 = -192 := by decide
theorem evaluated3_40 : value3 40 = -45 := by decide
theorem evaluated3_41 : value3 41 = 82 := by decide
theorem evaluated3_42 : value3 42 = 436 := by decide
theorem evaluated3_43 : value3 43 = 146 := by decide
theorem evaluated3_44 : value3 44 = 136 := by decide
theorem evaluated3_45 : value3 45 = 178 := by decide
theorem traceless3 : tr (matrix sample3_0) = 0 ∧ tr (matrix sample3_1) = 0 ∧ tr (matrix sample3_2) = 0 := by decide
def sample4_0 : Data := [[-1, -2, 1], [1, 0, -2], [1, -1, 1]]
def sample4_1 : Data := [[2, -1, 0], [0, 0, -2], [2, 2, -2]]
def sample4_2 : Data := [[1, -1, -2], [2, 1, -2], [2, 1, -2]]
def value4 (g : ℕ) : ℤ := sourceE (matrix sample4_0) (matrix sample4_1) (matrix sample4_2) g
theorem evaluated4_1 : value4 1 = 4 := by decide
theorem evaluated4_2 : value4 2 = 0 := by decide
theorem evaluated4_3 : value4 3 = -10 := by decide
theorem evaluated4_4 : value4 4 = -5 := by decide
theorem evaluated4_5 : value4 5 = -8 := by decide
theorem evaluated4_6 : value4 6 = -6 := by decide
theorem evaluated4_7 : value4 7 = 21 := by decide
theorem evaluated4_8 : value4 8 = 36 := by decide
theorem evaluated4_9 : value4 9 = 0 := by decide
theorem evaluated4_10 : value4 10 = 7 := by decide
theorem evaluated4_11 : value4 11 = 12 := by decide
theorem evaluated4_12 : value4 12 = 12 := by decide
theorem evaluated4_13 : value4 13 = 20 := by decide
theorem evaluated4_14 : value4 14 = 11 := by decide
theorem evaluated4_15 : value4 15 = 4 := by decide
theorem evaluated4_16 : value4 16 = 16 := by decide
theorem evaluated4_17 : value4 17 = -14 := by decide
theorem evaluated4_18 : value4 18 = -43 := by decide
theorem evaluated4_19 : value4 19 = -17 := by decide
theorem evaluated4_20 : value4 20 = -12 := by decide
theorem evaluated4_21 : value4 21 = -38 := by decide
theorem evaluated4_22 : value4 22 = -96 := by decide
theorem evaluated4_23 : value4 23 = 10 := by decide
theorem evaluated4_24 : value4 24 = -28 := by decide
theorem evaluated4_25 : value4 25 = -4 := by decide
theorem evaluated4_26 : value4 26 = -2 := by decide
theorem evaluated4_27 : value4 27 = 40 := by decide
theorem evaluated4_28 : value4 28 = 52 := by decide
theorem evaluated4_29 : value4 29 = -20 := by decide
theorem evaluated4_30 : value4 30 = -42 := by decide
theorem evaluated4_31 : value4 31 = 36 := by decide
theorem evaluated4_32 : value4 32 = -52 := by decide
theorem evaluated4_33 : value4 33 = -232 := by decide
theorem evaluated4_34 : value4 34 = 30 := by decide
theorem evaluated4_35 : value4 35 = 96 := by decide
theorem evaluated4_36 : value4 36 = 30 := by decide
theorem evaluated4_37 : value4 37 = 8 := by decide
theorem evaluated4_38 : value4 38 = 88 := by decide
theorem evaluated4_39 : value4 39 = -282 := by decide
theorem evaluated4_40 : value4 40 = -52 := by decide
theorem evaluated4_41 : value4 41 = 48 := by decide
theorem evaluated4_42 : value4 42 = -172 := by decide
theorem evaluated4_43 : value4 43 = -132 := by decide
theorem evaluated4_44 : value4 44 = -74 := by decide
theorem evaluated4_45 : value4 45 = 146 := by decide
theorem traceless4 : tr (matrix sample4_0) = 0 ∧ tr (matrix sample4_1) = 0 ∧ tr (matrix sample4_2) = 0 := by decide
def sample5_0 : Data := [[2, -1, -2], [2, -2, -2], [-2, 1, 0]]
def sample5_1 : Data := [[-1, -2, 0], [0, 0, 2], [-2, -1, 1]]
def sample5_2 : Data := [[2, 1, -2], [-2, -1, -1], [0, -1, -1]]
def value5 (g : ℕ) : ℤ := sourceE (matrix sample5_0) (matrix sample5_1) (matrix sample5_2) g
theorem evaluated5_1 : value5 1 = 8 := by decide
theorem evaluated5_2 : value5 2 = -2 := by decide
theorem evaluated5_3 : value5 3 = 4 := by decide
theorem evaluated5_4 : value5 4 = 2 := by decide
theorem evaluated5_5 : value5 5 = 15 := by decide
theorem evaluated5_6 : value5 6 = 4 := by decide
theorem evaluated5_7 : value5 7 = 12 := by decide
theorem evaluated5_8 : value5 8 = 18 := by decide
theorem evaluated5_9 : value5 9 = -18 := by decide
theorem evaluated5_10 : value5 10 = -8 := by decide
theorem evaluated5_11 : value5 11 = 22 := by decide
theorem evaluated5_12 : value5 12 = 18 := by decide
theorem evaluated5_13 : value5 13 = -8 := by decide
theorem evaluated5_14 : value5 14 = 16 := by decide
theorem evaluated5_15 : value5 15 = 8 := by decide
theorem evaluated5_16 : value5 16 = -15 := by decide
theorem evaluated5_17 : value5 17 = 31 := by decide
theorem evaluated5_18 : value5 18 = 88 := by decide
theorem evaluated5_19 : value5 19 = -139 := by decide
theorem evaluated5_20 : value5 20 = -18 := by decide
theorem evaluated5_21 : value5 21 = -74 := by decide
theorem evaluated5_22 : value5 22 = 143 := by decide
theorem evaluated5_23 : value5 23 = 52 := by decide
theorem evaluated5_24 : value5 24 = 34 := by decide
theorem evaluated5_25 : value5 25 = -33 := by decide
theorem evaluated5_26 : value5 26 = -28 := by decide
theorem evaluated5_27 : value5 27 = -140 := by decide
theorem evaluated5_28 : value5 28 = 38 := by decide
theorem evaluated5_29 : value5 29 = 36 := by decide
theorem evaluated5_30 : value5 30 = 38 := by decide
theorem evaluated5_31 : value5 31 = 553 := by decide
theorem evaluated5_32 : value5 32 = -76 := by decide
theorem evaluated5_33 : value5 33 = -182 := by decide
theorem evaluated5_34 : value5 34 = -161 := by decide
theorem evaluated5_35 : value5 35 = -372 := by decide
theorem evaluated5_36 : value5 36 = -8 := by decide
theorem evaluated5_37 : value5 37 = 198 := by decide
theorem evaluated5_38 : value5 38 = 8 := by decide
theorem evaluated5_39 : value5 39 = -140 := by decide
theorem evaluated5_40 : value5 40 = 340 := by decide
theorem evaluated5_41 : value5 41 = -18 := by decide
theorem evaluated5_42 : value5 42 = 104 := by decide
theorem evaluated5_43 : value5 43 = -148 := by decide
theorem evaluated5_44 : value5 44 = -980 := by decide
theorem evaluated5_45 : value5 45 = -632 := by decide
theorem traceless5 : tr (matrix sample5_0) = 0 ∧ tr (matrix sample5_1) = 0 ∧ tr (matrix sample5_2) = 0 := by decide
def sample6_0 : Data := [[2, -2, 1], [-1, 0, -1], [2, -1, -2]]
def sample6_1 : Data := [[2, 2, 0], [-1, -1, 1], [-1, -1, -1]]
def sample6_2 : Data := [[-1, -2, -1], [-2, -1, 0], [-1, -2, 2]]
def value6 (g : ℕ) : ℤ := sourceE (matrix sample6_0) (matrix sample6_1) (matrix sample6_2) g
theorem evaluated6_1 : value6 1 = 18 := by decide
theorem evaluated6_2 : value6 2 = 0 := by decide
theorem evaluated6_3 : value6 3 = 16 := by decide
theorem evaluated6_4 : value6 4 = 5 := by decide
theorem evaluated6_5 : value6 5 = -1 := by decide
theorem evaluated6_6 : value6 6 = -6 := by decide
theorem evaluated6_7 : value6 7 = 21 := by decide
theorem evaluated6_8 : value6 8 = 0 := by decide
theorem evaluated6_9 : value6 9 = -27 := by decide
theorem evaluated6_10 : value6 10 = -2 := by decide
theorem evaluated6_11 : value6 11 = 16 := by decide
theorem evaluated6_12 : value6 12 = 12 := by decide
theorem evaluated6_13 : value6 13 = 2 := by decide
theorem evaluated6_14 : value6 14 = -13 := by decide
theorem evaluated6_15 : value6 15 = 3 := by decide
theorem evaluated6_16 : value6 16 = -2 := by decide
theorem evaluated6_17 : value6 17 = -30 := by decide
theorem evaluated6_18 : value6 18 = 29 := by decide
theorem evaluated6_19 : value6 19 = 20 := by decide
theorem evaluated6_20 : value6 20 = -24 := by decide
theorem evaluated6_21 : value6 21 = -50 := by decide
theorem evaluated6_22 : value6 22 = 36 := by decide
theorem evaluated6_23 : value6 23 = 112 := by decide
theorem evaluated6_24 : value6 24 = -10 := by decide
theorem evaluated6_25 : value6 25 = 24 := by decide
theorem evaluated6_26 : value6 26 = 16 := by decide
theorem evaluated6_27 : value6 27 = 80 := by decide
theorem evaluated6_28 : value6 28 = 58 := by decide
theorem evaluated6_29 : value6 29 = -86 := by decide
theorem evaluated6_30 : value6 30 = 18 := by decide
theorem evaluated6_31 : value6 31 = 42 := by decide
theorem evaluated6_32 : value6 32 = -124 := by decide
theorem evaluated6_33 : value6 33 = -94 := by decide
theorem evaluated6_34 : value6 34 = 140 := by decide
theorem evaluated6_35 : value6 35 = -110 := by decide
theorem evaluated6_36 : value6 36 = 186 := by decide
theorem evaluated6_37 : value6 37 = -120 := by decide
theorem evaluated6_38 : value6 38 = 38 := by decide
theorem evaluated6_39 : value6 39 = 358 := by decide
theorem evaluated6_40 : value6 40 = -408 := by decide
theorem evaluated6_41 : value6 41 = -24 := by decide
theorem evaluated6_42 : value6 42 = -136 := by decide
theorem evaluated6_43 : value6 43 = -32 := by decide
theorem evaluated6_44 : value6 44 = -246 := by decide
theorem evaluated6_45 : value6 45 = 808 := by decide
theorem traceless6 : tr (matrix sample6_0) = 0 ∧ tr (matrix sample6_1) = 0 ∧ tr (matrix sample6_2) = 0 := by decide
def sample7_0 : Data := [[-1, -1, 0], [-2, -1, -1], [0, 2, 2]]
def sample7_1 : Data := [[-1, 1, -1], [0, 2, -1], [2, 1, -1]]
def sample7_2 : Data := [[0, 1, -1], [0, 2, -2], [-2, -1, -2]]
def value7 (g : ℕ) : ℤ := sourceE (matrix sample7_0) (matrix sample7_1) (matrix sample7_2) g
theorem evaluated7_1 : value7 1 = 6 := by decide
theorem evaluated7_2 : value7 2 = 0 := by decide
theorem evaluated7_3 : value7 3 = 16 := by decide
theorem evaluated7_4 : value7 4 = -8 := by decide
theorem evaluated7_5 : value7 5 = -11 := by decide
theorem evaluated7_6 : value7 6 = 5 := by decide
theorem evaluated7_7 : value7 7 = -12 := by decide
theorem evaluated7_8 : value7 8 = 9 := by decide
theorem evaluated7_9 : value7 9 = 0 := by decide
theorem evaluated7_10 : value7 10 = 4 := by decide
theorem evaluated7_11 : value7 11 = 1 := by decide
theorem evaluated7_12 : value7 12 = -9 := by decide
theorem evaluated7_13 : value7 13 = 5 := by decide
theorem evaluated7_14 : value7 14 = 0 := by decide
theorem evaluated7_15 : value7 15 = 4 := by decide
theorem evaluated7_16 : value7 16 = -8 := by decide
theorem evaluated7_17 : value7 17 = -44 := by decide
theorem evaluated7_18 : value7 18 = -127 := by decide
theorem evaluated7_19 : value7 19 = -7 := by decide
theorem evaluated7_20 : value7 20 = -25 := by decide
theorem evaluated7_21 : value7 21 = -164 := by decide
theorem evaluated7_22 : value7 22 = 104 := by decide
theorem evaluated7_23 : value7 23 = -200 := by decide
theorem evaluated7_24 : value7 24 = 2 := by decide
theorem evaluated7_25 : value7 25 = 18 := by decide
theorem evaluated7_26 : value7 26 = 2 := by decide
theorem evaluated7_27 : value7 27 = 174 := by decide
theorem evaluated7_28 : value7 28 = 16 := by decide
theorem evaluated7_29 : value7 29 = -308 := by decide
theorem evaluated7_30 : value7 30 = -436 := by decide
theorem evaluated7_31 : value7 31 = 468 := by decide
theorem evaluated7_32 : value7 32 = 14 := by decide
theorem evaluated7_33 : value7 33 = -54 := by decide
theorem evaluated7_34 : value7 34 = -10 := by decide
theorem evaluated7_35 : value7 35 = -22 := by decide
theorem evaluated7_36 : value7 36 = 18 := by decide
theorem evaluated7_37 : value7 37 = 150 := by decide
theorem evaluated7_38 : value7 38 = 92 := by decide
theorem evaluated7_39 : value7 39 = -2 := by decide
theorem evaluated7_40 : value7 40 = -48 := by decide
theorem evaluated7_41 : value7 41 = -90 := by decide
theorem evaluated7_42 : value7 42 = -142 := by decide
theorem evaluated7_43 : value7 43 = 159 := by decide
theorem evaluated7_44 : value7 44 = 24 := by decide
theorem evaluated7_45 : value7 45 = 76 := by decide
theorem traceless7 : tr (matrix sample7_0) = 0 ∧ tr (matrix sample7_1) = 0 ∧ tr (matrix sample7_2) = 0 := by decide
def sample8_0 : Data := [[2, -1, 0], [2, 2, 0], [0, 1, -4]]
def sample8_1 : Data := [[1, -2, -2], [1, -1, -1], [2, -1, 0]]
def sample8_2 : Data := [[1, 0, 0], [2, 0, 0], [-2, 2, -1]]
def value8 (g : ℕ) : ℤ := sourceE (matrix sample8_0) (matrix sample8_1) (matrix sample8_2) g
theorem evaluated8_1 : value8 1 = 20 := by decide
theorem evaluated8_2 : value8 2 = -8 := by decide
theorem evaluated8_3 : value8 3 = 2 := by decide
theorem evaluated8_4 : value8 4 = -6 := by decide
theorem evaluated8_5 : value8 5 = 4 := by decide
theorem evaluated8_6 : value8 6 = -1 := by decide
theorem evaluated8_7 : value8 7 = -72 := by decide
theorem evaluated8_8 : value8 8 = 3 := by decide
theorem evaluated8_9 : value8 9 = 0 := by decide
theorem evaluated8_10 : value8 10 = -22 := by decide
theorem evaluated8_11 : value8 11 = -22 := by decide
theorem evaluated8_12 : value8 12 = 7 := by decide
theorem evaluated8_13 : value8 13 = 0 := by decide
theorem evaluated8_14 : value8 14 = -4 := by decide
theorem evaluated8_15 : value8 15 = -9 := by decide
theorem evaluated8_16 : value8 16 = -34 := by decide
theorem evaluated8_17 : value8 17 = 14 := by decide
theorem evaluated8_18 : value8 18 = -52 := by decide
theorem evaluated8_19 : value8 19 = -6 := by decide
theorem evaluated8_20 : value8 20 = 1 := by decide
theorem evaluated8_21 : value8 21 = -22 := by decide
theorem evaluated8_22 : value8 22 = -7 := by decide
theorem evaluated8_23 : value8 23 = 26 := by decide
theorem evaluated8_24 : value8 24 = -42 := by decide
theorem evaluated8_25 : value8 25 = 25 := by decide
theorem evaluated8_26 : value8 26 = -14 := by decide
theorem evaluated8_27 : value8 27 = 252 := by decide
theorem evaluated8_28 : value8 28 = 9 := by decide
theorem evaluated8_29 : value8 29 = -56 := by decide
theorem evaluated8_30 : value8 30 = 24 := by decide
theorem evaluated8_31 : value8 31 = -252 := by decide
theorem evaluated8_32 : value8 32 = -3 := by decide
theorem evaluated8_33 : value8 33 = 60 := by decide
theorem evaluated8_34 : value8 34 = 128 := by decide
theorem evaluated8_35 : value8 35 = -48 := by decide
theorem evaluated8_36 : value8 36 = 482 := by decide
theorem evaluated8_37 : value8 37 = 0 := by decide
theorem evaluated8_38 : value8 38 = -20 := by decide
theorem evaluated8_39 : value8 39 = 838 := by decide
theorem evaluated8_40 : value8 40 = 602 := by decide
theorem evaluated8_41 : value8 41 = -190 := by decide
theorem evaluated8_42 : value8 42 = -672 := by decide
theorem evaluated8_43 : value8 43 = 32 := by decide
theorem evaluated8_44 : value8 44 = -252 := by decide
theorem evaluated8_45 : value8 45 = -850 := by decide
theorem traceless8 : tr (matrix sample8_0) = 0 ∧ tr (matrix sample8_1) = 0 ∧ tr (matrix sample8_2) = 0 := by decide
def sample9_0 : Data := [[0, 2, 2], [0, -2, 2], [0, -2, 2]]
def sample9_1 : Data := [[2, -2, 2], [1, 1, 1], [0, -1, -3]]
def sample9_2 : Data := [[1, 1, 1], [1, 1, -1], [-2, 1, -2]]
def value9 (g : ℕ) : ℤ := sourceE (matrix sample9_0) (matrix sample9_1) (matrix sample9_2) g
theorem evaluated9_1 : value9 1 = 0 := by decide
theorem evaluated9_2 : value9 2 = 8 := by decide
theorem evaluated9_3 : value9 3 = 2 := by decide
theorem evaluated9_4 : value9 4 = -10 := by decide
theorem evaluated9_5 : value9 5 = -4 := by decide
theorem evaluated9_6 : value9 6 = 6 := by decide
theorem evaluated9_7 : value9 7 = 0 := by decide
theorem evaluated9_8 : value9 8 = -36 := by decide
theorem evaluated9_9 : value9 9 = 18 := by decide
theorem evaluated9_10 : value9 10 = -8 := by decide
theorem evaluated9_11 : value9 11 = -24 := by decide
theorem evaluated9_12 : value9 12 = 28 := by decide
theorem evaluated9_13 : value9 13 = -16 := by decide
theorem evaluated9_14 : value9 14 = 4 := by decide
theorem evaluated9_15 : value9 15 = -6 := by decide
theorem evaluated9_16 : value9 16 = 22 := by decide
theorem evaluated9_17 : value9 17 = 6 := by decide
theorem evaluated9_18 : value9 18 = -196 := by decide
theorem evaluated9_19 : value9 19 = -40 := by decide
theorem evaluated9_20 : value9 20 = -113 := by decide
theorem evaluated9_21 : value9 21 = -104 := by decide
theorem evaluated9_22 : value9 22 = 170 := by decide
theorem evaluated9_23 : value9 23 = 86 := by decide
theorem evaluated9_24 : value9 24 = 88 := by decide
theorem evaluated9_25 : value9 25 = 126 := by decide
theorem evaluated9_26 : value9 26 = -26 := by decide
theorem evaluated9_27 : value9 27 = 336 := by decide
theorem evaluated9_28 : value9 28 = -96 := by decide
theorem evaluated9_29 : value9 29 = -196 := by decide
theorem evaluated9_30 : value9 30 = -116 := by decide
theorem evaluated9_31 : value9 31 = 200 := by decide
theorem evaluated9_32 : value9 32 = -2 := by decide
theorem evaluated9_33 : value9 33 = -140 := by decide
theorem evaluated9_34 : value9 34 = -904 := by decide
theorem evaluated9_35 : value9 35 = -96 := by decide
theorem evaluated9_36 : value9 36 = -608 := by decide
theorem evaluated9_37 : value9 37 = 576 := by decide
theorem evaluated9_38 : value9 38 = 324 := by decide
theorem evaluated9_39 : value9 39 = 608 := by decide
theorem evaluated9_40 : value9 40 = -484 := by decide
theorem evaluated9_41 : value9 41 = 108 := by decide
theorem evaluated9_42 : value9 42 = -32 := by decide
theorem evaluated9_43 : value9 43 = 1276 := by decide
theorem evaluated9_44 : value9 44 = -576 := by decide
theorem evaluated9_45 : value9 45 = 1384 := by decide
theorem traceless9 : tr (matrix sample9_0) = 0 ∧ tr (matrix sample9_1) = 0 ∧ tr (matrix sample9_2) = 0 := by decide
def sample10_0 : Data := [[-1, 0, 0], [0, 0, 0], [-2, 2, 1]]
def sample10_1 : Data := [[1, 1, 0], [-1, 1, 1], [1, 0, -2]]
def sample10_2 : Data := [[-2, -1, 0], [0, 0, 2], [-1, 1, 2]]
def value10 (g : ℕ) : ℤ := sourceE (matrix sample10_0) (matrix sample10_1) (matrix sample10_2) g
theorem evaluated10_1 : value10 1 = 2 := by decide
theorem evaluated10_2 : value10 2 = 4 := by decide
theorem evaluated10_3 : value10 3 = 12 := by decide
theorem evaluated10_4 : value10 4 = -1 := by decide
theorem evaluated10_5 : value10 5 = 8 := by decide
theorem evaluated10_6 : value10 6 = -4 := by decide
theorem evaluated10_7 : value10 7 = 0 := by decide
theorem evaluated10_8 : value10 8 = -9 := by decide
theorem evaluated10_9 : value10 9 = 18 := by decide
theorem evaluated10_10 : value10 10 = 1 := by decide
theorem evaluated10_11 : value10 11 = 4 := by decide
theorem evaluated10_12 : value10 12 = 0 := by decide
theorem evaluated10_13 : value10 13 = 9 := by decide
theorem evaluated10_14 : value10 14 = 14 := by decide
theorem evaluated10_15 : value10 15 = -9 := by decide
theorem evaluated10_16 : value10 16 = -6 := by decide
theorem evaluated10_17 : value10 17 = 10 := by decide
theorem evaluated10_18 : value10 18 = 1 := by decide
theorem evaluated10_19 : value10 19 = -22 := by decide
theorem evaluated10_20 : value10 20 = 23 := by decide
theorem evaluated10_21 : value10 21 = -6 := by decide
theorem evaluated10_22 : value10 22 = 14 := by decide
theorem evaluated10_23 : value10 23 = -11 := by decide
theorem evaluated10_24 : value10 24 = 14 := by decide
theorem evaluated10_25 : value10 25 = 28 := by decide
theorem evaluated10_26 : value10 26 = 37 := by decide
theorem evaluated10_27 : value10 27 = 0 := by decide
theorem evaluated10_28 : value10 28 = -7 := by decide
theorem evaluated10_29 : value10 29 = -34 := by decide
theorem evaluated10_30 : value10 30 = -26 := by decide
theorem evaluated10_31 : value10 31 = 14 := by decide
theorem evaluated10_32 : value10 32 = 59 := by decide
theorem evaluated10_33 : value10 33 = 46 := by decide
theorem evaluated10_34 : value10 34 = -18 := by decide
theorem evaluated10_35 : value10 35 = -32 := by decide
theorem evaluated10_36 : value10 36 = -4 := by decide
theorem evaluated10_37 : value10 37 = -28 := by decide
theorem evaluated10_38 : value10 38 = -15 := by decide
theorem evaluated10_39 : value10 39 = -10 := by decide
theorem evaluated10_40 : value10 40 = -29 := by decide
theorem evaluated10_41 : value10 41 = 28 := by decide
theorem evaluated10_42 : value10 42 = -22 := by decide
theorem evaluated10_43 : value10 43 = 26 := by decide
theorem evaluated10_44 : value10 44 = 78 := by decide
theorem evaluated10_45 : value10 45 = 95 := by decide
theorem traceless10 : tr (matrix sample10_0) = 0 ∧ tr (matrix sample10_1) = 0 ∧ tr (matrix sample10_2) = 0 := by decide
def sample11_0 : Data := [[-1, 0, 2], [-1, 0, 0], [0, -1, 1]]
def sample11_1 : Data := [[-1, -2, -2], [-2, 0, 1], [-1, -1, 1]]
def sample11_2 : Data := [[1, -2, -1], [-2, -1, 1], [1, 0, 0]]
def value11 (g : ℕ) : ℤ := sourceE (matrix sample11_0) (matrix sample11_1) (matrix sample11_2) g
theorem evaluated11_1 : value11 1 = 2 := by decide
theorem evaluated11_2 : value11 2 = 12 := by decide
theorem evaluated11_3 : value11 3 = 8 := by decide
theorem evaluated11_4 : value11 4 = 1 := by decide
theorem evaluated11_5 : value11 5 = 2 := by decide
theorem evaluated11_6 : value11 6 = 5 := by decide
theorem evaluated11_7 : value11 7 = 6 := by decide
theorem evaluated11_8 : value11 8 = -21 := by decide
theorem evaluated11_9 : value11 9 = -9 := by decide
theorem evaluated11_10 : value11 10 = 1 := by decide
theorem evaluated11_11 : value11 11 = 1 := by decide
theorem evaluated11_12 : value11 12 = -10 := by decide
theorem evaluated11_13 : value11 13 = -9 := by decide
theorem evaluated11_14 : value11 14 = -4 := by decide
theorem evaluated11_15 : value11 15 = -9 := by decide
theorem evaluated11_16 : value11 16 = -14 := by decide
theorem evaluated11_17 : value11 17 = 8 := by decide
theorem evaluated11_18 : value11 18 = -7 := by decide
theorem evaluated11_19 : value11 19 = -9 := by decide
theorem evaluated11_20 : value11 20 = 11 := by decide
theorem evaluated11_21 : value11 21 = -50 := by decide
theorem evaluated11_22 : value11 22 = 65 := by decide
theorem evaluated11_23 : value11 23 = -7 := by decide
theorem evaluated11_24 : value11 24 = 8 := by decide
theorem evaluated11_25 : value11 25 = -11 := by decide
theorem evaluated11_26 : value11 26 = -3 := by decide
theorem evaluated11_27 : value11 27 = -13 := by decide
theorem evaluated11_28 : value11 28 = 35 := by decide
theorem evaluated11_29 : value11 29 = 1 := by decide
theorem evaluated11_30 : value11 30 = -44 := by decide
theorem evaluated11_31 : value11 31 = -10 := by decide
theorem evaluated11_32 : value11 32 = -34 := by decide
theorem evaluated11_33 : value11 33 = -56 := by decide
theorem evaluated11_34 : value11 34 = 88 := by decide
theorem evaluated11_35 : value11 35 = -116 := by decide
theorem evaluated11_36 : value11 36 = 20 := by decide
theorem evaluated11_37 : value11 37 = 4 := by decide
theorem evaluated11_38 : value11 38 = -118 := by decide
theorem evaluated11_39 : value11 39 = 74 := by decide
theorem evaluated11_40 : value11 40 = 95 := by decide
theorem evaluated11_41 : value11 41 = -101 := by decide
theorem evaluated11_42 : value11 42 = 67 := by decide
theorem evaluated11_43 : value11 43 = -24 := by decide
theorem evaluated11_44 : value11 44 = -5 := by decide
theorem evaluated11_45 : value11 45 = 135 := by decide
theorem traceless11 : tr (matrix sample11_0) = 0 ∧ tr (matrix sample11_1) = 0 ∧ tr (matrix sample11_2) = 0 := by decide
def sample12_0 : Data := [[-2, -1, -2], [0, 2, -1], [-2, -1, 0]]
def sample12_1 : Data := [[2, 0, 0], [-2, 1, -2], [0, -2, -3]]
def sample12_2 : Data := [[1, 0, -2], [0, 1, 1], [0, 1, -2]]
def value12 (g : ℕ) : ℤ := sourceE (matrix sample12_0) (matrix sample12_1) (matrix sample12_2) g
theorem evaluated12_1 : value12 1 = 18 := by decide
theorem evaluated12_2 : value12 2 = 22 := by decide
theorem evaluated12_3 : value12 3 = 8 := by decide
theorem evaluated12_4 : value12 4 = 4 := by decide
theorem evaluated12_5 : value12 5 = 2 := by decide
theorem evaluated12_6 : value12 6 = 5 := by decide
theorem evaluated12_7 : value12 7 = -24 := by decide
theorem evaluated12_8 : value12 8 = -42 := by decide
theorem evaluated12_9 : value12 9 = -9 := by decide
theorem evaluated12_10 : value12 10 = 6 := by decide
theorem evaluated12_11 : value12 11 = -7 := by decide
theorem evaluated12_12 : value12 12 = -8 := by decide
theorem evaluated12_13 : value12 13 = -17 := by decide
theorem evaluated12_14 : value12 14 = 0 := by decide
theorem evaluated12_15 : value12 15 = -3 := by decide
theorem evaluated12_16 : value12 16 = -12 := by decide
theorem evaluated12_17 : value12 17 = 12 := by decide
theorem evaluated12_18 : value12 18 = 152 := by decide
theorem evaluated12_19 : value12 19 = 71 := by decide
theorem evaluated12_20 : value12 20 = 160 := by decide
theorem evaluated12_21 : value12 21 = 74 := by decide
theorem evaluated12_22 : value12 22 = 192 := by decide
theorem evaluated12_23 : value12 23 = 50 := by decide
theorem evaluated12_24 : value12 24 = -18 := by decide
theorem evaluated12_25 : value12 25 = 96 := by decide
theorem evaluated12_26 : value12 26 = 10 := by decide
theorem evaluated12_27 : value12 27 = 8 := by decide
theorem evaluated12_28 : value12 28 = -16 := by decide
theorem evaluated12_29 : value12 29 = 58 := by decide
theorem evaluated12_30 : value12 30 = 260 := by decide
theorem evaluated12_31 : value12 31 = 44 := by decide
theorem evaluated12_32 : value12 32 = -138 := by decide
theorem evaluated12_33 : value12 33 = -732 := by decide
theorem evaluated12_34 : value12 34 = 94 := by decide
theorem evaluated12_35 : value12 35 = -300 := by decide
theorem evaluated12_36 : value12 36 = -32 := by decide
theorem evaluated12_37 : value12 37 = -38 := by decide
theorem evaluated12_38 : value12 38 = -112 := by decide
theorem evaluated12_39 : value12 39 = -408 := by decide
theorem evaluated12_40 : value12 40 = -840 := by decide
theorem evaluated12_41 : value12 41 = -176 := by decide
theorem evaluated12_42 : value12 42 = -156 := by decide
theorem evaluated12_43 : value12 43 = -8 := by decide
theorem evaluated12_44 : value12 44 = -112 := by decide
theorem evaluated12_45 : value12 45 = -778 := by decide
theorem traceless12 : tr (matrix sample12_0) = 0 ∧ tr (matrix sample12_1) = 0 ∧ tr (matrix sample12_2) = 0 := by decide
def sample13_0 : Data := [[-1, 0, 2], [0, -2, 1], [1, -1, 3]]
def sample13_1 : Data := [[1, -1, 1], [2, -1, -1], [2, 1, 0]]
def sample13_2 : Data := [[1, 2, -2], [1, -2, 2], [0, 1, 1]]
def value13 (g : ℕ) : ℤ := sourceE (matrix sample13_0) (matrix sample13_1) (matrix sample13_2) g
theorem evaluated13_1 : value13 1 = 16 := by decide
theorem evaluated13_2 : value13 2 = 0 := by decide
theorem evaluated13_3 : value13 3 = 14 := by decide
theorem evaluated13_4 : value13 4 = 8 := by decide
theorem evaluated13_5 : value13 5 = 3 := by decide
theorem evaluated13_6 : value13 6 = 3 := by decide
theorem evaluated13_7 : value13 7 = 27 := by decide
theorem evaluated13_8 : value13 8 = 21 := by decide
theorem evaluated13_9 : value13 9 = -24 := by decide
theorem evaluated13_10 : value13 10 = 7 := by decide
theorem evaluated13_11 : value13 11 = 2 := by decide
theorem evaluated13_12 : value13 12 = 10 := by decide
theorem evaluated13_13 : value13 13 = -8 := by decide
theorem evaluated13_14 : value13 14 = -5 := by decide
theorem evaluated13_15 : value13 15 = -14 := by decide
theorem evaluated13_16 : value13 16 = -10 := by decide
theorem evaluated13_17 : value13 17 = 2 := by decide
theorem evaluated13_18 : value13 18 = 14 := by decide
theorem evaluated13_19 : value13 19 = 83 := by decide
theorem evaluated13_20 : value13 20 = 15 := by decide
theorem evaluated13_21 : value13 21 = -39 := by decide
theorem evaluated13_22 : value13 22 = -45 := by decide
theorem evaluated13_23 : value13 23 = 143 := by decide
theorem evaluated13_24 : value13 24 = 7 := by decide
theorem evaluated13_25 : value13 25 = 63 := by decide
theorem evaluated13_26 : value13 26 = -33 := by decide
theorem evaluated13_27 : value13 27 = 6 := by decide
theorem evaluated13_28 : value13 28 = 89 := by decide
theorem evaluated13_29 : value13 29 = 53 := by decide
theorem evaluated13_30 : value13 30 = -182 := by decide
theorem evaluated13_31 : value13 31 = 140 := by decide
theorem evaluated13_32 : value13 32 = -34 := by decide
theorem evaluated13_33 : value13 33 = -192 := by decide
theorem evaluated13_34 : value13 34 = 200 := by decide
theorem evaluated13_35 : value13 35 = -54 := by decide
theorem evaluated13_36 : value13 36 = -21 := by decide
theorem evaluated13_37 : value13 37 = -24 := by decide
theorem evaluated13_38 : value13 38 = 78 := by decide
theorem evaluated13_39 : value13 39 = -84 := by decide
theorem evaluated13_40 : value13 40 = -208 := by decide
theorem evaluated13_41 : value13 41 = 125 := by decide
theorem evaluated13_42 : value13 42 = -86 := by decide
theorem evaluated13_43 : value13 43 = -438 := by decide
theorem evaluated13_44 : value13 44 = 155 := by decide
theorem evaluated13_45 : value13 45 = 436 := by decide
theorem traceless13 : tr (matrix sample13_0) = 0 ∧ tr (matrix sample13_1) = 0 ∧ tr (matrix sample13_2) = 0 := by decide
def sample14_0 : Data := [[1, -2, -1], [-1, -2, -1], [2, -2, 1]]
def sample14_1 : Data := [[-2, 1, 0], [2, -2, -2], [2, -2, 4]]
def sample14_2 : Data := [[2, -1, 0], [2, 0, -2], [-2, -1, -2]]
def value14 (g : ℕ) : ℤ := sourceE (matrix sample14_0) (matrix sample14_1) (matrix sample14_2) g
theorem evaluated14_1 : value14 1 = 10 := by decide
theorem evaluated14_2 : value14 2 = 36 := by decide
theorem evaluated14_3 : value14 3 = 8 := by decide
theorem evaluated14_4 : value14 4 = 5 := by decide
theorem evaluated14_5 : value14 5 = 4 := by decide
theorem evaluated14_6 : value14 6 = -6 := by decide
theorem evaluated14_7 : value14 7 = -24 := by decide
theorem evaluated14_8 : value14 8 = 36 := by decide
theorem evaluated14_9 : value14 9 = -36 := by decide
theorem evaluated14_10 : value14 10 = -7 := by decide
theorem evaluated14_11 : value14 11 = 11 := by decide
theorem evaluated14_12 : value14 12 = 40 := by decide
theorem evaluated14_13 : value14 13 = -12 := by decide
theorem evaluated14_14 : value14 14 = -12 := by decide
theorem evaluated14_15 : value14 15 = 12 := by decide
theorem evaluated14_16 : value14 16 = -16 := by decide
theorem evaluated14_17 : value14 17 = -28 := by decide
theorem evaluated14_18 : value14 18 = -43 := by decide
theorem evaluated14_19 : value14 19 = 106 := by decide
theorem evaluated14_20 : value14 20 = 132 := by decide
theorem evaluated14_21 : value14 21 = 32 := by decide
theorem evaluated14_22 : value14 22 = 300 := by decide
theorem evaluated14_23 : value14 23 = 356 := by decide
theorem evaluated14_24 : value14 24 = -68 := by decide
theorem evaluated14_25 : value14 25 = 32 := by decide
theorem evaluated14_26 : value14 26 = 84 := by decide
theorem evaluated14_27 : value14 27 = 33 := by decide
theorem evaluated14_28 : value14 28 = -628 := by decide
theorem evaluated14_29 : value14 29 = 180 := by decide
theorem evaluated14_30 : value14 30 = 256 := by decide
theorem evaluated14_31 : value14 31 = -60 := by decide
theorem evaluated14_32 : value14 32 = 212 := by decide
theorem evaluated14_33 : value14 33 = 176 := by decide
theorem evaluated14_34 : value14 34 = -536 := by decide
theorem evaluated14_35 : value14 35 = 976 := by decide
theorem evaluated14_36 : value14 36 = 30 := by decide
theorem evaluated14_37 : value14 37 = -192 := by decide
theorem evaluated14_38 : value14 38 = 1456 := by decide
theorem evaluated14_39 : value14 39 = 636 := by decide
theorem evaluated14_40 : value14 40 = 732 := by decide
theorem evaluated14_41 : value14 41 = -88 := by decide
theorem evaluated14_42 : value14 42 = 162 := by decide
theorem evaluated14_43 : value14 43 = -1264 := by decide
theorem evaluated14_44 : value14 44 = -1316 := by decide
theorem evaluated14_45 : value14 45 = 1308 := by decide
theorem traceless14 : tr (matrix sample14_0) = 0 ∧ tr (matrix sample14_1) = 0 ∧ tr (matrix sample14_2) = 0 := by decide
def sample15_0 : Data := [[2, -1, 0], [0, 1, -2], [0, 2, -3]]
def sample15_1 : Data := [[0, -2, 0], [0, 0, 0], [2, 1, 0]]
def sample15_2 : Data := [[1, -1, 2], [1, -1, -2], [-1, -1, 0]]
def value15 (g : ℕ) : ℤ := sourceE (matrix sample15_0) (matrix sample15_1) (matrix sample15_2) g
theorem evaluated15_1 : value15 1 = 6 := by decide
theorem evaluated15_2 : value15 2 = 0 := by decide
theorem evaluated15_3 : value15 3 = 0 := by decide
theorem evaluated15_4 : value15 4 = -2 := by decide
theorem evaluated15_5 : value15 5 = -2 := by decide
theorem evaluated15_6 : value15 6 = 0 := by decide
theorem evaluated15_7 : value15 7 = 6 := by decide
theorem evaluated15_8 : value15 8 = 0 := by decide
theorem evaluated15_9 : value15 9 = -24 := by decide
theorem evaluated15_10 : value15 10 = 8 := by decide
theorem evaluated15_11 : value15 11 = 6 := by decide
theorem evaluated15_12 : value15 12 = 8 := by decide
theorem evaluated15_13 : value15 13 = 8 := by decide
theorem evaluated15_14 : value15 14 = 0 := by decide
theorem evaluated15_15 : value15 15 = 8 := by decide
theorem evaluated15_16 : value15 16 = 0 := by decide
theorem evaluated15_17 : value15 17 = -8 := by decide
theorem evaluated15_18 : value15 18 = -52 := by decide
theorem evaluated15_19 : value15 19 = -100 := by decide
theorem evaluated15_20 : value15 20 = -48 := by decide
theorem evaluated15_21 : value15 21 = 124 := by decide
theorem evaluated15_22 : value15 22 = -72 := by decide
theorem evaluated15_23 : value15 23 = -120 := by decide
theorem evaluated15_24 : value15 24 = -52 := by decide
theorem evaluated15_25 : value15 25 = 40 := by decide
theorem evaluated15_26 : value15 26 = -40 := by decide
theorem evaluated15_27 : value15 27 = 92 := by decide
theorem evaluated15_28 : value15 28 = 48 := by decide
theorem evaluated15_29 : value15 29 = 192 := by decide
theorem evaluated15_30 : value15 30 = 128 := by decide
theorem evaluated15_31 : value15 31 = 0 := by decide
theorem evaluated15_32 : value15 32 = -80 := by decide
theorem evaluated15_33 : value15 33 = -16 := by decide
theorem evaluated15_34 : value15 34 = 144 := by decide
theorem evaluated15_35 : value15 35 = 352 := by decide
theorem evaluated15_36 : value15 36 = 32 := by decide
theorem evaluated15_37 : value15 37 = -256 := by decide
theorem evaluated15_38 : value15 38 = -192 := by decide
theorem evaluated15_39 : value15 39 = 600 := by decide
theorem evaluated15_40 : value15 40 = 240 := by decide
theorem evaluated15_41 : value15 41 = -160 := by decide
theorem evaluated15_42 : value15 42 = -872 := by decide
theorem evaluated15_43 : value15 43 = 320 := by decide
theorem evaluated15_44 : value15 44 = -544 := by decide
theorem evaluated15_45 : value15 45 = -1216 := by decide
theorem traceless15 : tr (matrix sample15_0) = 0 ∧ tr (matrix sample15_1) = 0 ∧ tr (matrix sample15_2) = 0 := by decide
def sample16_0 : Data := [[-1, 2, 1], [0, 1, 1], [0, 0, 0]]
def sample16_1 : Data := [[0, -1, 0], [2, 0, -2], [0, 1, 0]]
def sample16_2 : Data := [[2, 2, -1], [-1, -2, -1], [-2, -1, 0]]
def value16 (g : ℕ) : ℤ := sourceE (matrix sample16_0) (matrix sample16_1) (matrix sample16_2) g
theorem evaluated16_1 : value16 1 = 2 := by decide
theorem evaluated16_2 : value16 2 = -8 := by decide
theorem evaluated16_3 : value16 3 = 10 := by decide
theorem evaluated16_4 : value16 4 = 5 := by decide
theorem evaluated16_5 : value16 5 = -9 := by decide
theorem evaluated16_6 : value16 6 = 6 := by decide
theorem evaluated16_7 : value16 7 = 0 := by decide
theorem evaluated16_8 : value16 8 = 0 := by decide
theorem evaluated16_9 : value16 9 = 15 := by decide
theorem evaluated16_10 : value16 10 = 1 := by decide
theorem evaluated16_11 : value16 11 = -3 := by decide
theorem evaluated16_12 : value16 12 = 0 := by decide
theorem evaluated16_13 : value16 13 = -2 := by decide
theorem evaluated16_14 : value16 14 = -2 := by decide
theorem evaluated16_15 : value16 15 = 7 := by decide
theorem evaluated16_16 : value16 16 = 6 := by decide
theorem evaluated16_17 : value16 17 = 30 := by decide
theorem evaluated16_18 : value16 18 = -29 := by decide
theorem evaluated16_19 : value16 19 = -85 := by decide
theorem evaluated16_20 : value16 20 = -116 := by decide
theorem evaluated16_21 : value16 21 = 102 := by decide
theorem evaluated16_22 : value16 22 = 48 := by decide
theorem evaluated16_23 : value16 23 = 220 := by decide
theorem evaluated16_24 : value16 24 = 0 := by decide
theorem evaluated16_25 : value16 25 = -16 := by decide
theorem evaluated16_26 : value16 26 = 28 := by decide
theorem evaluated16_27 : value16 27 = -10 := by decide
theorem evaluated16_28 : value16 28 = -102 := by decide
theorem evaluated16_29 : value16 29 = 100 := by decide
theorem evaluated16_30 : value16 30 = -142 := by decide
theorem evaluated16_31 : value16 31 = -278 := by decide
theorem evaluated16_32 : value16 32 = 22 := by decide
theorem evaluated16_33 : value16 33 = 82 := by decide
theorem evaluated16_34 : value16 34 = -10 := by decide
theorem evaluated16_35 : value16 35 = 70 := by decide
theorem evaluated16_36 : value16 36 = 20 := by decide
theorem evaluated16_37 : value16 37 = 14 := by decide
theorem evaluated16_38 : value16 38 = 6 := by decide
theorem evaluated16_39 : value16 39 = 58 := by decide
theorem evaluated16_40 : value16 40 = -62 := by decide
theorem evaluated16_41 : value16 41 = 154 := by decide
theorem evaluated16_42 : value16 42 = -16 := by decide
theorem evaluated16_43 : value16 43 = 120 := by decide
theorem evaluated16_44 : value16 44 = -234 := by decide
theorem evaluated16_45 : value16 45 = 196 := by decide
theorem traceless16 : tr (matrix sample16_0) = 0 ∧ tr (matrix sample16_1) = 0 ∧ tr (matrix sample16_2) = 0 := by decide
def sample17_0 : Data := [[-1, 2, 1], [2, -2, 0], [2, 0, 3]]
def sample17_1 : Data := [[-1, -1, -1], [0, -1, 1], [2, -1, 2]]
def sample17_2 : Data := [[2, -2, 1], [-2, 2, 1], [1, 1, -4]]
def value17 (g : ℕ) : ℤ := sourceE (matrix sample17_0) (matrix sample17_1) (matrix sample17_2) g
theorem evaluated17_1 : value17 1 = 26 := by decide
theorem evaluated17_2 : value17 2 = 0 := by decide
theorem evaluated17_3 : value17 3 = 36 := by decide
theorem evaluated17_4 : value17 4 = 7 := by decide
theorem evaluated17_5 : value17 5 = -23 := by decide
theorem evaluated17_6 : value17 6 = -9 := by decide
theorem evaluated17_7 : value17 7 = -6 := by decide
theorem evaluated17_8 : value17 8 = -9 := by decide
theorem evaluated17_9 : value17 9 = -24 := by decide
theorem evaluated17_10 : value17 10 = 15 := by decide
theorem evaluated17_11 : value17 11 = 22 := by decide
theorem evaluated17_12 : value17 12 = 12 := by decide
theorem evaluated17_13 : value17 13 = -18 := by decide
theorem evaluated17_14 : value17 14 = -13 := by decide
theorem evaluated17_15 : value17 15 = 21 := by decide
theorem evaluated17_16 : value17 16 = -31 := by decide
theorem evaluated17_17 : value17 17 = 27 := by decide
theorem evaluated17_18 : value17 18 = -145 := by decide
theorem evaluated17_19 : value17 19 = 110 := by decide
theorem evaluated17_20 : value17 20 = -135 := by decide
theorem evaluated17_21 : value17 21 = -104 := by decide
theorem evaluated17_22 : value17 22 = 324 := by decide
theorem evaluated17_23 : value17 23 = 60 := by decide
theorem evaluated17_24 : value17 24 = 4 := by decide
theorem evaluated17_25 : value17 25 = -42 := by decide
theorem evaluated17_26 : value17 26 = 12 := by decide
theorem evaluated17_27 : value17 27 = -315 := by decide
theorem evaluated17_28 : value17 28 = -105 := by decide
theorem evaluated17_29 : value17 29 = 354 := by decide
theorem evaluated17_30 : value17 30 = -153 := by decide
theorem evaluated17_31 : value17 31 = -559 := by decide
theorem evaluated17_32 : value17 32 = 18 := by decide
theorem evaluated17_33 : value17 33 = 221 := by decide
theorem evaluated17_34 : value17 34 = 157 := by decide
theorem evaluated17_35 : value17 35 = -267 := by decide
theorem evaluated17_36 : value17 36 = -72 := by decide
theorem evaluated17_37 : value17 37 = 15 := by decide
theorem evaluated17_38 : value17 38 = 90 := by decide
theorem evaluated17_39 : value17 39 = -215 := by decide
theorem evaluated17_40 : value17 40 = -42 := by decide
theorem evaluated17_41 : value17 41 = 225 := by decide
theorem evaluated17_42 : value17 42 = 98 := by decide
theorem evaluated17_43 : value17 43 = 345 := by decide
theorem evaluated17_44 : value17 44 = 180 := by decide
theorem evaluated17_45 : value17 45 = -261 := by decide
theorem traceless17 : tr (matrix sample17_0) = 0 ∧ tr (matrix sample17_1) = 0 ∧ tr (matrix sample17_2) = 0 := by decide
def sample18_0 : Data := [[1, 0, -2], [0, -2, 1], [1, 1, 1]]
def sample18_1 : Data := [[-1, 2, -1], [1, -2, -1], [1, 2, 3]]
def sample18_2 : Data := [[-2, -1, 1], [1, -1, 0], [0, -1, 3]]
def value18 (g : ℕ) : ℤ := sourceE (matrix sample18_0) (matrix sample18_1) (matrix sample18_2) g
theorem evaluated18_1 : value18 1 = 4 := by decide
theorem evaluated18_2 : value18 2 = 12 := by decide
theorem evaluated18_3 : value18 3 = 12 := by decide
theorem evaluated18_4 : value18 4 = 4 := by decide
theorem evaluated18_5 : value18 5 = 3 := by decide
theorem evaluated18_6 : value18 6 = 16 := by decide
theorem evaluated18_7 : value18 7 = -21 := by decide
theorem evaluated18_8 : value18 8 = -24 := by decide
theorem evaluated18_9 : value18 9 = 24 := by decide
theorem evaluated18_10 : value18 10 = -16 := by decide
theorem evaluated18_11 : value18 11 = -3 := by decide
theorem evaluated18_12 : value18 12 = -10 := by decide
theorem evaluated18_13 : value18 13 = 12 := by decide
theorem evaluated18_14 : value18 14 = 14 := by decide
theorem evaluated18_15 : value18 15 = 26 := by decide
theorem evaluated18_16 : value18 16 = 12 := by decide
theorem evaluated18_17 : value18 17 = -16 := by decide
theorem evaluated18_18 : value18 18 = -64 := by decide
theorem evaluated18_19 : value18 19 = 3 := by decide
theorem evaluated18_20 : value18 20 = -52 := by decide
theorem evaluated18_21 : value18 21 = 8 := by decide
theorem evaluated18_22 : value18 22 = -110 := by decide
theorem evaluated18_23 : value18 23 = 6 := by decide
theorem evaluated18_24 : value18 24 = -4 := by decide
theorem evaluated18_25 : value18 25 = 58 := by decide
theorem evaluated18_26 : value18 26 = -42 := by decide
theorem evaluated18_27 : value18 27 = 108 := by decide
theorem evaluated18_28 : value18 28 = -216 := by decide
theorem evaluated18_29 : value18 29 = -142 := by decide
theorem evaluated18_30 : value18 30 = 316 := by decide
theorem evaluated18_31 : value18 31 = -280 := by decide
theorem evaluated18_32 : value18 32 = -84 := by decide
theorem evaluated18_33 : value18 33 = 152 := by decide
theorem evaluated18_34 : value18 34 = 36 := by decide
theorem evaluated18_35 : value18 35 = -160 := by decide
theorem evaluated18_36 : value18 36 = -120 := by decide
theorem evaluated18_37 : value18 37 = -190 := by decide
theorem evaluated18_38 : value18 38 = -296 := by decide
theorem evaluated18_39 : value18 39 = 290 := by decide
theorem evaluated18_40 : value18 40 = 416 := by decide
theorem evaluated18_41 : value18 41 = -548 := by decide
theorem evaluated18_42 : value18 42 = 318 := by decide
theorem evaluated18_43 : value18 43 = 332 := by decide
theorem evaluated18_44 : value18 44 = -604 := by decide
theorem evaluated18_45 : value18 45 = 670 := by decide
theorem traceless18 : tr (matrix sample18_0) = 0 ∧ tr (matrix sample18_1) = 0 ∧ tr (matrix sample18_2) = 0 := by decide
def sample19_0 : Data := [[0, -2, 2], [1, -2, 2], [2, 1, 2]]
def sample19_1 : Data := [[-2, 2, 0], [-2, 2, 0], [-1, 0, 0]]
def sample19_2 : Data := [[1, 2, 0], [1, 2, 2], [-2, 0, -3]]
def value19 (g : ℕ) : ℤ := sourceE (matrix sample19_0) (matrix sample19_1) (matrix sample19_2) g
theorem evaluated19_1 : value19 1 = 16 := by decide
theorem evaluated19_2 : value19 2 = 0 := by decide
theorem evaluated19_3 : value19 3 = 18 := by decide
theorem evaluated19_4 : value19 4 = 0 := by decide
theorem evaluated19_5 : value19 5 = -12 := by decide
theorem evaluated19_6 : value19 6 = 0 := by decide
theorem evaluated19_7 : value19 7 = 18 := by decide
theorem evaluated19_8 : value19 8 = 0 := by decide
theorem evaluated19_9 : value19 9 = -24 := by decide
theorem evaluated19_10 : value19 10 = -4 := by decide
theorem evaluated19_11 : value19 11 = -18 := by decide
theorem evaluated19_12 : value19 12 = 0 := by decide
theorem evaluated19_13 : value19 13 = -4 := by decide
theorem evaluated19_14 : value19 14 = 20 := by decide
theorem evaluated19_15 : value19 15 = -12 := by decide
theorem evaluated19_16 : value19 16 = 22 := by decide
theorem evaluated19_17 : value19 17 = -10 := by decide
theorem evaluated19_18 : value19 18 = -12 := by decide
theorem evaluated19_19 : value19 19 = 150 := by decide
theorem evaluated19_20 : value19 20 = 36 := by decide
theorem evaluated19_21 : value19 21 = -96 := by decide
theorem evaluated19_22 : value19 22 = -24 := by decide
theorem evaluated19_23 : value19 23 = -150 := by decide
theorem evaluated19_24 : value19 24 = 32 := by decide
theorem evaluated19_25 : value19 25 = 8 := by decide
theorem evaluated19_26 : value19 26 = -42 := by decide
theorem evaluated19_27 : value19 27 = 248 := by decide
theorem evaluated19_28 : value19 28 = -16 := by decide
theorem evaluated19_29 : value19 29 = -108 := by decide
theorem evaluated19_30 : value19 30 = -120 := by decide
theorem evaluated19_31 : value19 31 = 344 := by decide
theorem evaluated19_32 : value19 32 = -48 := by decide
theorem evaluated19_33 : value19 33 = 136 := by decide
theorem evaluated19_34 : value19 34 = -72 := by decide
theorem evaluated19_35 : value19 35 = 96 := by decide
theorem evaluated19_36 : value19 36 = -16 := by decide
theorem evaluated19_37 : value19 37 = 76 := by decide
theorem evaluated19_38 : value19 38 = 16 := by decide
theorem evaluated19_39 : value19 39 = 352 := by decide
theorem evaluated19_40 : value19 40 = -48 := by decide
theorem evaluated19_41 : value19 41 = -120 := by decide
theorem evaluated19_42 : value19 42 = -396 := by decide
theorem evaluated19_43 : value19 43 = 56 := by decide
theorem evaluated19_44 : value19 44 = -16 := by decide
theorem evaluated19_45 : value19 45 = 668 := by decide
theorem traceless19 : tr (matrix sample19_0) = 0 ∧ tr (matrix sample19_1) = 0 ∧ tr (matrix sample19_2) = 0 := by decide
def sample20_0 : Data := [[-1, -1, 2], [0, 0, -1], [2, -2, 1]]
def sample20_1 : Data := [[-2, -1, -2], [-1, -1, 1], [-2, 1, 3]]
def sample20_2 : Data := [[2, 1, 0], [1, -1, 2], [0, 1, -1]]
def value20 (g : ℕ) : ℤ := sourceE (matrix sample20_0) (matrix sample20_1) (matrix sample20_2) g
theorem evaluated20_1 : value20 1 = 14 := by decide
theorem evaluated20_2 : value20 2 = 26 := by decide
theorem evaluated20_3 : value20 3 = 12 := by decide
theorem evaluated20_4 : value20 4 = -5 := by decide
theorem evaluated20_5 : value20 5 = -9 := by decide
theorem evaluated20_6 : value20 6 = -5 := by decide
theorem evaluated20_7 : value20 7 = 12 := by decide
theorem evaluated20_8 : value20 8 = 39 := by decide
theorem evaluated20_9 : value20 9 = -3 := by decide
theorem evaluated20_10 : value20 10 = 7 := by decide
theorem evaluated20_11 : value20 11 = -13 := by decide
theorem evaluated20_12 : value20 12 = -20 := by decide
theorem evaluated20_13 : value20 13 = 15 := by decide
theorem evaluated20_14 : value20 14 = 13 := by decide
theorem evaluated20_15 : value20 15 = -19 := by decide
theorem evaluated20_16 : value20 16 = 7 := by decide
theorem evaluated20_17 : value20 17 = 7 := by decide
theorem evaluated20_18 : value20 18 = 156 := by decide
theorem evaluated20_19 : value20 19 = 39 := by decide
theorem evaluated20_20 : value20 20 = 23 := by decide
theorem evaluated20_21 : value20 21 = -107 := by decide
theorem evaluated20_22 : value20 22 = -125 := by decide
theorem evaluated20_23 : value20 23 = -15 := by decide
theorem evaluated20_24 : value20 24 = 17 := by decide
theorem evaluated20_25 : value20 25 = -33 := by decide
theorem evaluated20_26 : value20 26 = -27 := by decide
theorem evaluated20_27 : value20 27 = -28 := by decide
theorem evaluated20_28 : value20 28 = 24 := by decide
theorem evaluated20_29 : value20 29 = -27 := by decide
theorem evaluated20_30 : value20 30 = 181 := by decide
theorem evaluated20_31 : value20 31 = 35 := by decide
theorem evaluated20_32 : value20 32 = 83 := by decide
theorem evaluated20_33 : value20 33 = -71 := by decide
theorem evaluated20_34 : value20 34 = 59 := by decide
theorem evaluated20_35 : value20 35 = 55 := by decide
theorem evaluated20_36 : value20 36 = -115 := by decide
theorem evaluated20_37 : value20 37 = 75 := by decide
theorem evaluated20_38 : value20 38 = 0 := by decide
theorem evaluated20_39 : value20 39 = -485 := by decide
theorem evaluated20_40 : value20 40 = 200 := by decide
theorem evaluated20_41 : value20 41 = 137 := by decide
theorem evaluated20_42 : value20 42 = 365 := by decide
theorem evaluated20_43 : value20 43 = -258 := by decide
theorem evaluated20_44 : value20 44 = -244 := by decide
theorem evaluated20_45 : value20 45 = -700 := by decide
theorem traceless20 : tr (matrix sample20_0) = 0 ∧ tr (matrix sample20_1) = 0 ∧ tr (matrix sample20_2) = 0 := by decide

#print axioms evaluated20_45
end TraceSamples
