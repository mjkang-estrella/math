import Definitions
namespace EBC337062
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Source-zero BFS distance and multiplicity data, computed independently in this lane. -/
def distance0 (x : ℕ) : ℕ :=
  match x with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 3
  | 6 => 2
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | 10 => 2
  | 11 => 3
  | 12 => 4
  | 13 => 3
  | 14 => 2
  | 15 => 3
  | 16 => 2
  | 17 => 3
  | 18 => 2
  | 19 => 3
  | 20 => 4
  | 21 => 3
  | 22 => 2
  | 23 => 1
  | 24 => 2
  | 25 => 1
  | 26 => 2
  | 27 => 3
  | 28 => 4
  | 29 => 3
  | 30 => 2
  | 31 => 1
  | _ => 0

def count0 (x : ℕ) : ℕ :=
  match x with
  | 0 => 1
  | 1 => 1
  | 2 => 3
  | 3 => 7
  | 4 => 41
  | 5 => 7
  | 6 => 2
  | 7 => 1
  | 8 => 4
  | 9 => 1
  | 10 => 2
  | 11 => 7
  | 12 => 40
  | 13 => 6
  | 14 => 2
  | 15 => 18
  | 16 => 4
  | 17 => 18
  | 18 => 2
  | 19 => 6
  | 20 => 40
  | 21 => 7
  | 22 => 2
  | 23 => 1
  | 24 => 4
  | 25 => 1
  | 26 => 2
  | 27 => 7
  | 28 => 41
  | 29 => 7
  | 30 => 3
  | 31 => 1
  | _ => 0

def tabDist (x y : ℕ) : ℕ := distance0 ((y + 32 - x) % 32)
def tabCount (x y : ℕ) : ℕ := count0 ((y + 32 - x) % 32)
/-- Oriented splitting numerator. This is arithmetic, not yet identified with paths. -/
def oriented (x y u v : ℕ) : ℕ :=
  if tabDist x u + 1 + tabDist v y = tabDist x y then
    tabCount x u * tabCount v y else 0

def scaledTerm (x y u v : ℕ) : ℕ :=
  if x = y then 0 else
    (oriented x y u v + oriented x y v u) * (103320 / tabCount x y)
def scaledRow (u v x : ℕ) : ℕ :=
  ((List.range 32).map (fun y => scaledTerm x y u v)).sum

theorem row_1_0 : scaledRow 0 1 0 = 533799 := by decide
theorem row_1_1 : scaledRow 0 1 1 = 533799 := by decide
theorem row_1_2 : scaledRow 0 1 2 = 101652 := by decide
theorem row_1_3 : scaledRow 0 1 3 = 67149 := by decide
theorem row_1_4 : scaledRow 0 1 4 = 17640 := by decide
theorem row_1_5 : scaledRow 0 1 5 = 17640 := by decide
theorem row_1_6 : scaledRow 0 1 6 = 44766 := by decide
theorem row_1_7 : scaledRow 0 1 7 = 127072 := by decide
theorem row_1_8 : scaledRow 0 1 8 = 37310 := by decide
theorem row_1_9 : scaledRow 0 1 9 = 37310 := by decide
theorem row_1_10 : scaledRow 0 1 10 = 127135 := by decide
theorem row_1_11 : scaledRow 0 1 11 = 44892 := by decide
theorem row_1_12 : scaledRow 0 1 12 = 18081 := by decide
theorem row_1_13 : scaledRow 0 1 13 = 15498 := by decide
theorem row_1_14 : scaledRow 0 1 14 = 49812 := by decide
theorem row_1_15 : scaledRow 0 1 15 = 11480 := by decide
theorem row_1_16 : scaledRow 0 1 16 = 22960 := by decide
theorem row_1_17 : scaledRow 0 1 17 = 22960 := by decide
theorem row_1_18 : scaledRow 0 1 18 = 11480 := by decide
theorem row_1_19 : scaledRow 0 1 19 = 49812 := by decide
theorem row_1_20 : scaledRow 0 1 20 = 15498 := by decide
theorem row_1_21 : scaledRow 0 1 21 = 18081 := by decide
theorem row_1_22 : scaledRow 0 1 22 = 44892 := by decide
theorem row_1_23 : scaledRow 0 1 23 = 127135 := by decide
theorem row_1_24 : scaledRow 0 1 24 = 37310 := by decide
theorem row_1_25 : scaledRow 0 1 25 = 37310 := by decide
theorem row_1_26 : scaledRow 0 1 26 = 127072 := by decide
theorem row_1_27 : scaledRow 0 1 27 = 44766 := by decide
theorem row_1_28 : scaledRow 0 1 28 = 17640 := by decide
theorem row_1_29 : scaledRow 0 1 29 = 17640 := by decide
theorem row_1_30 : scaledRow 0 1 30 = 67149 := by decide
theorem row_1_31 : scaledRow 0 1 31 = 101652 := by decide

theorem scaled_total_1 : ((List.range 32).map (scaledRow 0 1)).sum = 2548392 := by
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, row_1_0, row_1_1, row_1_2, row_1_3, row_1_4, row_1_5, row_1_6, row_1_7, row_1_8, row_1_9, row_1_10, row_1_11, row_1_12, row_1_13, row_1_14, row_1_15, row_1_16, row_1_17, row_1_18, row_1_19, row_1_20, row_1_21, row_1_22, row_1_23, row_1_24, row_1_25, row_1_26, row_1_27, row_1_28, row_1_29, row_1_30, row_1_31]
  norm_num

theorem row_9_0 : scaledRow 0 9 0 = 533862 := by decide
theorem row_9_1 : scaledRow 0 9 1 = 37310 := by decide
theorem row_9_2 : scaledRow 0 9 2 = 101652 := by decide
theorem row_9_3 : scaledRow 0 9 3 = 44766 := by decide
theorem row_9_4 : scaledRow 0 9 4 = 17640 := by decide
theorem row_9_5 : scaledRow 0 9 5 = 17640 := by decide
theorem row_9_6 : scaledRow 0 9 6 = 44766 := by decide
theorem row_9_7 : scaledRow 0 9 7 = 101652 := by decide
theorem row_9_8 : scaledRow 0 9 8 = 37310 := by decide
theorem row_9_9 : scaledRow 0 9 9 = 533862 := by decide
theorem row_9_10 : scaledRow 0 9 10 = 127135 := by decide
theorem row_9_11 : scaledRow 0 9 11 = 67338 := by decide
theorem row_9_12 : scaledRow 0 9 12 = 18081 := by decide
theorem row_9_13 : scaledRow 0 9 13 = 15120 := by decide
theorem row_9_14 : scaledRow 0 9 14 = 44766 := by decide
theorem row_9_15 : scaledRow 0 9 15 = 11480 := by decide
theorem row_9_16 : scaledRow 0 9 16 = 37310 := by decide
theorem row_9_17 : scaledRow 0 9 17 = 22960 := by decide
theorem row_9_18 : scaledRow 0 9 18 = 127135 := by decide
theorem row_9_19 : scaledRow 0 9 19 = 49812 := by decide
theorem row_9_20 : scaledRow 0 9 20 = 18081 := by decide
theorem row_9_21 : scaledRow 0 9 21 = 18081 := by decide
theorem row_9_22 : scaledRow 0 9 22 = 49812 := by decide
theorem row_9_23 : scaledRow 0 9 23 = 127135 := by decide
theorem row_9_24 : scaledRow 0 9 24 = 22960 := by decide
theorem row_9_25 : scaledRow 0 9 25 = 37310 := by decide
theorem row_9_26 : scaledRow 0 9 26 = 11480 := by decide
theorem row_9_27 : scaledRow 0 9 27 = 44766 := by decide
theorem row_9_28 : scaledRow 0 9 28 = 15120 := by decide
theorem row_9_29 : scaledRow 0 9 29 = 18081 := by decide
theorem row_9_30 : scaledRow 0 9 30 = 67338 := by decide
theorem row_9_31 : scaledRow 0 9 31 = 127135 := by decide

theorem scaled_total_9 : ((List.range 32).map (scaledRow 0 9)).sum = 2548896 := by
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, row_9_0, row_9_1, row_9_2, row_9_3, row_9_4, row_9_5, row_9_6, row_9_7, row_9_8, row_9_9, row_9_10, row_9_11, row_9_12, row_9_13, row_9_14, row_9_15, row_9_16, row_9_17, row_9_18, row_9_19, row_9_20, row_9_21, row_9_22, row_9_23, row_9_24, row_9_25, row_9_26, row_9_27, row_9_28, row_9_29, row_9_30, row_9_31]
  norm_num

theorem fractions_differ : (15169 / 615 : ℚ) ≠ 15172 / 615 := by norm_num

def rationalTerm (x y u v : ℕ) : ℚ :=
  if x = y then 0 else
    ((oriented x y u v + oriented x y v u : ℕ) : ℚ) / tabCount x y
def rationalRow (u v x : ℕ) : ℚ :=
  ((List.range 32).map (fun y => rationalTerm x y u v)).sum
end EBC337062
