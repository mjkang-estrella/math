import Certificate
namespace R162
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem row_0 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (0 : Fin 88) j ↔
 (0 : Fin 88) ≠ j ∧ (next (0 : Fin 88) = j ∨ next j = (0 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((0 : Fin 88) ≠ j ∧ ((0,j.val) ∈ edges (nanostar 4) ∨ (j.val,0) ∈ edges (nanostar 4))) ↔
   (0 : Fin 88) ≠ j ∧ (next (0 : Fin 88) = j ∨ next j = (0 : Fin 88))
 decide
theorem row_1 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (1 : Fin 88) j ↔
 (1 : Fin 88) ≠ j ∧ (next (1 : Fin 88) = j ∨ next j = (1 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((1 : Fin 88) ≠ j ∧ ((1,j.val) ∈ edges (nanostar 4) ∨ (j.val,1) ∈ edges (nanostar 4))) ↔
   (1 : Fin 88) ≠ j ∧ (next (1 : Fin 88) = j ∨ next j = (1 : Fin 88))
 decide
theorem row_2 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (2 : Fin 88) j ↔
 (2 : Fin 88) ≠ j ∧ (next (2 : Fin 88) = j ∨ next j = (2 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((2 : Fin 88) ≠ j ∧ ((2,j.val) ∈ edges (nanostar 4) ∨ (j.val,2) ∈ edges (nanostar 4))) ↔
   (2 : Fin 88) ≠ j ∧ (next (2 : Fin 88) = j ∨ next j = (2 : Fin 88))
 decide
theorem row_3 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (3 : Fin 88) j ↔
 (3 : Fin 88) ≠ j ∧ (next (3 : Fin 88) = j ∨ next j = (3 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((3 : Fin 88) ≠ j ∧ ((3,j.val) ∈ edges (nanostar 4) ∨ (j.val,3) ∈ edges (nanostar 4))) ↔
   (3 : Fin 88) ≠ j ∧ (next (3 : Fin 88) = j ∨ next j = (3 : Fin 88))
 decide
theorem row_4 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (4 : Fin 88) j ↔
 (4 : Fin 88) ≠ j ∧ (next (4 : Fin 88) = j ∨ next j = (4 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((4 : Fin 88) ≠ j ∧ ((4,j.val) ∈ edges (nanostar 4) ∨ (j.val,4) ∈ edges (nanostar 4))) ↔
   (4 : Fin 88) ≠ j ∧ (next (4 : Fin 88) = j ∨ next j = (4 : Fin 88))
 decide
theorem row_5 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (5 : Fin 88) j ↔
 (5 : Fin 88) ≠ j ∧ (next (5 : Fin 88) = j ∨ next j = (5 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((5 : Fin 88) ≠ j ∧ ((5,j.val) ∈ edges (nanostar 4) ∨ (j.val,5) ∈ edges (nanostar 4))) ↔
   (5 : Fin 88) ≠ j ∧ (next (5 : Fin 88) = j ∨ next j = (5 : Fin 88))
 decide
theorem row_6 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (6 : Fin 88) j ↔
 (6 : Fin 88) ≠ j ∧ (next (6 : Fin 88) = j ∨ next j = (6 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((6 : Fin 88) ≠ j ∧ ((6,j.val) ∈ edges (nanostar 4) ∨ (j.val,6) ∈ edges (nanostar 4))) ↔
   (6 : Fin 88) ≠ j ∧ (next (6 : Fin 88) = j ∨ next j = (6 : Fin 88))
 decide
theorem row_7 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (7 : Fin 88) j ↔
 (7 : Fin 88) ≠ j ∧ (next (7 : Fin 88) = j ∨ next j = (7 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((7 : Fin 88) ≠ j ∧ ((7,j.val) ∈ edges (nanostar 4) ∨ (j.val,7) ∈ edges (nanostar 4))) ↔
   (7 : Fin 88) ≠ j ∧ (next (7 : Fin 88) = j ∨ next j = (7 : Fin 88))
 decide
theorem row_8 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (8 : Fin 88) j ↔
 (8 : Fin 88) ≠ j ∧ (next (8 : Fin 88) = j ∨ next j = (8 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((8 : Fin 88) ≠ j ∧ ((8,j.val) ∈ edges (nanostar 4) ∨ (j.val,8) ∈ edges (nanostar 4))) ↔
   (8 : Fin 88) ≠ j ∧ (next (8 : Fin 88) = j ∨ next j = (8 : Fin 88))
 decide
theorem row_9 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (9 : Fin 88) j ↔
 (9 : Fin 88) ≠ j ∧ (next (9 : Fin 88) = j ∨ next j = (9 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((9 : Fin 88) ≠ j ∧ ((9,j.val) ∈ edges (nanostar 4) ∨ (j.val,9) ∈ edges (nanostar 4))) ↔
   (9 : Fin 88) ≠ j ∧ (next (9 : Fin 88) = j ∨ next j = (9 : Fin 88))
 decide
theorem row_10 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (10 : Fin 88) j ↔
 (10 : Fin 88) ≠ j ∧ (next (10 : Fin 88) = j ∨ next j = (10 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((10 : Fin 88) ≠ j ∧ ((10,j.val) ∈ edges (nanostar 4) ∨ (j.val,10) ∈ edges (nanostar 4))) ↔
   (10 : Fin 88) ≠ j ∧ (next (10 : Fin 88) = j ∨ next j = (10 : Fin 88))
 decide
end R162
