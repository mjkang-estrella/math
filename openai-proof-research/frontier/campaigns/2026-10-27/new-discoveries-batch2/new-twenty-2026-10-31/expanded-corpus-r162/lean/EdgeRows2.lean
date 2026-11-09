import Certificate
namespace R162
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem row_22 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (22 : Fin 88) j ↔
 (22 : Fin 88) ≠ j ∧ (next (22 : Fin 88) = j ∨ next j = (22 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((22 : Fin 88) ≠ j ∧ ((22,j.val) ∈ edges (nanostar 4) ∨ (j.val,22) ∈ edges (nanostar 4))) ↔
   (22 : Fin 88) ≠ j ∧ (next (22 : Fin 88) = j ∨ next j = (22 : Fin 88))
 decide
theorem row_23 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (23 : Fin 88) j ↔
 (23 : Fin 88) ≠ j ∧ (next (23 : Fin 88) = j ∨ next j = (23 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((23 : Fin 88) ≠ j ∧ ((23,j.val) ∈ edges (nanostar 4) ∨ (j.val,23) ∈ edges (nanostar 4))) ↔
   (23 : Fin 88) ≠ j ∧ (next (23 : Fin 88) = j ∨ next j = (23 : Fin 88))
 decide
theorem row_24 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (24 : Fin 88) j ↔
 (24 : Fin 88) ≠ j ∧ (next (24 : Fin 88) = j ∨ next j = (24 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((24 : Fin 88) ≠ j ∧ ((24,j.val) ∈ edges (nanostar 4) ∨ (j.val,24) ∈ edges (nanostar 4))) ↔
   (24 : Fin 88) ≠ j ∧ (next (24 : Fin 88) = j ∨ next j = (24 : Fin 88))
 decide
theorem row_25 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (25 : Fin 88) j ↔
 (25 : Fin 88) ≠ j ∧ (next (25 : Fin 88) = j ∨ next j = (25 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((25 : Fin 88) ≠ j ∧ ((25,j.val) ∈ edges (nanostar 4) ∨ (j.val,25) ∈ edges (nanostar 4))) ↔
   (25 : Fin 88) ≠ j ∧ (next (25 : Fin 88) = j ∨ next j = (25 : Fin 88))
 decide
theorem row_26 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (26 : Fin 88) j ↔
 (26 : Fin 88) ≠ j ∧ (next (26 : Fin 88) = j ∨ next j = (26 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((26 : Fin 88) ≠ j ∧ ((26,j.val) ∈ edges (nanostar 4) ∨ (j.val,26) ∈ edges (nanostar 4))) ↔
   (26 : Fin 88) ≠ j ∧ (next (26 : Fin 88) = j ∨ next j = (26 : Fin 88))
 decide
theorem row_27 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (27 : Fin 88) j ↔
 (27 : Fin 88) ≠ j ∧ (next (27 : Fin 88) = j ∨ next j = (27 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((27 : Fin 88) ≠ j ∧ ((27,j.val) ∈ edges (nanostar 4) ∨ (j.val,27) ∈ edges (nanostar 4))) ↔
   (27 : Fin 88) ≠ j ∧ (next (27 : Fin 88) = j ∨ next j = (27 : Fin 88))
 decide
theorem row_28 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (28 : Fin 88) j ↔
 (28 : Fin 88) ≠ j ∧ (next (28 : Fin 88) = j ∨ next j = (28 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((28 : Fin 88) ≠ j ∧ ((28,j.val) ∈ edges (nanostar 4) ∨ (j.val,28) ∈ edges (nanostar 4))) ↔
   (28 : Fin 88) ≠ j ∧ (next (28 : Fin 88) = j ∨ next j = (28 : Fin 88))
 decide
theorem row_29 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (29 : Fin 88) j ↔
 (29 : Fin 88) ≠ j ∧ (next (29 : Fin 88) = j ∨ next j = (29 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((29 : Fin 88) ≠ j ∧ ((29,j.val) ∈ edges (nanostar 4) ∨ (j.val,29) ∈ edges (nanostar 4))) ↔
   (29 : Fin 88) ≠ j ∧ (next (29 : Fin 88) = j ∨ next j = (29 : Fin 88))
 decide
theorem row_30 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (30 : Fin 88) j ↔
 (30 : Fin 88) ≠ j ∧ (next (30 : Fin 88) = j ∨ next j = (30 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((30 : Fin 88) ≠ j ∧ ((30,j.val) ∈ edges (nanostar 4) ∨ (j.val,30) ∈ edges (nanostar 4))) ↔
   (30 : Fin 88) ≠ j ∧ (next (30 : Fin 88) = j ∨ next j = (30 : Fin 88))
 decide
theorem row_31 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (31 : Fin 88) j ↔
 (31 : Fin 88) ≠ j ∧ (next (31 : Fin 88) = j ∨ next j = (31 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((31 : Fin 88) ≠ j ∧ ((31,j.val) ∈ edges (nanostar 4) ∨ (j.val,31) ∈ edges (nanostar 4))) ↔
   (31 : Fin 88) ≠ j ∧ (next (31 : Fin 88) = j ∨ next j = (31 : Fin 88))
 decide
theorem row_32 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (32 : Fin 88) j ↔
 (32 : Fin 88) ≠ j ∧ (next (32 : Fin 88) = j ∨ next j = (32 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((32 : Fin 88) ≠ j ∧ ((32,j.val) ∈ edges (nanostar 4) ∨ (j.val,32) ∈ edges (nanostar 4))) ↔
   (32 : Fin 88) ≠ j ∧ (next (32 : Fin 88) = j ∨ next j = (32 : Fin 88))
 decide
end R162
