import Certificate
namespace R162
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem row_11 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (11 : Fin 88) j ↔
 (11 : Fin 88) ≠ j ∧ (next (11 : Fin 88) = j ∨ next j = (11 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((11 : Fin 88) ≠ j ∧ ((11,j.val) ∈ edges (nanostar 4) ∨ (j.val,11) ∈ edges (nanostar 4))) ↔
   (11 : Fin 88) ≠ j ∧ (next (11 : Fin 88) = j ∨ next j = (11 : Fin 88))
 decide
theorem row_12 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (12 : Fin 88) j ↔
 (12 : Fin 88) ≠ j ∧ (next (12 : Fin 88) = j ∨ next j = (12 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((12 : Fin 88) ≠ j ∧ ((12,j.val) ∈ edges (nanostar 4) ∨ (j.val,12) ∈ edges (nanostar 4))) ↔
   (12 : Fin 88) ≠ j ∧ (next (12 : Fin 88) = j ∨ next j = (12 : Fin 88))
 decide
theorem row_13 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (13 : Fin 88) j ↔
 (13 : Fin 88) ≠ j ∧ (next (13 : Fin 88) = j ∨ next j = (13 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((13 : Fin 88) ≠ j ∧ ((13,j.val) ∈ edges (nanostar 4) ∨ (j.val,13) ∈ edges (nanostar 4))) ↔
   (13 : Fin 88) ≠ j ∧ (next (13 : Fin 88) = j ∨ next j = (13 : Fin 88))
 decide
theorem row_14 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (14 : Fin 88) j ↔
 (14 : Fin 88) ≠ j ∧ (next (14 : Fin 88) = j ∨ next j = (14 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((14 : Fin 88) ≠ j ∧ ((14,j.val) ∈ edges (nanostar 4) ∨ (j.val,14) ∈ edges (nanostar 4))) ↔
   (14 : Fin 88) ≠ j ∧ (next (14 : Fin 88) = j ∨ next j = (14 : Fin 88))
 decide
theorem row_15 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (15 : Fin 88) j ↔
 (15 : Fin 88) ≠ j ∧ (next (15 : Fin 88) = j ∨ next j = (15 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((15 : Fin 88) ≠ j ∧ ((15,j.val) ∈ edges (nanostar 4) ∨ (j.val,15) ∈ edges (nanostar 4))) ↔
   (15 : Fin 88) ≠ j ∧ (next (15 : Fin 88) = j ∨ next j = (15 : Fin 88))
 decide
theorem row_16 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (16 : Fin 88) j ↔
 (16 : Fin 88) ≠ j ∧ (next (16 : Fin 88) = j ∨ next j = (16 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((16 : Fin 88) ≠ j ∧ ((16,j.val) ∈ edges (nanostar 4) ∨ (j.val,16) ∈ edges (nanostar 4))) ↔
   (16 : Fin 88) ≠ j ∧ (next (16 : Fin 88) = j ∨ next j = (16 : Fin 88))
 decide
theorem row_17 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (17 : Fin 88) j ↔
 (17 : Fin 88) ≠ j ∧ (next (17 : Fin 88) = j ∨ next j = (17 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((17 : Fin 88) ≠ j ∧ ((17,j.val) ∈ edges (nanostar 4) ∨ (j.val,17) ∈ edges (nanostar 4))) ↔
   (17 : Fin 88) ≠ j ∧ (next (17 : Fin 88) = j ∨ next j = (17 : Fin 88))
 decide
theorem row_18 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (18 : Fin 88) j ↔
 (18 : Fin 88) ≠ j ∧ (next (18 : Fin 88) = j ∨ next j = (18 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((18 : Fin 88) ≠ j ∧ ((18,j.val) ∈ edges (nanostar 4) ∨ (j.val,18) ∈ edges (nanostar 4))) ↔
   (18 : Fin 88) ≠ j ∧ (next (18 : Fin 88) = j ∨ next j = (18 : Fin 88))
 decide
theorem row_19 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (19 : Fin 88) j ↔
 (19 : Fin 88) ≠ j ∧ (next (19 : Fin 88) = j ∨ next j = (19 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((19 : Fin 88) ≠ j ∧ ((19,j.val) ∈ edges (nanostar 4) ∨ (j.val,19) ∈ edges (nanostar 4))) ↔
   (19 : Fin 88) ≠ j ∧ (next (19 : Fin 88) = j ∨ next j = (19 : Fin 88))
 decide
theorem row_20 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (20 : Fin 88) j ↔
 (20 : Fin 88) ≠ j ∧ (next (20 : Fin 88) = j ∨ next j = (20 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((20 : Fin 88) ≠ j ∧ ((20,j.val) ∈ edges (nanostar 4) ∨ (j.val,20) ∈ edges (nanostar 4))) ↔
   (20 : Fin 88) ≠ j ∧ (next (20 : Fin 88) = j ∨ next j = (20 : Fin 88))
 decide
theorem row_21 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (21 : Fin 88) j ↔
 (21 : Fin 88) ≠ j ∧ (next (21 : Fin 88) = j ∨ next j = (21 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((21 : Fin 88) ≠ j ∧ ((21,j.val) ∈ edges (nanostar 4) ∨ (j.val,21) ∈ edges (nanostar 4))) ↔
   (21 : Fin 88) ≠ j ∧ (next (21 : Fin 88) = j ∨ next j = (21 : Fin 88))
 decide
end R162
