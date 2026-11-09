import Certificate
namespace R162
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem row_33 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (33 : Fin 88) j ↔
 (33 : Fin 88) ≠ j ∧ (next (33 : Fin 88) = j ∨ next j = (33 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((33 : Fin 88) ≠ j ∧ ((33,j.val) ∈ edges (nanostar 4) ∨ (j.val,33) ∈ edges (nanostar 4))) ↔
   (33 : Fin 88) ≠ j ∧ (next (33 : Fin 88) = j ∨ next j = (33 : Fin 88))
 decide
theorem row_34 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (34 : Fin 88) j ↔
 (34 : Fin 88) ≠ j ∧ (next (34 : Fin 88) = j ∨ next j = (34 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((34 : Fin 88) ≠ j ∧ ((34,j.val) ∈ edges (nanostar 4) ∨ (j.val,34) ∈ edges (nanostar 4))) ↔
   (34 : Fin 88) ≠ j ∧ (next (34 : Fin 88) = j ∨ next j = (34 : Fin 88))
 decide
theorem row_35 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (35 : Fin 88) j ↔
 (35 : Fin 88) ≠ j ∧ (next (35 : Fin 88) = j ∨ next j = (35 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((35 : Fin 88) ≠ j ∧ ((35,j.val) ∈ edges (nanostar 4) ∨ (j.val,35) ∈ edges (nanostar 4))) ↔
   (35 : Fin 88) ≠ j ∧ (next (35 : Fin 88) = j ∨ next j = (35 : Fin 88))
 decide
theorem row_36 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (36 : Fin 88) j ↔
 (36 : Fin 88) ≠ j ∧ (next (36 : Fin 88) = j ∨ next j = (36 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((36 : Fin 88) ≠ j ∧ ((36,j.val) ∈ edges (nanostar 4) ∨ (j.val,36) ∈ edges (nanostar 4))) ↔
   (36 : Fin 88) ≠ j ∧ (next (36 : Fin 88) = j ∨ next j = (36 : Fin 88))
 decide
theorem row_37 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (37 : Fin 88) j ↔
 (37 : Fin 88) ≠ j ∧ (next (37 : Fin 88) = j ∨ next j = (37 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((37 : Fin 88) ≠ j ∧ ((37,j.val) ∈ edges (nanostar 4) ∨ (j.val,37) ∈ edges (nanostar 4))) ↔
   (37 : Fin 88) ≠ j ∧ (next (37 : Fin 88) = j ∨ next j = (37 : Fin 88))
 decide
theorem row_38 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (38 : Fin 88) j ↔
 (38 : Fin 88) ≠ j ∧ (next (38 : Fin 88) = j ∨ next j = (38 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((38 : Fin 88) ≠ j ∧ ((38,j.val) ∈ edges (nanostar 4) ∨ (j.val,38) ∈ edges (nanostar 4))) ↔
   (38 : Fin 88) ≠ j ∧ (next (38 : Fin 88) = j ∨ next j = (38 : Fin 88))
 decide
theorem row_39 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (39 : Fin 88) j ↔
 (39 : Fin 88) ≠ j ∧ (next (39 : Fin 88) = j ∨ next j = (39 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((39 : Fin 88) ≠ j ∧ ((39,j.val) ∈ edges (nanostar 4) ∨ (j.val,39) ∈ edges (nanostar 4))) ↔
   (39 : Fin 88) ≠ j ∧ (next (39 : Fin 88) = j ∨ next j = (39 : Fin 88))
 decide
theorem row_40 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (40 : Fin 88) j ↔
 (40 : Fin 88) ≠ j ∧ (next (40 : Fin 88) = j ∨ next j = (40 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((40 : Fin 88) ≠ j ∧ ((40,j.val) ∈ edges (nanostar 4) ∨ (j.val,40) ∈ edges (nanostar 4))) ↔
   (40 : Fin 88) ≠ j ∧ (next (40 : Fin 88) = j ∨ next j = (40 : Fin 88))
 decide
theorem row_41 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (41 : Fin 88) j ↔
 (41 : Fin 88) ≠ j ∧ (next (41 : Fin 88) = j ∨ next j = (41 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((41 : Fin 88) ≠ j ∧ ((41,j.val) ∈ edges (nanostar 4) ∨ (j.val,41) ∈ edges (nanostar 4))) ↔
   (41 : Fin 88) ≠ j ∧ (next (41 : Fin 88) = j ∨ next j = (41 : Fin 88))
 decide
theorem row_42 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (42 : Fin 88) j ↔
 (42 : Fin 88) ≠ j ∧ (next (42 : Fin 88) = j ∨ next j = (42 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((42 : Fin 88) ≠ j ∧ ((42,j.val) ∈ edges (nanostar 4) ∨ (j.val,42) ∈ edges (nanostar 4))) ↔
   (42 : Fin 88) ≠ j ∧ (next (42 : Fin 88) = j ∨ next j = (42 : Fin 88))
 decide
theorem row_43 : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj (43 : Fin 88) j ↔
 (43 : Fin 88) ≠ j ∧ (next (43 : Fin 88) = j ∨ next j = (43 : Fin 88)) := by
 change ∀ j : Fin 88,
   ((43 : Fin 88) ≠ j ∧ ((43,j.val) ∈ edges (nanostar 4) ∨ (j.val,43) ∈ edges (nanostar 4))) ↔
   (43 : Fin 88) ≠ j ∧ (next (43 : Fin 88) = j ∨ next j = (43 : Fin 88))
 decide
end R162
