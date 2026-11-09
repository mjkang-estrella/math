module
public import GridFinal2
public import Mathlib.Data.Fin.VecNotation
@[expose] public section
namespace Grid343536
def codes4 : Fin 15 → Fin 4 → ℕ := ![
![0, 0, 0, 0],
![0, 0, 0, 1],
![0, 0, 1, 0],
![0, 0, 1, 1],
![0, 0, 1, 2],
![0, 1, 0, 0],
![0, 1, 0, 1],
![0, 1, 0, 2],
![0, 1, 1, 0],
![0, 1, 1, 1],
![0, 1, 1, 2],
![0, 1, 2, 0],
![0, 1, 2, 1],
![0, 1, 2, 2],
![0, 1, 2, 3]]
theorem setoid4_complete (r : Setoid (Fin 4)) :
    ∃ i : Fin 15, r = Setoid.ker (codes4 i) := by
  classical
  by_cases h01 : r 0 1
  ·
    by_cases h02 : r 0 2
    ·
      by_cases h03 : r 0 3
      ·
        by_cases h12 : r 1 2
        ·
          by_cases h13 : r 1 3
          ·
            by_cases h23 : r 2 3
            ·
              refine ⟨0, ?_⟩
              ext u v
              fin_cases u <;> fin_cases v
              · exact iff_of_true (r.refl 0) rfl
              · exact iff_of_true h01 rfl
              · exact iff_of_true h02 rfl
              · exact iff_of_true h03 rfl
              · exact iff_of_true (r.symm h01) rfl
              · exact iff_of_true (r.refl 1) rfl
              · exact iff_of_true h12 rfl
              · exact iff_of_true h13 rfl
              · exact iff_of_true (r.symm h02) rfl
              · exact iff_of_true (r.symm h12) rfl
              · exact iff_of_true (r.refl 2) rfl
              · exact iff_of_true h23 rfl
              · exact iff_of_true (r.symm h03) rfl
              · exact iff_of_true (r.symm h13) rfl
              · exact iff_of_true (r.symm h23) rfl
              · exact iff_of_true (r.refl 3) rfl
            ·
              exact False.elim (h23 (r.trans (r.symm h02) h03))
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h13 (r.trans (r.symm h01) h03))
            ·
              exact False.elim (h13 (r.trans (r.symm h01) h03))
        ·
          by_cases h13 : r 1 3
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h12 (r.trans (r.symm h01) h02))
            ·
              exact False.elim (h12 (r.trans (r.symm h01) h02))
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h12 (r.trans (r.symm h01) h02))
            ·
              exact False.elim (h12 (r.trans (r.symm h01) h02))
      ·
        by_cases h12 : r 1 2
        ·
          by_cases h13 : r 1 3
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h03 (r.trans h01 h13))
            ·
              exact False.elim (h03 (r.trans h01 h13))
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h03 (r.trans h02 h23))
            ·
              refine ⟨1, ?_⟩
              ext u v
              fin_cases u <;> fin_cases v
              · exact iff_of_true (r.refl 0) rfl
              · exact iff_of_true h01 rfl
              · exact iff_of_true h02 rfl
              · exact iff_of_false h03 (by change ¬ (codes4 1 0 = codes4 1 3); decide)
              · exact iff_of_true (r.symm h01) rfl
              · exact iff_of_true (r.refl 1) rfl
              · exact iff_of_true h12 rfl
              · exact iff_of_false h13 (by change ¬ (codes4 1 1 = codes4 1 3); decide)
              · exact iff_of_true (r.symm h02) rfl
              · exact iff_of_true (r.symm h12) rfl
              · exact iff_of_true (r.refl 2) rfl
              · exact iff_of_false h23 (by change ¬ (codes4 1 2 = codes4 1 3); decide)
              · exact iff_of_false (fun h => h03 (r.symm h)) (by change ¬ (codes4 1 3 = codes4 1 0); decide)
              · exact iff_of_false (fun h => h13 (r.symm h)) (by change ¬ (codes4 1 3 = codes4 1 1); decide)
              · exact iff_of_false (fun h => h23 (r.symm h)) (by change ¬ (codes4 1 3 = codes4 1 2); decide)
              · exact iff_of_true (r.refl 3) rfl
        ·
          by_cases h13 : r 1 3
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h03 (r.trans h01 h13))
            ·
              exact False.elim (h03 (r.trans h01 h13))
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h03 (r.trans h02 h23))
            ·
              exact False.elim (h12 (r.trans (r.symm h01) h02))
    ·
      by_cases h03 : r 0 3
      ·
        by_cases h12 : r 1 2
        ·
          by_cases h13 : r 1 3
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h02 (r.trans h01 h12))
            ·
              exact False.elim (h02 (r.trans h01 h12))
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h02 (r.trans h01 h12))
            ·
              exact False.elim (h02 (r.trans h01 h12))
        ·
          by_cases h13 : r 1 3
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h02 (r.trans h03 (r.symm h23)))
            ·
              refine ⟨2, ?_⟩
              ext u v
              fin_cases u <;> fin_cases v
              · exact iff_of_true (r.refl 0) rfl
              · exact iff_of_true h01 rfl
              · exact iff_of_false h02 (by change ¬ (codes4 2 0 = codes4 2 2); decide)
              · exact iff_of_true h03 rfl
              · exact iff_of_true (r.symm h01) rfl
              · exact iff_of_true (r.refl 1) rfl
              · exact iff_of_false h12 (by change ¬ (codes4 2 1 = codes4 2 2); decide)
              · exact iff_of_true h13 rfl
              · exact iff_of_false (fun h => h02 (r.symm h)) (by change ¬ (codes4 2 2 = codes4 2 0); decide)
              · exact iff_of_false (fun h => h12 (r.symm h)) (by change ¬ (codes4 2 2 = codes4 2 1); decide)
              · exact iff_of_true (r.refl 2) rfl
              · exact iff_of_false h23 (by change ¬ (codes4 2 2 = codes4 2 3); decide)
              · exact iff_of_true (r.symm h03) rfl
              · exact iff_of_true (r.symm h13) rfl
              · exact iff_of_false (fun h => h23 (r.symm h)) (by change ¬ (codes4 2 3 = codes4 2 2); decide)
              · exact iff_of_true (r.refl 3) rfl
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h02 (r.trans h03 (r.symm h23)))
            ·
              exact False.elim (h13 (r.trans (r.symm h01) h03))
      ·
        by_cases h12 : r 1 2
        ·
          by_cases h13 : r 1 3
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h02 (r.trans h01 h12))
            ·
              exact False.elim (h02 (r.trans h01 h12))
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h02 (r.trans h01 h12))
            ·
              exact False.elim (h02 (r.trans h01 h12))
        ·
          by_cases h13 : r 1 3
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h03 (r.trans h01 h13))
            ·
              exact False.elim (h03 (r.trans h01 h13))
          ·
            by_cases h23 : r 2 3
            ·
              refine ⟨3, ?_⟩
              ext u v
              fin_cases u <;> fin_cases v
              · exact iff_of_true (r.refl 0) rfl
              · exact iff_of_true h01 rfl
              · exact iff_of_false h02 (by change ¬ (codes4 3 0 = codes4 3 2); decide)
              · exact iff_of_false h03 (by change ¬ (codes4 3 0 = codes4 3 3); decide)
              · exact iff_of_true (r.symm h01) rfl
              · exact iff_of_true (r.refl 1) rfl
              · exact iff_of_false h12 (by change ¬ (codes4 3 1 = codes4 3 2); decide)
              · exact iff_of_false h13 (by change ¬ (codes4 3 1 = codes4 3 3); decide)
              · exact iff_of_false (fun h => h02 (r.symm h)) (by change ¬ (codes4 3 2 = codes4 3 0); decide)
              · exact iff_of_false (fun h => h12 (r.symm h)) (by change ¬ (codes4 3 2 = codes4 3 1); decide)
              · exact iff_of_true (r.refl 2) rfl
              · exact iff_of_true h23 rfl
              · exact iff_of_false (fun h => h03 (r.symm h)) (by change ¬ (codes4 3 3 = codes4 3 0); decide)
              · exact iff_of_false (fun h => h13 (r.symm h)) (by change ¬ (codes4 3 3 = codes4 3 1); decide)
              · exact iff_of_true (r.symm h23) rfl
              · exact iff_of_true (r.refl 3) rfl
            ·
              refine ⟨4, ?_⟩
              ext u v
              fin_cases u <;> fin_cases v
              · exact iff_of_true (r.refl 0) rfl
              · exact iff_of_true h01 rfl
              · exact iff_of_false h02 (by change ¬ (codes4 4 0 = codes4 4 2); decide)
              · exact iff_of_false h03 (by change ¬ (codes4 4 0 = codes4 4 3); decide)
              · exact iff_of_true (r.symm h01) rfl
              · exact iff_of_true (r.refl 1) rfl
              · exact iff_of_false h12 (by change ¬ (codes4 4 1 = codes4 4 2); decide)
              · exact iff_of_false h13 (by change ¬ (codes4 4 1 = codes4 4 3); decide)
              · exact iff_of_false (fun h => h02 (r.symm h)) (by change ¬ (codes4 4 2 = codes4 4 0); decide)
              · exact iff_of_false (fun h => h12 (r.symm h)) (by change ¬ (codes4 4 2 = codes4 4 1); decide)
              · exact iff_of_true (r.refl 2) rfl
              · exact iff_of_false h23 (by change ¬ (codes4 4 2 = codes4 4 3); decide)
              · exact iff_of_false (fun h => h03 (r.symm h)) (by change ¬ (codes4 4 3 = codes4 4 0); decide)
              · exact iff_of_false (fun h => h13 (r.symm h)) (by change ¬ (codes4 4 3 = codes4 4 1); decide)
              · exact iff_of_false (fun h => h23 (r.symm h)) (by change ¬ (codes4 4 3 = codes4 4 2); decide)
              · exact iff_of_true (r.refl 3) rfl
  ·
    by_cases h02 : r 0 2
    ·
      by_cases h03 : r 0 3
      ·
        by_cases h12 : r 1 2
        ·
          by_cases h13 : r 1 3
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h01 (r.trans h02 (r.symm h12)))
            ·
              exact False.elim (h01 (r.trans h02 (r.symm h12)))
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h01 (r.trans h02 (r.symm h12)))
            ·
              exact False.elim (h01 (r.trans h02 (r.symm h12)))
        ·
          by_cases h13 : r 1 3
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h01 (r.trans h03 (r.symm h13)))
            ·
              exact False.elim (h01 (r.trans h03 (r.symm h13)))
          ·
            by_cases h23 : r 2 3
            ·
              refine ⟨5, ?_⟩
              ext u v
              fin_cases u <;> fin_cases v
              · exact iff_of_true (r.refl 0) rfl
              · exact iff_of_false h01 (by change ¬ (codes4 5 0 = codes4 5 1); decide)
              · exact iff_of_true h02 rfl
              · exact iff_of_true h03 rfl
              · exact iff_of_false (fun h => h01 (r.symm h)) (by change ¬ (codes4 5 1 = codes4 5 0); decide)
              · exact iff_of_true (r.refl 1) rfl
              · exact iff_of_false h12 (by change ¬ (codes4 5 1 = codes4 5 2); decide)
              · exact iff_of_false h13 (by change ¬ (codes4 5 1 = codes4 5 3); decide)
              · exact iff_of_true (r.symm h02) rfl
              · exact iff_of_false (fun h => h12 (r.symm h)) (by change ¬ (codes4 5 2 = codes4 5 1); decide)
              · exact iff_of_true (r.refl 2) rfl
              · exact iff_of_true h23 rfl
              · exact iff_of_true (r.symm h03) rfl
              · exact iff_of_false (fun h => h13 (r.symm h)) (by change ¬ (codes4 5 3 = codes4 5 1); decide)
              · exact iff_of_true (r.symm h23) rfl
              · exact iff_of_true (r.refl 3) rfl
            ·
              exact False.elim (h23 (r.trans (r.symm h02) h03))
      ·
        by_cases h12 : r 1 2
        ·
          by_cases h13 : r 1 3
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h01 (r.trans h02 (r.symm h12)))
            ·
              exact False.elim (h01 (r.trans h02 (r.symm h12)))
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h01 (r.trans h02 (r.symm h12)))
            ·
              exact False.elim (h01 (r.trans h02 (r.symm h12)))
        ·
          by_cases h13 : r 1 3
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h03 (r.trans h02 h23))
            ·
              refine ⟨6, ?_⟩
              ext u v
              fin_cases u <;> fin_cases v
              · exact iff_of_true (r.refl 0) rfl
              · exact iff_of_false h01 (by change ¬ (codes4 6 0 = codes4 6 1); decide)
              · exact iff_of_true h02 rfl
              · exact iff_of_false h03 (by change ¬ (codes4 6 0 = codes4 6 3); decide)
              · exact iff_of_false (fun h => h01 (r.symm h)) (by change ¬ (codes4 6 1 = codes4 6 0); decide)
              · exact iff_of_true (r.refl 1) rfl
              · exact iff_of_false h12 (by change ¬ (codes4 6 1 = codes4 6 2); decide)
              · exact iff_of_true h13 rfl
              · exact iff_of_true (r.symm h02) rfl
              · exact iff_of_false (fun h => h12 (r.symm h)) (by change ¬ (codes4 6 2 = codes4 6 1); decide)
              · exact iff_of_true (r.refl 2) rfl
              · exact iff_of_false h23 (by change ¬ (codes4 6 2 = codes4 6 3); decide)
              · exact iff_of_false (fun h => h03 (r.symm h)) (by change ¬ (codes4 6 3 = codes4 6 0); decide)
              · exact iff_of_true (r.symm h13) rfl
              · exact iff_of_false (fun h => h23 (r.symm h)) (by change ¬ (codes4 6 3 = codes4 6 2); decide)
              · exact iff_of_true (r.refl 3) rfl
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h03 (r.trans h02 h23))
            ·
              refine ⟨7, ?_⟩
              ext u v
              fin_cases u <;> fin_cases v
              · exact iff_of_true (r.refl 0) rfl
              · exact iff_of_false h01 (by change ¬ (codes4 7 0 = codes4 7 1); decide)
              · exact iff_of_true h02 rfl
              · exact iff_of_false h03 (by change ¬ (codes4 7 0 = codes4 7 3); decide)
              · exact iff_of_false (fun h => h01 (r.symm h)) (by change ¬ (codes4 7 1 = codes4 7 0); decide)
              · exact iff_of_true (r.refl 1) rfl
              · exact iff_of_false h12 (by change ¬ (codes4 7 1 = codes4 7 2); decide)
              · exact iff_of_false h13 (by change ¬ (codes4 7 1 = codes4 7 3); decide)
              · exact iff_of_true (r.symm h02) rfl
              · exact iff_of_false (fun h => h12 (r.symm h)) (by change ¬ (codes4 7 2 = codes4 7 1); decide)
              · exact iff_of_true (r.refl 2) rfl
              · exact iff_of_false h23 (by change ¬ (codes4 7 2 = codes4 7 3); decide)
              · exact iff_of_false (fun h => h03 (r.symm h)) (by change ¬ (codes4 7 3 = codes4 7 0); decide)
              · exact iff_of_false (fun h => h13 (r.symm h)) (by change ¬ (codes4 7 3 = codes4 7 1); decide)
              · exact iff_of_false (fun h => h23 (r.symm h)) (by change ¬ (codes4 7 3 = codes4 7 2); decide)
              · exact iff_of_true (r.refl 3) rfl
    ·
      by_cases h03 : r 0 3
      ·
        by_cases h12 : r 1 2
        ·
          by_cases h13 : r 1 3
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h01 (r.trans h03 (r.symm h13)))
            ·
              exact False.elim (h01 (r.trans h03 (r.symm h13)))
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h02 (r.trans h03 (r.symm h23)))
            ·
              refine ⟨8, ?_⟩
              ext u v
              fin_cases u <;> fin_cases v
              · exact iff_of_true (r.refl 0) rfl
              · exact iff_of_false h01 (by change ¬ (codes4 8 0 = codes4 8 1); decide)
              · exact iff_of_false h02 (by change ¬ (codes4 8 0 = codes4 8 2); decide)
              · exact iff_of_true h03 rfl
              · exact iff_of_false (fun h => h01 (r.symm h)) (by change ¬ (codes4 8 1 = codes4 8 0); decide)
              · exact iff_of_true (r.refl 1) rfl
              · exact iff_of_true h12 rfl
              · exact iff_of_false h13 (by change ¬ (codes4 8 1 = codes4 8 3); decide)
              · exact iff_of_false (fun h => h02 (r.symm h)) (by change ¬ (codes4 8 2 = codes4 8 0); decide)
              · exact iff_of_true (r.symm h12) rfl
              · exact iff_of_true (r.refl 2) rfl
              · exact iff_of_false h23 (by change ¬ (codes4 8 2 = codes4 8 3); decide)
              · exact iff_of_true (r.symm h03) rfl
              · exact iff_of_false (fun h => h13 (r.symm h)) (by change ¬ (codes4 8 3 = codes4 8 1); decide)
              · exact iff_of_false (fun h => h23 (r.symm h)) (by change ¬ (codes4 8 3 = codes4 8 2); decide)
              · exact iff_of_true (r.refl 3) rfl
        ·
          by_cases h13 : r 1 3
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h01 (r.trans h03 (r.symm h13)))
            ·
              exact False.elim (h01 (r.trans h03 (r.symm h13)))
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h02 (r.trans h03 (r.symm h23)))
            ·
              refine ⟨11, ?_⟩
              ext u v
              fin_cases u <;> fin_cases v
              · exact iff_of_true (r.refl 0) rfl
              · exact iff_of_false h01 (by change ¬ (codes4 11 0 = codes4 11 1); decide)
              · exact iff_of_false h02 (by change ¬ (codes4 11 0 = codes4 11 2); decide)
              · exact iff_of_true h03 rfl
              · exact iff_of_false (fun h => h01 (r.symm h)) (by change ¬ (codes4 11 1 = codes4 11 0); decide)
              · exact iff_of_true (r.refl 1) rfl
              · exact iff_of_false h12 (by change ¬ (codes4 11 1 = codes4 11 2); decide)
              · exact iff_of_false h13 (by change ¬ (codes4 11 1 = codes4 11 3); decide)
              · exact iff_of_false (fun h => h02 (r.symm h)) (by change ¬ (codes4 11 2 = codes4 11 0); decide)
              · exact iff_of_false (fun h => h12 (r.symm h)) (by change ¬ (codes4 11 2 = codes4 11 1); decide)
              · exact iff_of_true (r.refl 2) rfl
              · exact iff_of_false h23 (by change ¬ (codes4 11 2 = codes4 11 3); decide)
              · exact iff_of_true (r.symm h03) rfl
              · exact iff_of_false (fun h => h13 (r.symm h)) (by change ¬ (codes4 11 3 = codes4 11 1); decide)
              · exact iff_of_false (fun h => h23 (r.symm h)) (by change ¬ (codes4 11 3 = codes4 11 2); decide)
              · exact iff_of_true (r.refl 3) rfl
      ·
        by_cases h12 : r 1 2
        ·
          by_cases h13 : r 1 3
          ·
            by_cases h23 : r 2 3
            ·
              refine ⟨9, ?_⟩
              ext u v
              fin_cases u <;> fin_cases v
              · exact iff_of_true (r.refl 0) rfl
              · exact iff_of_false h01 (by change ¬ (codes4 9 0 = codes4 9 1); decide)
              · exact iff_of_false h02 (by change ¬ (codes4 9 0 = codes4 9 2); decide)
              · exact iff_of_false h03 (by change ¬ (codes4 9 0 = codes4 9 3); decide)
              · exact iff_of_false (fun h => h01 (r.symm h)) (by change ¬ (codes4 9 1 = codes4 9 0); decide)
              · exact iff_of_true (r.refl 1) rfl
              · exact iff_of_true h12 rfl
              · exact iff_of_true h13 rfl
              · exact iff_of_false (fun h => h02 (r.symm h)) (by change ¬ (codes4 9 2 = codes4 9 0); decide)
              · exact iff_of_true (r.symm h12) rfl
              · exact iff_of_true (r.refl 2) rfl
              · exact iff_of_true h23 rfl
              · exact iff_of_false (fun h => h03 (r.symm h)) (by change ¬ (codes4 9 3 = codes4 9 0); decide)
              · exact iff_of_true (r.symm h13) rfl
              · exact iff_of_true (r.symm h23) rfl
              · exact iff_of_true (r.refl 3) rfl
            ·
              exact False.elim (h23 (r.trans (r.symm h12) h13))
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h13 (r.trans h12 h23))
            ·
              refine ⟨10, ?_⟩
              ext u v
              fin_cases u <;> fin_cases v
              · exact iff_of_true (r.refl 0) rfl
              · exact iff_of_false h01 (by change ¬ (codes4 10 0 = codes4 10 1); decide)
              · exact iff_of_false h02 (by change ¬ (codes4 10 0 = codes4 10 2); decide)
              · exact iff_of_false h03 (by change ¬ (codes4 10 0 = codes4 10 3); decide)
              · exact iff_of_false (fun h => h01 (r.symm h)) (by change ¬ (codes4 10 1 = codes4 10 0); decide)
              · exact iff_of_true (r.refl 1) rfl
              · exact iff_of_true h12 rfl
              · exact iff_of_false h13 (by change ¬ (codes4 10 1 = codes4 10 3); decide)
              · exact iff_of_false (fun h => h02 (r.symm h)) (by change ¬ (codes4 10 2 = codes4 10 0); decide)
              · exact iff_of_true (r.symm h12) rfl
              · exact iff_of_true (r.refl 2) rfl
              · exact iff_of_false h23 (by change ¬ (codes4 10 2 = codes4 10 3); decide)
              · exact iff_of_false (fun h => h03 (r.symm h)) (by change ¬ (codes4 10 3 = codes4 10 0); decide)
              · exact iff_of_false (fun h => h13 (r.symm h)) (by change ¬ (codes4 10 3 = codes4 10 1); decide)
              · exact iff_of_false (fun h => h23 (r.symm h)) (by change ¬ (codes4 10 3 = codes4 10 2); decide)
              · exact iff_of_true (r.refl 3) rfl
        ·
          by_cases h13 : r 1 3
          ·
            by_cases h23 : r 2 3
            ·
              exact False.elim (h12 (r.trans h13 (r.symm h23)))
            ·
              refine ⟨12, ?_⟩
              ext u v
              fin_cases u <;> fin_cases v
              · exact iff_of_true (r.refl 0) rfl
              · exact iff_of_false h01 (by change ¬ (codes4 12 0 = codes4 12 1); decide)
              · exact iff_of_false h02 (by change ¬ (codes4 12 0 = codes4 12 2); decide)
              · exact iff_of_false h03 (by change ¬ (codes4 12 0 = codes4 12 3); decide)
              · exact iff_of_false (fun h => h01 (r.symm h)) (by change ¬ (codes4 12 1 = codes4 12 0); decide)
              · exact iff_of_true (r.refl 1) rfl
              · exact iff_of_false h12 (by change ¬ (codes4 12 1 = codes4 12 2); decide)
              · exact iff_of_true h13 rfl
              · exact iff_of_false (fun h => h02 (r.symm h)) (by change ¬ (codes4 12 2 = codes4 12 0); decide)
              · exact iff_of_false (fun h => h12 (r.symm h)) (by change ¬ (codes4 12 2 = codes4 12 1); decide)
              · exact iff_of_true (r.refl 2) rfl
              · exact iff_of_false h23 (by change ¬ (codes4 12 2 = codes4 12 3); decide)
              · exact iff_of_false (fun h => h03 (r.symm h)) (by change ¬ (codes4 12 3 = codes4 12 0); decide)
              · exact iff_of_true (r.symm h13) rfl
              · exact iff_of_false (fun h => h23 (r.symm h)) (by change ¬ (codes4 12 3 = codes4 12 2); decide)
              · exact iff_of_true (r.refl 3) rfl
          ·
            by_cases h23 : r 2 3
            ·
              refine ⟨13, ?_⟩
              ext u v
              fin_cases u <;> fin_cases v
              · exact iff_of_true (r.refl 0) rfl
              · exact iff_of_false h01 (by change ¬ (codes4 13 0 = codes4 13 1); decide)
              · exact iff_of_false h02 (by change ¬ (codes4 13 0 = codes4 13 2); decide)
              · exact iff_of_false h03 (by change ¬ (codes4 13 0 = codes4 13 3); decide)
              · exact iff_of_false (fun h => h01 (r.symm h)) (by change ¬ (codes4 13 1 = codes4 13 0); decide)
              · exact iff_of_true (r.refl 1) rfl
              · exact iff_of_false h12 (by change ¬ (codes4 13 1 = codes4 13 2); decide)
              · exact iff_of_false h13 (by change ¬ (codes4 13 1 = codes4 13 3); decide)
              · exact iff_of_false (fun h => h02 (r.symm h)) (by change ¬ (codes4 13 2 = codes4 13 0); decide)
              · exact iff_of_false (fun h => h12 (r.symm h)) (by change ¬ (codes4 13 2 = codes4 13 1); decide)
              · exact iff_of_true (r.refl 2) rfl
              · exact iff_of_true h23 rfl
              · exact iff_of_false (fun h => h03 (r.symm h)) (by change ¬ (codes4 13 3 = codes4 13 0); decide)
              · exact iff_of_false (fun h => h13 (r.symm h)) (by change ¬ (codes4 13 3 = codes4 13 1); decide)
              · exact iff_of_true (r.symm h23) rfl
              · exact iff_of_true (r.refl 3) rfl
            ·
              refine ⟨14, ?_⟩
              ext u v
              fin_cases u <;> fin_cases v
              · exact iff_of_true (r.refl 0) rfl
              · exact iff_of_false h01 (by change ¬ (codes4 14 0 = codes4 14 1); decide)
              · exact iff_of_false h02 (by change ¬ (codes4 14 0 = codes4 14 2); decide)
              · exact iff_of_false h03 (by change ¬ (codes4 14 0 = codes4 14 3); decide)
              · exact iff_of_false (fun h => h01 (r.symm h)) (by change ¬ (codes4 14 1 = codes4 14 0); decide)
              · exact iff_of_true (r.refl 1) rfl
              · exact iff_of_false h12 (by change ¬ (codes4 14 1 = codes4 14 2); decide)
              · exact iff_of_false h13 (by change ¬ (codes4 14 1 = codes4 14 3); decide)
              · exact iff_of_false (fun h => h02 (r.symm h)) (by change ¬ (codes4 14 2 = codes4 14 0); decide)
              · exact iff_of_false (fun h => h12 (r.symm h)) (by change ¬ (codes4 14 2 = codes4 14 1); decide)
              · exact iff_of_true (r.refl 2) rfl
              · exact iff_of_false h23 (by change ¬ (codes4 14 2 = codes4 14 3); decide)
              · exact iff_of_false (fun h => h03 (r.symm h)) (by change ¬ (codes4 14 3 = codes4 14 0); decide)
              · exact iff_of_false (fun h => h13 (r.symm h)) (by change ¬ (codes4 14 3 = codes4 14 1); decide)
              · exact iff_of_false (fun h => h23 (r.symm h)) (by change ¬ (codes4 14 3 = codes4 14 2); decide)
              · exact iff_of_true (r.refl 3) rfl
end Grid343536
