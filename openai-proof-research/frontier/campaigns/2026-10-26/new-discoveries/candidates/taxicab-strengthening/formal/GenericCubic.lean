import StrengthenedScalar

namespace StrengthenedTaxicab

theorem generic_cubic_sorted {A B C u v w : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hu : 0 ≤ u) (huv : u ≤ v) (hvw : v ≤ w)
    (hub : u ≤ B) (huc : u ≤ C) (hva : v ≤ A) (hvc : v ≤ C)
    (hwa : w ≤ A) (hwb : w ≤ B)
    (hH : 0 ≤ cubic A B C u v w) :
    3*(2*u+v+w) ≤ 2*(A+B+C) := by
  have hv : 0 ≤ v := hu.trans huv
  have hw : 0 ≤ w := hv.trans hvw
  by_contra h
  have hgt : 2*(A+B+C)<3*(2*u+v+w) := lt_of_not_ge h
  let d := (3*(2*u+v+w)-2*(A+B+C))/6
  have hd : 0<d := by dsimp [d]; linarith
  have hthreshold := threshold_sorted hu huv hvw
    (show w ≤ A+d by linarith) (show w ≤ B+d by linarith)
    (show v ≤ C+d by linarith)
    (show 2*((A+d)+(B+d)+(C+d))=3*(2*u+v+w) by dsimp [d]; ring)
  have hp1 : 0 ≤ A*B-u*v := by nlinarith [mul_le_mul hub hva hv hB]
  have hp2 : 0 ≤ A*C-u*w := by nlinarith [mul_le_mul huc hwa hw hC]
  have hp3 : 0 ≤ B*C-v*w := by nlinarith [mul_le_mul hvc hwb hw hC]
  have hcoef : 0 ≤ (A*B-u*v)+(A*C-u*w)+(B*C-v*w) := by linarith
  have hnon1 := mul_nonneg hd.le hcoef
  have hnon2 := mul_nonneg (sq_nonneg d) (add_nonneg (add_nonneg hA hB) hC)
  have hstrict := pow_pos hd 3
  rw [cubic_offset] at hthreshold
  linarith

/-- The full nonnegative cubic criterion, with all six caps and no order restriction. -/
theorem generic_cubic {A B C u v w : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hub : u ≤ B) (huc : u ≤ C) (hva : v ≤ A) (hvc : v ≤ C)
    (hwa : w ≤ A) (hwb : w ≤ B)
    (hH : 0 ≤ cubic A B C u v w) :
    3*(u+v+w+min u (min v w)) ≤ 2*(A+B+C) := by
  by_cases huv : u ≤ v
  · by_cases hvw : v ≤ w
    · have h := generic_cubic_sorted hA hB hC hu huv hvw hub huc hva hvc hwa hwb hH
      simp only [min_eq_left hvw, min_eq_left huv]
      linarith
    have hwv : w ≤ v := le_of_not_ge hvw
    by_cases huw : u ≤ w
    · have h := generic_cubic_sorted hA hC hB hu huw hwv huc hub hwa hwb hva hvc
        (by convert hH using 1; unfold cubic; ring)
      simp only [min_eq_right hwv, min_eq_left huw]
      linarith
    have hwu : w ≤ u := le_of_not_ge huw
    have h := generic_cubic_sorted hC hA hB hw hwu huv hwa hwb huc hub hvc hva
      (by convert hH using 1; unfold cubic; ring)
    simp only [min_eq_right hwv, min_eq_right hwu]
    linarith
  have hvu : v ≤ u := le_of_not_ge huv
  by_cases huw : u ≤ w
  · have h := generic_cubic_sorted hB hA hC hv hvu huw hva hvc hub huc hwb hwa
      (by convert hH using 1; unfold cubic; ring)
    simp only [min_eq_left (hvu.trans huw), min_eq_right hvu]
    linarith
  have hwu : w ≤ u := le_of_not_ge huw
  by_cases hvw : v ≤ w
  · have h := generic_cubic_sorted hB hC hA hv hvw hwu hvc hva hwb hwa hub huc
      (by convert hH using 1; unfold cubic; ring)
    simp only [min_eq_left hvw, min_eq_right hvu]
    linarith
  have hwv : w ≤ v := le_of_not_ge hvw
  have h := generic_cubic_sorted hC hB hA hw hwv hvu hwb hwa hvc hva huc hub
    (by convert hH using 1; unfold cubic; ring)
  simp only [min_eq_right hwv, min_eq_right hwu]
  linarith

end StrengthenedTaxicab
