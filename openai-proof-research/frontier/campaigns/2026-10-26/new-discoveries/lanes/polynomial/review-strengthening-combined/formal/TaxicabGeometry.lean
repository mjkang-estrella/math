import Mathlib

namespace TaxicabGeometry
noncomputable section

abbrev Point := ℝ × ℝ

/-- Explicit L1 size; no use is made of the default maximum norm on products. -/
def norm1 (p : Point) : ℝ := |p.1| + |p.2|

def dist1 (P Q : Point) : ℝ := |P.1-Q.1| + |P.2-Q.2|

def lineValue (a b c : ℝ) (P : Point) : ℝ := a*P.1+b*P.2+c

def lineScale (a b : ℝ) : ℝ := max |a| |b|

/-- The source's explicit point-to-line taxicab distance, equation (5). -/
def lineDistance (a b c : ℝ) (P : Point) : ℝ := |lineValue a b c P| / lineScale a b

theorem dist1_comm (P Q : Point) : dist1 P Q = dist1 Q P := by
  simp only [dist1, abs_sub_comm]

theorem dist1_eq_norm1_sub (P Q : Point) : dist1 P Q = norm1 (Q-P) := by
  change |P.1-Q.1| + |P.2-Q.2| = |Q.1-P.1| + |Q.2-P.2|
  simp only [abs_sub_comm]

theorem norm1_nonneg (P : Point) : 0 ≤ norm1 P := add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem norm1_eq_zero_iff (P : Point) : norm1 P = 0 ↔ P = 0 := by
  rw [norm1, add_eq_zero_iff_of_nonneg (abs_nonneg _) (abs_nonneg _)]
  simp only [abs_eq_zero]
  constructor
  · rintro ⟨h1,h2⟩
    exact Prod.ext h1 h2
  · intro h
    subst P
    exact ⟨rfl,rfl⟩

theorem lineScale_pos (a b : ℝ) (h : a ≠ 0 ∨ b ≠ 0) : 0 < lineScale a b := by
  rcases h with h | h
  · exact (abs_pos.mpr h).trans_le (le_max_left _ _)
  · exact (abs_pos.mpr h).trans_le (le_max_right _ _)

/-- The dual L-infinity/L1 inequality, proved directly in coordinates. -/
theorem abs_linear_bound (a b x y : ℝ) :
    |a*x+b*y| ≤ lineScale a b * (|x|+|y|) := by
  calc
    |a*x+b*y| ≤ |a*x|+|b*y| := abs_add_le _ _
    _ = |a| * |x|+|b| * |y| := by rw [abs_mul,abs_mul]
    _ ≤ max |a| |b| * |x| + max |a| |b| * |y| :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
    _ = lineScale a b * (|x|+|y|) := by unfold lineScale; ring

theorem line_difference_bound (a b c : ℝ) (P Q : Point) :
    |lineValue a b c P-lineValue a b c Q| ≤ lineScale a b * dist1 P Q := by
  calc
    |lineValue a b c P-lineValue a b c Q| = |a*(P.1-Q.1)+b*(P.2-Q.2)| := by
      congr 1
      unfold lineValue
      ring
    _ ≤ lineScale a b * dist1 P Q := abs_linear_bound _ _ _ _

theorem lineDistance_nonneg (a b c : ℝ) (P : Point) : 0 ≤ lineDistance a b c P := by
  exact div_nonneg (abs_nonneg _) ((abs_nonneg a).trans (le_max_left _ _))

/-- Any point of the line gives an upper bound for the source distance. -/
theorem lineDistance_le_dist1 (a b c : ℝ) (P Q : Point)
    (hab : a ≠ 0 ∨ b ≠ 0) (hQ : lineValue a b c Q = 0) :
    lineDistance a b c P ≤ dist1 P Q := by
  apply (div_le_iff₀ (lineScale_pos a b hab)).mpr
  have h := line_difference_bound a b c P Q
  rw [hQ, sub_zero] at h
  simpa only [mul_comm] using h

/-- Coordinate form of an affine barycentric identity. -/
theorem barycentric_line_value (a b c la lb lc : ℝ) (A B C P : Point)
    (hsum : la+lb+lc = 1) (hP : P = la • A + lb • B + lc • C) :
    la*lineValue a b c A + lb*lineValue a b c B + lc*lineValue a b c C =
      lineValue a b c P := by
  have hx := congrArg Prod.fst hP
  have hy := congrArg Prod.snd hP
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at hx
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hy
  calc
    la*lineValue a b c A + lb*lineValue a b c B + lc*lineValue a b c C =
        a*(la*A.1+lb*B.1+lc*C.1) + b*(la*A.2+lb*B.2+lc*C.2) + c*(la+lb+lc) := by
      unfold lineValue
      ring
    _ = lineValue a b c P := by rw [← hx,← hy,hsum]; unfold lineValue; ring

/-- Weighted opposite-side bound without division by a barycentric coordinate. -/
theorem weighted_lineDistance_bound (a b c la lb lc : ℝ) (A B C P : Point)
    (hab : a ≠ 0 ∨ b ≠ 0) (hB : lineValue a b c B = 0) (hC : lineValue a b c C = 0)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hlc : 0 ≤ lc)
    (hsum : la+lb+lc = 1) (hP : P = la • A + lb • B + lc • C) :
    (1-la)*lineDistance a b c P ≤ la*dist1 P A := by
  have hv := barycentric_line_value a b c la lb lc A B C P hsum hP
  rw [hB,hC,mul_zero,mul_zero,add_zero,add_zero] at hv
  have hla1 : 0 ≤ 1-la := by linarith
  have he : (1-la)*lineValue a b c P = la*(lineValue a b c A-lineValue a b c P) := by
    rw [← hv]
    ring
  have heabs := congrArg abs he
  rw [abs_mul,abs_of_nonneg hla1,abs_mul,abs_of_nonneg hla] at heabs
  unfold lineDistance
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (lineScale_pos a b hab)).mpr
  calc
    (1-la) * |lineValue a b c P| = la * |lineValue a b c A-lineValue a b c P| := heabs
    _ ≤ la*(lineScale a b * dist1 A P) :=
      mul_le_mul_of_nonneg_left (line_difference_bound a b c A P) hla
    _ = (la*dist1 P A)*lineScale a b := by rw [dist1_comm A P]; ring

/-- Coefficients of the supporting line through B and C, in inherited coordinates. -/
def sideDistance (P B C : Point) : ℝ :=
  lineDistance (B.2-C.2) (C.1-B.1) (B.1*C.2-C.1*B.2) P

theorem side_coefficients_nonzero (B C : Point) (h : B ≠ C) :
    B.2-C.2 ≠ 0 ∨ C.1-B.1 ≠ 0 := by
  by_contra hn
  simp only [not_or,not_not] at hn
  apply h
  apply Prod.ext <;> linarith [hn.1,hn.2]

theorem side_line_left (B C : Point) :
    lineValue (B.2-C.2) (C.1-B.1) (B.1*C.2-C.1*B.2) B = 0 := by
  unfold lineValue
  ring

theorem side_line_right (B C : Point) :
    lineValue (B.2-C.2) (C.1-B.1) (B.1*C.2-C.1*B.2) C = 0 := by
  unfold lineValue
  ring

/-- Exactly the three scalar inequalities needed for the side opposite A. -/
theorem opposite_side_bounds (la lb lc : ℝ) (A B C P : Point) (hBC : B ≠ C)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hlc : 0 ≤ lc)
    (hsum : la+lb+lc = 1) (hP : P = la • A + lb • B + lc • C) :
    0 ≤ sideDistance P B C ∧
    sideDistance P B C ≤ norm1 (B-P) ∧
    sideDistance P B C ≤ norm1 (C-P) ∧
    (1-la)*sideDistance P B C ≤ la*norm1 (A-P) := by
  have hab := side_coefficients_nonzero B C hBC
  refine ⟨lineDistance_nonneg _ _ _ _, ?_, ?_, ?_⟩
  · rw [← dist1_eq_norm1_sub]
    exact lineDistance_le_dist1 _ _ _ P B hab (side_line_left B C)
  · rw [← dist1_eq_norm1_sub]
    exact lineDistance_le_dist1 _ _ _ P C hab (side_line_right B C)
  · rw [← dist1_eq_norm1_sub]
    exact weighted_lineDistance_bound _ _ _ la lb lc A B C P hab (side_line_left B C)
      (side_line_right B C) hla hlb hlc hsum hP

/-- All cyclic source inequalities, with explicit L1 vertex sizes. -/
theorem triangle_side_bounds (la lb lc : ℝ) (A B C P : Point)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hlc : 0 ≤ lc)
    (hsum : la+lb+lc = 1) (hP : P = la • A + lb • B + lc • C) :
    0 ≤ sideDistance P B C ∧ 0 ≤ sideDistance P C A ∧ 0 ≤ sideDistance P A B ∧
    sideDistance P B C ≤ min (norm1 (B-P)) (norm1 (C-P)) ∧
    sideDistance P C A ≤ min (norm1 (A-P)) (norm1 (C-P)) ∧
    sideDistance P A B ≤ min (norm1 (A-P)) (norm1 (B-P)) ∧
    (1-la)*sideDistance P B C ≤ la*norm1 (A-P) ∧
    (1-lb)*sideDistance P C A ≤ lb*norm1 (B-P) ∧
    (1-lc)*sideDistance P A B ≤ lc*norm1 (C-P) := by
  obtain ⟨hra,haB,haC,hwa⟩ := opposite_side_bounds la lb lc A B C P hBC hla hlb hlc hsum hP
  have hPb : P = lb • B + lc • C + la • A := by rw [hP]; abel
  have hPc : P = lc • C + la • A + lb • B := by rw [hP]; abel
  obtain ⟨hrb,hbC,hbA,hwb⟩ := opposite_side_bounds lb lc la B C A P hCA hlb hlc hla (by linarith) hPb
  obtain ⟨hrc,hcA,hcB,hwc⟩ := opposite_side_bounds lc la lb C A B P hAB hlc hla hlb (by linarith) hPc
  exact ⟨hra,hrb,hrc,le_min haB haC,le_min hbA hbC,le_min hcA hcB,hwa,hwb,hwc⟩

/-- Elementary conversion from the weighted bound to the scalar ratio bound. -/
theorem ratio_le_weight (A r t : ℝ) (hA : 0 < A) (hr : 0 ≤ r)
    (h : (1-t)*r ≤ t*A) : r/(A+r) ≤ t := by
  apply (div_le_iff₀ (by linarith : 0 < A+r)).mpr
  nlinarith

/-- The sum-of-three-ratios hypothesis follows from the geometric inequalities. -/
theorem triangle_ratio_bound (la lb lc : ℝ) (A B C P : Point)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hlc : 0 ≤ lc)
    (hsum : la+lb+lc = 1) (hP : P = la • A + lb • B + lc • C)
    (hA : 0 < norm1 (A-P)) (hB : 0 < norm1 (B-P)) (hC : 0 < norm1 (C-P)) :
    sideDistance P B C / (norm1 (A-P)+sideDistance P B C) +
      sideDistance P C A / (norm1 (B-P)+sideDistance P C A) +
      sideDistance P A B / (norm1 (C-P)+sideDistance P A B) ≤ 1 := by
  obtain ⟨hra,hrb,hrc,_,_,_,hwa,hwb,hwc⟩ :=
    triangle_side_bounds la lb lc A B C P hAB hBC hCA hla hlb hlc hsum hP
  have ha := ratio_le_weight _ _ la hA hra hwa
  have hb := ratio_le_weight _ _ lb hB hrb hwb
  have hc := ratio_le_weight _ _ lc hC hrc hwc
  linarith

/-- Nonzero explicit L1 size of a nonzero vector. -/
theorem norm1_pos_of_ne_zero (V : Point) (hV : V ≠ 0) : 0 < norm1 V := by
  by_contra h
  have hz : norm1 V = 0 := by linarith [norm1_nonneg V]
  exact hV ((norm1_eq_zero_iff V).mp hz)

/-- A noncollinear vertex cannot coincide with an interior barycentric point. -/
theorem vertex_size_pos (a b c la lb lc : ℝ) (A B C P : Point)
    (hA : lineValue a b c A ≠ 0) (hB : lineValue a b c B = 0) (hC : lineValue a b c C = 0)
    (hla : la < 1) (hsum : la+lb+lc = 1) (hP : P = la • A + lb • B + lc • C) :
    0 < norm1 (A-P) := by
  have hv := barycentric_line_value a b c la lb lc A B C P hsum hP
  rw [hB,hC,mul_zero,mul_zero,add_zero,add_zero] at hv
  have hAP : A ≠ P := by
    intro he
    rw [← he] at hv
    have hz : (1-la)*lineValue a b c A = 0 := by nlinarith
    exact (mul_ne_zero (by linarith : 1-la ≠ 0) hA) hz
  exact norm1_pos_of_ne_zero (A-P) (sub_ne_zero.mpr hAP)

/-- Signed doubled affine area in the same coordinates as the side formula. -/
def area (A B C : Point) : ℝ :=
  lineValue (B.2-C.2) (C.1-B.1) (B.1*C.2-C.1*B.2) A

theorem area_cyclic (A B C : Point) : area B C A = area A B C := by
  unfold area lineValue
  ring

theorem area_distinct (A B C : Point) (h : area A B C ≠ 0) :
    A ≠ B ∧ B ≠ C ∧ C ≠ A := by
  constructor
  · intro he
    subst A
    exact h (side_line_left B C)
  constructor
  · intro he
    subst C
    apply h
    unfold area lineValue
    ring
  · intro he
    subst C
    exact h (side_line_right B A)

/-- All three strict-positive vertex sizes follow from nonzero area and positive barycentrics. -/
theorem triangle_vertex_sizes_pos (la lb lc : ℝ) (A B C P : Point)
    (harea : area A B C ≠ 0) (hla : 0 < la) (hlb : 0 < lb) (hlc : 0 < lc)
    (hsum : la+lb+lc = 1) (hP : P = la • A + lb • B + lc • C) :
    0 < norm1 (A-P) ∧ 0 < norm1 (B-P) ∧ 0 < norm1 (C-P) := by
  have hPb : P = lb • B + lc • C + la • A := by rw [hP]; abel
  have hPc : P = lc • C + la • A + lb • B := by rw [hP]; abel
  refine ⟨?_,?_,?_⟩
  · exact vertex_size_pos _ _ _ la lb lc A B C P harea
      (side_line_left B C) (side_line_right B C) (by linarith) hsum hP
  · have hb : area B C A ≠ 0 := by rw [area_cyclic]; exact harea
    exact vertex_size_pos _ _ _ lb lc la B C A P hb
      (side_line_left C A) (side_line_right C A) (by linarith) (by linarith) hPb
  · have hc : area C A B ≠ 0 := by rw [area_cyclic,area_cyclic]; exact harea
    exact vertex_size_pos _ _ _ lc la lb C A B P hc
      (side_line_left A B) (side_line_right A B) (by linarith) (by linarith) hPc

/-- Direct source-to-scalar ratio hypothesis with no vertex-size assumptions left over. -/
theorem interior_triangle_ratio_bound (la lb lc : ℝ) (A B C P : Point)
    (harea : area A B C ≠ 0) (hla : 0 < la) (hlb : 0 < lb) (hlc : 0 < lc)
    (hsum : la+lb+lc = 1) (hP : P = la • A + lb • B + lc • C) :
    sideDistance P B C / (norm1 (A-P)+sideDistance P B C) +
      sideDistance P C A / (norm1 (B-P)+sideDistance P C A) +
      sideDistance P A B / (norm1 (C-P)+sideDistance P A B) ≤ 1 := by
  obtain ⟨hAB,hBC,hCA⟩ := area_distinct A B C harea
  obtain ⟨hA,hB,hC⟩ := triangle_vertex_sizes_pos la lb lc A B C P harea hla hlb hlc hsum hP
  exact triangle_ratio_bound la lb lc A B C P hAB hBC hCA hla.le hlb.le hlc.le hsum hP hA hB hC

end
end TaxicabGeometry
