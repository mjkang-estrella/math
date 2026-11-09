import Mathlib

namespace StrengthenedTaxicab

def cubic (A B C u v w : ℝ) : ℝ := A*B*C-A*v*w-B*u*w-C*u*v-2*u*v*w

lemma cubic_of_fraction {A B C u v w : ℝ} (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hF : u/(A+u)+v/(B+v)+w/(C+w) ≤ 1) : 0 ≤ cubic A B C u v w := by
  have hid : cubic A B C u v w =
      (1-(u/(A+u)+v/(B+v)+w/(C+w)))*((A+u)*(B+v)*(C+w)) := by
    unfold cubic
    field_simp
    ring
  rw [hid]
  exact mul_nonneg (sub_nonneg.mpr hF) (by positivity)

lemma derivative_nonpos {u y a b c : ℝ} (_hu : 0 ≤ u) (hy : 0 ≤ y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (_hc : 0 ≤ c)
    (hrel : 2*(a+b+c)+y=6*u) :
    u*(b+c-8*u-4*y)+b*(y+a)+c*(2*y+a+b)  ≤  0 := by
  let D := u*(b+c-8*u-4*y)+b*(y+a)+c*(2*y+a+b)
  have hid : 12*D = -31*u^2-(3*(b+c)-8*u)^2-(3*y-u)^2-
      12*y*b-3*(b-c)^2-18*y*a + (2*(a+b+c)+y-6*u)*(6*(b+c)+9*y) := by
    dsimp [D]
    ring
  rw [sub_eq_zero.mpr hrel, zero_mul, add_zero] at hid
  have hya := mul_nonneg hy ha
  have hyb := mul_nonneg hy hb
  change D ≤ 0
  nlinarith [sq_nonneg u, sq_nonneg (3*(b+c)-8*u), sq_nonneg (3*y-u), sq_nonneg (b-c)]

lemma reduce_equal_sides {u v y a b c : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hrel : 2*(a+b+c)+y=6*u) :
    cubic (v+y+a) (v+y+b) (v+c) u v (v+y)  ≤ 
      cubic (u+y+a) (u+y+b) (u+c) u u (u+y) := by
  let D := u*(b+c-8*u-4*y)+b*(y+a)+c*(2*y+a+b)
  have hD : D ≤ 0 := derivative_nonpos hu hy ha hb hc hrel
  have hq : b+c-4*u ≤ 0 := by linarith
  have hdiff : cubic (v+y+a) (v+y+b) (v+c) u v (v+y) -
      cubic (u+y+a) (u+y+b) (u+c) u u (u+y) =
      (v-u)*(D+(b+c-4*u)*(v-u)) := by
    dsimp [cubic,D]
    ring
  have hinner : D+(b+c-4*u)*(v-u) ≤ 0 :=
    add_nonpos hD (mul_nonpos_of_nonpos_of_nonneg hq (sub_nonneg.mpr huv))
  have hprod := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr huv) hinner
  linarith

lemma symmetrize_lengths (A B C u w : ℝ) (hC : 0 ≤ C) :
    cubic A B C u u w  ≤  cubic ((A+B)/2) ((A+B)/2) C u u w := by
  have hid : cubic ((A+B)/2) ((A+B)/2) C u u w - cubic A B C u u w =
      C*(A-B)^2/4 := by unfold cubic; ring
  have hnon := div_nonneg (mul_nonneg hC (sq_nonneg (A-B))) (by norm_num : (0:ℝ) ≤ 4)
  linarith

lemma equal_side_product_bound {u w s C : ℝ} (_hu : 0 ≤ u) (huw : u ≤ w)
    (hws : w ≤ s) (_hC : u ≤ C) (hrel : 4*s+2*C=9*u+3*w) :
    C*(s-u) ≤ 2*u*w := by
  by_cases hsmall : 3*w ≤ 8*u
  · have hfactor : 0 ≤ (w-u)*(25*u-9*w) := mul_nonneg (sub_nonneg.mpr huw) (by linarith)
    have hid : 32*(2*u*w-C*(s-u)) =
        (4*C-5*u-3*w)^2+(w-u)*(25*u-9*w) := by
      nlinarith [congrArg (fun x : ℝ => 8*C*x) hrel]
    nlinarith [sq_nonneg (4*C-5*u-3*w)]
  · have hlarge : 13*u ≤ 5*w := by linarith
    have hfactor : 0 ≤ (s-w)*(5*w-13*u) :=
      mul_nonneg (sub_nonneg.mpr hws) (sub_nonneg.mpr hlarge)
    have hid : 2*(2*u*w-C*(s-u)) =
        (w-3*u)^2+(s-w)*(5*w-13*u)+4*(s-w)^2 := by
      nlinarith [congrArg (fun x : ℝ => (s-u)*x) hrel]
    nlinarith [sq_nonneg (w-3*u), sq_nonneg (s-w)]

lemma equal_sides_threshold {u w s C : ℝ} (hu : 0 ≤ u) (huw : u ≤ w)
    (hws : w ≤ s) (hC : u ≤ C) (hrel : 4*s+2*C=9*u+3*w) :
    cubic s s C u u w ≤ 0 := by
  have hp := equal_side_product_bound hu huw hws hC hrel
  have hs : 0 ≤ s+u := by linarith
  have hid : cubic s s C u u w=(s+u)*(C*(s-u)-2*u*w) := by unfold cubic; ring
  rw [hid]
  exact mul_nonpos_of_nonneg_of_nonpos hs (sub_nonpos.mpr hp)


lemma threshold_sorted {A B C u v w : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvw : v ≤ w)
    (hAw : w ≤ A) (hBw : w ≤ B) (hCv : v ≤ C)
    (hrel : 2*(A+B+C)=3*(2*u+v+w)) : cubic A B C u v w ≤ 0 := by
  let y := w-v
  let a := A-w
  let b := B-w
  let c := C-v
  have hy : 0 ≤ y := sub_nonneg.mpr hvw
  have ha : 0 ≤ a := sub_nonneg.mpr hAw
  have hb : 0 ≤ b := sub_nonneg.mpr hBw
  have hc : 0 ≤ c := sub_nonneg.mpr hCv
  have hs : 2*(a+b+c)+y=6*u := by dsimp [a,b,c,y]; linarith
  have hreduce := reduce_equal_sides hu huv hy ha hb hc hs
  have hsym := symmetrize_lengths (u+y+a) (u+y+b) (u+c) u (u+y) (by positivity)
  have hlast := equal_sides_threshold hu (show u ≤ u+y by linarith)
    (show u+y ≤ ((u+y+a)+(u+y+b))/2 by linarith) (show u ≤ u+c by linarith)
    (show 4*(((u+y+a)+(u+y+b))/2)+2*(u+c)=9*u+3*(u+y) by linarith)
  have h := hreduce.trans (hsym.trans hlast)
  convert h using 1
  dsimp [a,b,c,y,cubic]
  ring

lemma cubic_offset (A B C u v w d : ℝ) :
    cubic (A+d) (B+d) (C+d) u v w = cubic A B C u v w +
      d*((A*B-u*v)+(A*C-u*w)+(B*C-v*w))+d^2*(A+B+C)+d^3 := by
  unfold cubic
  ring

theorem scalar_strength_sorted {A B C u v w : ℝ} (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (hu : 0 ≤ u) (huv : u ≤ v) (hvw : v ≤ w)
    (hub : u ≤ B) (huc : u ≤ C) (hva : v ≤ A) (hvc : v ≤ C)
    (hwa : w ≤ A) (hwb : w ≤ B)
    (hF : u/(A+u)+v/(B+v)+w/(C+w) ≤ 1) :
    3*(2*u+v+w) ≤ 2*(A+B+C) := by
  have hv : 0 ≤ v := hu.trans huv
  have hw : 0 ≤ w := hv.trans hvw
  have hH := cubic_of_fraction hA hB hC hu hv hw hF
  by_contra h
  have hgt : 2*(A+B+C)<3*(2*u+v+w) := lt_of_not_ge h
  let d := (3*(2*u+v+w)-2*(A+B+C))/6
  have hd : 0<d := by dsimp [d]; linarith
  have hthreshold := threshold_sorted hu huv hvw
    (show w ≤ A+d by linarith) (show w ≤ B+d by linarith)
    (show v ≤ C+d by linarith)
    (show 2*((A+d)+(B+d)+(C+d))=3*(2*u+v+w) by dsimp [d]; ring)
  have hp1 : 0 ≤ A*B-u*v := by nlinarith [mul_le_mul hub hva hv hB.le]
  have hp2 : 0 ≤ A*C-u*w := by nlinarith [mul_le_mul huc hwa hw hC.le]
  have hp3 : 0 ≤ B*C-v*w := by nlinarith [mul_le_mul hvc hwb hw hC.le]
  have hcoef : 0 ≤ (A*B-u*v)+(A*C-u*w)+(B*C-v*w) := by linarith
  have hnon1 := mul_nonneg hd.le hcoef
  have hnon2 := mul_nonneg (sq_nonneg d) (show 0 ≤ A+B+C by linarith)
  have hstrict := pow_pos hd 3
  rw [cubic_offset] at hthreshold
  linarith

/-- The strengthened scalar inequality in arbitrary variable order. -/
theorem scalar_strength {A B C u v w : ℝ} (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hub : u ≤ B) (huc : u ≤ C) (hva : v ≤ A) (hvc : v ≤ C)
    (hwa : w ≤ A) (hwb : w ≤ B)
    (hF : u/(A+u)+v/(B+v)+w/(C+w) ≤ 1) :
    3*(u+v+w+min u (min v w)) ≤ 2*(A+B+C) := by
  by_cases huv : u ≤ v
  · by_cases hvw : v ≤ w
    · have h := scalar_strength_sorted hA hB hC hu huv hvw hub huc hva hvc hwa hwb hF
      simp only [min_eq_left hvw, min_eq_left huv]
      linarith
    have hwv : w ≤ v := le_of_not_ge hvw
    by_cases huw : u ≤ w
    · have h := scalar_strength_sorted hA hC hB hu huw hwv huc hub hwa hwb hva hvc
        (by linarith)
      simp only [min_eq_right hwv, min_eq_left huw]
      linarith
    have hwu : w ≤ u := le_of_not_ge huw
    have h := scalar_strength_sorted hC hA hB hw hwu huv hwa hwb huc hub hvc hva
      (by linarith)
    simp only [min_eq_right hwv, min_eq_right hwu]
    linarith
  have hvu : v ≤ u := le_of_not_ge huv
  by_cases huw : u ≤ w
  · have h := scalar_strength_sorted hB hA hC hv hvu huw hva hvc hub huc hwb hwa
      (by linarith)
    simp only [min_eq_left (hvu.trans huw), min_eq_right hvu]
    linarith
  have hwu : w ≤ u := le_of_not_ge huw
  by_cases hvw : v ≤ w
  · have h := scalar_strength_sorted hB hC hA hv hvw hwu hvc hva hwb hwa hub huc
      (by linarith)
    simp only [min_eq_left hvw, min_eq_right hvu]
    linarith
  have hwv : w ≤ v := le_of_not_ge hvw
  have h := scalar_strength_sorted hC hB hA hw hwv hvu hwb hwa hvc hva huc hub
    (by linarith)
  simp only [min_eq_right hwv, min_eq_right hwu]
  linarith

/-- Barycentric form, including all zero-length boundary cases. -/
theorem scalar_strength_weighted {A B C u v w a b c : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hub : u ≤ B) (huc : u ≤ C) (hva : v ≤ A) (hvc : v ≤ C)
    (hwa : w ≤ A) (hwb : w ≤ B)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : a+b+c=1)
    (hua : (1-a)*u ≤ a*A) (hvb : (1-b)*v ≤ b*B) (hwc : (1-c)*w ≤ c*C) :
    3*(u+v+w+min u (min v w)) ≤ 2*(A+B+C) := by
  by_contra h
  have hgt : 2*(A+B+C)<3*(u+v+w+min u (min v w)) := lt_of_not_ge h
  let d := (3*(u+v+w+min u (min v w))-2*(A+B+C))/12
  have hd : 0<d := by dsimp [d]; linarith
  have hfa : u/((A+d)+u) ≤ a := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_nonneg ha hd.le]
  have hfb : v/((B+d)+v) ≤ b := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_nonneg hb hd.le]
  have hfc : w/((C+d)+w) ≤ c := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_nonneg hc hd.le]
  have hbound := scalar_strength (show 0<A+d by positivity) (show 0<B+d by positivity)
    (show 0<C+d by positivity) hu hv hw
    (show u ≤ B+d by linarith) (show u ≤ C+d by linarith)
    (show v ≤ A+d by linarith) (show v ≤ C+d by linarith)
    (show w ≤ A+d by linarith) (show w ≤ B+d by linarith) (by linarith)
  dsimp [d] at hbound
  linarith

end StrengthenedTaxicab
