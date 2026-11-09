import Mathlib

namespace NewDiscoveries.Taxicab

lemma frac_concave {a : ℝ} (ha : 0 < a) :
    ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x / (a+x)) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy p q hp hq hpq
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  simp only [smul_eq_mul]
  have hax : 0 < a+x := by positivity
  have hay : 0 < a+y := by positivity
  have haz : 0 < a+(p*x+q*y) := by positivity
  have hid : (p*x+q*y)/(a+(p*x+q*y)) -
      (p*(x/(a+x))+q*(y/(a+y))) =
      a*p*q*(x-y)^2 / ((a+x)*(a+y)*(a+(p*x+q*y))) := by
    field_simp
    rw [show q = 1-p by linarith]
    ring
  have hn : 0 ≤ a*p*q*(x-y)^2 / ((a+x)*(a+y)*(a+(p*x+q*y))) := by positivity
  linarith

lemma frac_jensen3 {a x y z p q r : ℝ} (ha : 0<a)
    (hx : 0≤x) (hy : 0≤y) (hz : 0≤z)
    (hp : 0≤p) (hq : 0≤q) (hr : 0≤r) (hs : p+q+r=1) :
    p*(x/(a+x)) + q*(y/(a+y)) + r*(z/(a+z)) ≤
      (p*x+q*y+r*z)/(a+(p*x+q*y+r*z)) := by
  have h := (frac_concave ha).le_map_sum (t:=Finset.univ)
    (w:= ![p,q,r]) (p:= ![x,y,z])
    (by intro i hi; fin_cases i <;> simp_all)
    (by simpa [Fin.sum_univ_succ, add_assoc] using hs)
    (by intro i hi; fin_cases i <;> simp_all)
  simpa [Fin.sum_univ_succ, smul_eq_mul, add_assoc] using h

lemma vertex1 {A B C x : ℝ} (hA : 0<A) (hAB : A≤B) (hBC : B≤C)
    (hx : 0≤x) (he : 3*x=2*(B+C-2*A)) :
    1 ≤ x/(A+x) + A/(B+A) + A/(C+A) := by
  have hB : 0<B := lt_of_lt_of_le hA hAB
  have hC : 0<C := lt_of_lt_of_le hB hBC
  have hpoly : 0 ≤ x*(2*A+B+C)-(B*C-A^2) := by
    have hCA : A≤C := hAB.trans hBC
    have h1 := mul_nonneg (sub_nonneg.mpr hAB) (show 0≤B+A by positivity)
    have h2 := mul_nonneg (sub_nonneg.mpr hCA) (show 0≤C+A by positivity)
    have h3 := add_nonneg (mul_nonneg (sub_nonneg.mpr hAB) hC.le)
      (mul_nonneg hA.le (sub_nonneg.mpr hCA))
    have he' : 3*x*(2*A+B+C)=2*(B+C-2*A)*(2*A+B+C) := by rw [he]
    nlinarith [he']
  have hid : x/(A+x)+A/(B+A)+A/(C+A)-1 =
      A*(x*(2*A+B+C)-(B*C-A^2))/((A+x)*(B+A)*(C+A)) := by
    field_simp
    ring
  have : 0 ≤ A*(x*(2*A+B+C)-(B*C-A^2))/((A+x)*(B+A)*(C+A)) := by positivity
  linarith

lemma vertex2 {A B C x : ℝ} (hA : 0<A) (hAB : A≤B) (hBC : B≤C)
    (hx : 0≤x) (he : 3*x=2*C-A-B) :
    1 ≤ B/(A+B) + x/(B+x) + A/(C+A) := by
  have hB : 0<B := lt_of_lt_of_le hA hAB
  have hC : 0<C := lt_of_lt_of_le hB hBC
  have hCA : A≤C := hAB.trans hBC
  have hfirst : (C-B)/(B+C) ≤ x/(B+x) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hpos := mul_nonneg hB.le (show 0≤B+C-2*A by linarith)
    have he' : 3*x*B=(2*C-A-B)*B := by rw [he]
    nlinarith
  have hsecond : A*(C-B)/((A+B)*(A+C)) ≤ (C-B)/(B+C) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hpos := mul_nonneg (sub_nonneg.mpr hBC) (show 0≤A^2+B*C by positivity)
    nlinarith
  have hid : B/(A+B)+A/(C+A) = 1-A*(C-B)/((A+B)*(A+C)) := by
    field_simp
    ring
  linarith

lemma vertex3 {A B C x : ℝ} (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (hx : 0≤x) : 1 ≤ B/(A+B) + A/(B+A) + x/(C+x) := by
  have he : B/(A+B)+A/(B+A)=1 := by field_simp; ring
  have : 0≤x/(C+x) := by positivity
  linarith

/-- On the threshold slice, the fraction sum is at least one. -/
lemma threshold_sorted {A B C u v w : ℝ} (hA : 0<A) (hAB : A≤B) (hBC : B≤C)
    (_hu : 0≤u) (_hv : 0≤v) (_hw : 0≤w)
    (hub : u≤B) (hva : v≤A) (hwa : w≤A)
    (ht : 3*(u+v+w)=2*(A+B+C)) :
    1 ≤ u/(A+u)+v/(B+v)+w/(C+w) := by
  have hB : 0<B := lt_of_lt_of_le hA hAB
  have hC : 0<C := lt_of_lt_of_le hB hBC
  let D := B+2*A-(u+v+w)
  have hD : 0≤D := by dsimp [D]; linarith
  have hDA : D≤A := by dsimp [D]; linarith
  have hDB : D≤B := le_trans hDA hAB
  have hx : 0≤B-D := sub_nonneg.mpr hDB
  have hy : 0≤A-D := sub_nonneg.mpr hDA
  have hV1 := vertex1 hA hAB hBC hx (show 3*(B-D)=2*(B+C-2*A) by dsimp [D]; linarith)
  have hV2 := vertex2 hA hAB hBC hy (show 3*(A-D)=2*C-A-B by dsimp [D]; linarith)
  have hV3 := vertex3 hA hB hC hy
  by_cases hDz : D=0
  · have huB : u=B := by dsimp [D] at hDz; linarith
    have hvA : v=A := by dsimp [D] at hDz; linarith
    have hwA : w=A := by dsimp [D] at hDz; linarith
    simpa [huB,hvA,hwA,hDz] using hV3
  have hDp : 0<D := lt_of_le_of_ne hD (Ne.symm hDz)
  let p := (B-u)/D
  let q := (A-v)/D
  let r := (A-w)/D
  have hp : 0≤p := div_nonneg (sub_nonneg.mpr hub) hD
  have hq : 0≤q := div_nonneg (sub_nonneg.mpr hva) hD
  have hr : 0≤r := div_nonneg (sub_nonneg.mpr hwa) hD
  have hs : p+q+r=1 := by
    dsimp [p,q,r]
    field_simp
    dsimp [D]
    ring
  have hxu : p*(B-D)+q*B+r*B=u := by
    dsimp [p,q,r]
    field_simp
    dsimp [D]
    ring
  have hxv : p*A+q*(A-D)+r*A=v := by
    dsimp [p,q,r]
    field_simp
    dsimp [D]
    ring
  have hxw : p*A+q*A+r*(A-D)=w := by
    dsimp [p,q,r]
    field_simp
    dsimp [D]
    ring
  have hj1 := frac_jensen3 hA hx hB.le hB.le hp hq hr hs
  have hj2 := frac_jensen3 hB hA.le hy hA.le hp hq hr hs
  have hj3 := frac_jensen3 hC hA.le hA.le hy hp hq hr hs
  rw [hxu] at hj1
  rw [hxv] at hj2
  rw [hxw] at hj3
  have hv1 := mul_nonneg hp (sub_nonneg.mpr hV1)
  have hv2 := mul_nonneg hq (sub_nonneg.mpr hV2)
  have hv3 := mul_nonneg hr (sub_nonneg.mpr hV3)
  nlinarith

lemma frac_mono {a x y : ℝ} (ha : 0<a) (hx : 0≤x) (hxy : x≤y) :
    x/(a+x) ≤ y/(a+y) := by
  apply (div_le_div_iff₀ (by positivity) (by linarith)).2
  nlinarith

lemma frac_strict_mono {a x y : ℝ} (ha : 0<a) (hx : 0≤x) (hxy : x<y) :
    x/(a+x) < y/(a+y) := by
  apply (div_lt_div_iff₀ (by positivity) (by linarith)).2
  nlinarith

/-- The scalar inequality in sorted vertex lengths. -/
theorem scalar_sorted {A B C u v w : ℝ} (hA : 0<A) (hAB : A≤B) (hBC : B≤C)
    (hu : 0≤u) (hv : 0≤v) (hw : 0≤w)
    (hub : u≤B) (hva : v≤A) (hwa : w≤A)
    (hF : u/(A+u)+v/(B+v)+w/(C+w)≤1) :
    3*(u+v+w)≤2*(A+B+C) := by
  by_contra h
  have hgt : 2*(A+B+C)<3*(u+v+w) := lt_of_not_ge h
  have hB : 0<B := lt_of_lt_of_le hA hAB
  have hC : 0<C := lt_of_lt_of_le hB hBC
  have hsum : 0<u+v+w := by linarith
  let k := 2*(A+B+C)/(3*(u+v+w))
  have hk : 0<k := by dsimp [k]; positivity
  have hklt : k<1 := (div_lt_one (by positivity)).2 hgt
  have hku : k*u≤u := by nlinarith
  have hkv : k*v≤v := by nlinarith
  have hkw : k*w≤w := by nlinarith
  have hku0 : 0≤k*u := mul_nonneg hk.le hu
  have hkv0 : 0≤k*v := mul_nonneg hk.le hv
  have hkw0 : 0≤k*w := mul_nonneg hk.le hw
  have ht : 3*(k*u+k*v+k*w)=2*(A+B+C) := by
    dsimp [k]
    field_simp
  have hthreshold := threshold_sorted hA hAB hBC hku0 hkv0 hkw0
    (hku.trans hub) (hkv.trans hva) (hkw.trans hwa) ht
  have hm1 := frac_mono hA hku0 hku
  have hm2 := frac_mono hB hkv0 hkv
  have hm3 := frac_mono hC hkw0 hkw
  have hstrict : k*u/(A+k*u)+k*v/(B+k*v)+k*w/(C+k*w) <
      u/(A+u)+v/(B+v)+w/(C+w) := by
    rcases lt_or_ge 0 u with huPos | huZero
    · have hs := frac_strict_mono hA hku0 (show k*u<u by nlinarith)
      linarith
    rcases lt_or_ge 0 v with hvPos | hvZero
    · have hs := frac_strict_mono hB hkv0 (show k*v<v by nlinarith)
      linarith
    have hwPos : 0<w := by linarith
    have hs := frac_strict_mono hC hkw0 (show k*w<w by nlinarith)
    linarith
  linarith

/-- Scalar core of the unrestricted taxicab Erdős–Mordell inequality.
This is one lemma of the candidate result, not a separately counted discovery. -/
theorem scalar_bound {A B C u v w : ℝ} (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (hu : 0≤u) (hv : 0≤v) (hw : 0≤w)
    (hub : u≤B) (huc : u≤C) (hva : v≤A) (hvc : v≤C) (hwa : w≤A) (hwb : w≤B)
    (hF : u/(A+u)+v/(B+v)+w/(C+w)≤1) :
    3*(u+v+w)≤2*(A+B+C) := by
  by_cases hAB : A≤B
  · by_cases hBC : B≤C
    · exact scalar_sorted hA hAB hBC hu hv hw hub hva hwa hF
    have hCB : C≤B := le_of_not_ge hBC
    by_cases hAC : A≤C
    · have h := scalar_sorted hA hAC hCB hu hw hv huc hwa hva (by linarith)
      linarith
    have hCA : C≤A := le_of_not_ge hAC
    have h := scalar_sorted hC hCA hAB hw hu hv hwa huc hvc (by linarith)
    linarith
  have hBA : B≤A := le_of_not_ge hAB
  by_cases hAC : A≤C
  · have h := scalar_sorted hB hBA hAC hv hu hw hva hub hwb (by linarith)
    linarith
  have hCA : C≤A := le_of_not_ge hAC
  by_cases hBC : B≤C
  · have h := scalar_sorted hB hBC hCA hv hw hu hvc hwb hub (by linarith)
    linarith
  have hCB : C≤B := le_of_not_ge hBC
  have h := scalar_sorted hC hCB hBA hw hv hu hwb hvc huc (by linarith)
  linarith

/-- Barycentric form, allowing zero lengths and avoiding all divisions by a zero length. -/
theorem scalar_weighted {A B C u v w a b c : ℝ}
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hu : 0≤u) (hv : 0≤v) (hw : 0≤w)
    (hub : u≤B) (huc : u≤C) (hva : v≤A) (hvc : v≤C) (hwa : w≤A) (hwb : w≤B)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hs : a+b+c=1)
    (hua : (1-a)*u≤a*A) (hvb : (1-b)*v≤b*B) (hwc : (1-c)*w≤c*C) :
    3*(u+v+w)≤2*(A+B+C) := by
  by_contra h
  have hgt : 2*(A+B+C)<3*(u+v+w) := lt_of_not_ge h
  let d := (3*(u+v+w)-2*(A+B+C))/12
  have hd : 0<d := by dsimp [d]; linarith
  have hfa : u/((A+d)+u)≤a := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_nonneg ha hd.le]
  have hfb : v/((B+d)+v)≤b := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_nonneg hb hd.le]
  have hfc : w/((C+d)+w)≤c := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_nonneg hc hd.le]
  have hbound := scalar_bound (show 0<A+d by positivity) (show 0<B+d by positivity)
    (show 0<C+d by positivity) hu hv hw
    (show u≤B+d by linarith) (show u≤C+d by linarith)
    (show v≤A+d by linarith) (show v≤C+d by linarith)
    (show w≤A+d by linarith) (show w≤B+d by linarith) (by linarith)
  dsimp [d] at hbound
  linarith

#print axioms scalar_bound
#print axioms scalar_weighted
end NewDiscoveries.Taxicab
