import Approximation

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped ContDiff

namespace MittagModulus

/-- The lower difference, with arbitrary positive steps. -/
def mixedDifference : List ℝ → (ℝ → ℝ) → ℝ → ℝ
  | [], f => f
  | h :: hs, f => fun t => mixedDifference hs f t - mixedDifference hs f (t + h)

def PositiveMixedDifferences (f : ℝ → ℝ) : Prop :=
  ∀ hs : List ℝ, (∀ h ∈ hs, 0 < h) → ∀ t : ℝ, 0 < t →
    0 ≤ mixedDifference hs f t

theorem mixedDifference_neg (hs : List ℝ) (f : ℝ → ℝ) :
    mixedDifference hs (-f) = -mixedDifference hs f := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    funext t
    simp only [mixedDifference, ih, Pi.neg_apply]
    ring

theorem mixedDifference_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hs : List ℝ) :
    ContDiff ℝ ∞ (mixedDifference hs f) := by
  induction hs with
  | nil => exact hf
  | cons h hs ih => exact ih.sub (ih.comp (contDiff_id.add contDiff_const))

theorem deriv_mixedDifference {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hs : List ℝ) :
    deriv (mixedDifference hs f) = mixedDifference hs (deriv f) := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    have hd : Differentiable ℝ (mixedDifference hs f) :=
      (mixedDifference_contDiff hf hs).differentiable (by simp)
    funext t
    change deriv (fun t => mixedDifference hs f t - mixedDifference hs f (t + h)) t = _
    have hds : DifferentiableAt ℝ (fun x => mixedDifference hs f (x + h)) t :=
      (hd (t + h)).comp t (differentiableAt_id.add_const h)
    change deriv (mixedDifference hs f - (fun x => mixedDifference hs f (x + h))) t = _
    rw [deriv_sub (hd t) hds, deriv_comp_add_const]
    rw [ih]
    rfl

theorem PositiveMixedDifferences.antitone_mixed {f : ℝ → ℝ}
    (hf : PositiveMixedDifferences f) (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h) :
    AntitoneOn (mixedDifference hs f) (Set.Ioi 0) := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hxy
  · exact le_rfl
  · have hh : 0 < y - x := sub_pos.mpr hxy
    have hpos : ∀ h ∈ (y - x) :: hs, 0 < h := by
      intro h hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hh
      · exact hhs h hmem
    have h := hf ((y - x) :: hs) hpos x hx
    change 0 ≤ mixedDifference hs f x - mixedDifference hs f (x + (y - x)) at h
    have he : x + (y - x) = y := by ring
    rw [he] at h
    linarith

theorem PositiveMixedDifferences.neg_deriv {f : ℝ → ℝ}
    (hf : PositiveMixedDifferences f) (hcont : ContDiff ℝ ∞ f) :
    PositiveMixedDifferences (-deriv f) := by
  intro hs hhs t ht
  have ha := hf.antitone_mixed hs hhs
  have hd : derivWithin (mixedDifference hs f) (Set.Ioi 0) t ≤ 0 := ha.derivWithin_nonpos
  rw [derivWithin_of_isOpen isOpen_Ioi ht] at hd
  rw [mixedDifference_neg, Pi.neg_apply, ← deriv_mixedDifference hcont hs]
  linarith

theorem mixedDifference_tendsto {f : ℝ → ℝ} {F : ℕ → ℝ → ℝ}
    (hF : ∀ t, Filter.Tendsto (fun N => F N t) Filter.atTop (nhds (f t)))
    (hs : List ℝ) (t : ℝ) :
    Filter.Tendsto (fun N => mixedDifference hs (F N) t) Filter.atTop
      (nhds (mixedDifference hs f t)) := by
  induction hs generalizing t with
  | nil => exact hF t
  | cons h hs ih => exact (ih t).sub (ih (t + h))

theorem PositiveMixedDifferences.of_tendsto {f : ℝ → ℝ} {F : ℕ → ℝ → ℝ}
    (hF : ∀ N, PositiveMixedDifferences (F N))
    (hlim : ∀ t, Filter.Tendsto (fun N => F N t) Filter.atTop (nhds (f t))) :
    PositiveMixedDifferences f := by
  intro hs hhs t ht
  exact ge_of_tendsto (mixedDifference_tendsto hlim hs t)
    (Filter.Eventually.of_forall (fun N => hF N hs hhs t ht))

theorem PositiveMixedDifferences.iteratedDeriv_sign {f : ℝ → ℝ}
    (hf : PositiveMixedDifferences f) (hc : ContDiff ℝ ∞ f) (k : ℕ)
    (t : ℝ) (ht : 0 < t) : 0 ≤ (-1 : ℝ) ^ k * iteratedDeriv k f t := by
  induction k generalizing f with
  | zero => simpa only [pow_zero, iteratedDeriv_zero, one_mul, mixedDifference] using hf [] (by simp) t ht
  | succ k ih =>
    have hd : ContDiff ℝ ∞ (-deriv f) := ((contDiff_infty_iff_deriv.mp hc).2).neg
    have h := ih (hf.neg_deriv hc) hd
    rw [iteratedDeriv_neg] at h
    rw [iteratedDeriv_succ', pow_succ]
    nlinarith

theorem PositiveMixedDifferences.completelyMonotone {f : ℝ → ℝ}
    (hf : PositiveMixedDifferences f) (hc : ContDiff ℝ ∞ f) :
    CompletelyMonotonePositive f :=
  ⟨hc.contDiffOn, fun k t ht => hf.iteratedDeriv_sign hc k t ht⟩

theorem mixedDifference_exp (ell : ℝ) (hs : List ℝ) (t : ℝ) :
    mixedDifference hs (fun x => Real.exp (-ell * x)) t =
      Real.exp (-ell * t) * (hs.map (fun h => 1 - Real.exp (-ell * h))).prod := by
  induction hs generalizing t with
  | nil => simp [mixedDifference]
  | cons h hs ih =>
    change mixedDifference hs (fun x => Real.exp (-ell * x)) t -
      mixedDifference hs (fun x => Real.exp (-ell * x)) (t + h) = _
    rw [ih t, ih (t + h)]
    have he : -ell * (t + h) = -ell * t + -ell * h := by ring
    rw [he, Real.exp_add, List.map_cons, List.prod_cons]
    ring

theorem positiveMixedDifferences_exp {ell : ℝ} (hell : 0 ≤ ell) :
    PositiveMixedDifferences (fun x => Real.exp (-ell * x)) := by
  intro hs hhs t _
  rw [mixedDifference_exp]
  apply mul_nonneg (Real.exp_nonneg _)
  apply List.prod_nonneg
  intro u hu
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hu
  have hneg : -ell * h ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hhs h hh).le
  have he : Real.exp (-ell * h) ≤ 1 := Real.exp_le_one_iff.mpr hneg
  linarith

theorem mixedDifference_add (hs : List ℝ) (f g : ℝ → ℝ) :
    mixedDifference hs (f + g) = mixedDifference hs f + mixedDifference hs g := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    funext t
    simp only [mixedDifference, ih, Pi.add_apply]
    ring

theorem mixedDifference_const_mul (hs : List ℝ) (c : ℝ) (f : ℝ → ℝ) :
    mixedDifference hs (fun t => c * f t) = fun t => c * mixedDifference hs f t := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    funext t
    simp only [mixedDifference, ih]
    ring

theorem PositiveMixedDifferences.add {f g : ℝ → ℝ}
    (hf : PositiveMixedDifferences f) (hg : PositiveMixedDifferences g) :
    PositiveMixedDifferences (f + g) := by
  intro hs hhs t ht
  rw [mixedDifference_add, Pi.add_apply]
  exact add_nonneg (hf hs hhs t ht) (hg hs hhs t ht)

theorem PositiveMixedDifferences.const_mul {f : ℝ → ℝ}
    (hf : PositiveMixedDifferences f) {c : ℝ} (hc : 0 ≤ c) :
    PositiveMixedDifferences (fun t => c * f t) := by
  intro hs hhs t ht
  rw [mixedDifference_const_mul]
  exact mul_nonneg hc (hf hs hhs t ht)

theorem mixedDifference_continuousOn_param {F : ℝ → ℝ → ℝ} {a b : ℝ}
    (hF : ∀ t, ContinuousOn (fun u => F u t) (Set.uIcc a b))
    (hs : List ℝ) (t : ℝ) :
    ContinuousOn (fun u => mixedDifference hs (F u) t) (Set.uIcc a b) := by
  induction hs generalizing t with
  | nil => exact hF t
  | cons h hs ih => exact (ih t).sub (ih (t + h))

theorem mixedDifference_intervalIntegral {F : ℝ → ℝ → ℝ} {a b : ℝ}
    (hF : ∀ t, ContinuousOn (fun u => F u t) (Set.uIcc a b))
    (hs : List ℝ) (t : ℝ) :
    mixedDifference hs (fun x => ∫ u in a..b, F u x) t =
      ∫ u in a..b, mixedDifference hs (F u) t := by
  induction hs generalizing t with
  | nil => rfl
  | cons h hs ih =>
    change mixedDifference hs (fun x => ∫ u in a..b, F u x) t -
      mixedDifference hs (fun x => ∫ u in a..b, F u x) (t + h) = _
    rw [ih t, ih (t + h)]
    exact (intervalIntegral.integral_sub
      (mixedDifference_continuousOn_param hF hs t).intervalIntegrable
      (mixedDifference_continuousOn_param hF hs (t + h)).intervalIntegrable).symm

theorem PositiveMixedDifferences.intervalIntegral {F : ℝ → ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hF : ∀ t, ContinuousOn (fun u => F u t) (Set.uIcc a b))
    (hpos : ∀ u ∈ Set.Icc a b, PositiveMixedDifferences (F u)) :
    PositiveMixedDifferences (fun t => ∫ u in a..b, F u t) := by
  intro hs hhs t ht
  rw [mixedDifference_intervalIntegral hF]
  exact intervalIntegral.integral_nonneg hab (fun u hu => hpos u hu hs hhs t ht)

theorem mixedDifference_tendsto_positive {f : ℝ → ℝ} {F : ℕ → ℝ → ℝ}
    (hF : ∀ t, 0 < t → Filter.Tendsto (fun N => F N t) Filter.atTop (nhds (f t)))
    (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h) (t : ℝ) (ht : 0 < t) :
    Filter.Tendsto (fun N => mixedDifference hs (F N) t) Filter.atTop
      (nhds (mixedDifference hs f t)) := by
  induction hs generalizing t with
  | nil => exact hF t ht
  | cons h hs ih =>
    have hh : 0 < h := hhs h (by simp)
    have htail : ∀ u ∈ hs, 0 < u := fun u hu => hhs u (List.mem_cons_of_mem h hu)
    exact (ih htail t ht).sub (ih htail (t + h) (by linarith))

theorem PositiveMixedDifferences.of_tendsto_positive {f : ℝ → ℝ} {F : ℕ → ℝ → ℝ}
    (hF : ∀ N, PositiveMixedDifferences (F N))
    (hlim : ∀ t, 0 < t → Filter.Tendsto (fun N => F N t) Filter.atTop (nhds (f t))) :
    PositiveMixedDifferences f := by
  intro hs hhs t ht
  exact ge_of_tendsto (mixedDifference_tendsto_positive hlim hs hhs t ht)
    (Filter.Eventually.of_forall (fun N => hF N hs hhs t ht))

end MittagModulus
