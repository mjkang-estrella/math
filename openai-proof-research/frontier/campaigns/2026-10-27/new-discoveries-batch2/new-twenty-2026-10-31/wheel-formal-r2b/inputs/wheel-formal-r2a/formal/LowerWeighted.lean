import WheelProfile
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
open scoped BigOperators
namespace WheelFormal

/-- Universal parametric dual bound on actual independent wheel-square sets. -/
theorem vertexWeight_independent_bound (t : ℕ) (ht : 1 ≤ t)
    (s : WheelSet t) (hs : Independent (wheelSquare t) s) :
    (∑ v ∈ s, vertexWeight t v) ≤ 2*(2*(t:ℝ)^2+(t:ℝ)+1) := by
  classical
  let a := (mixedA t s).card
  let b := (mixedB t s).card
  let r := (rimSet t s).card
  have hat : a ≤ t := mixedA_card t ht s hs
  have hbt : b ≤ t := mixedB_card t ht s hs
  have haM : a ≤ 2*t+1 := by omega
  have hbM : b ≤ 2*t+1 := by omega
  have hrow : r ≤ (2*t+1-a)*t := rim_row_bound t ht s hs
  have hcol : r ≤ (2*t+1-b)*t := rim_column_bound t ht s hs
  have hrowR : (r:ℝ) ≤ (2*(t:ℝ)+1-a)*t := by
    have h := (Nat.cast_le (α := ℝ)).mpr hrow
    push_cast [Nat.cast_sub haM] at h
    exact h
  have hcolR : (r:ℝ) ≤ (2*(t:ℝ)+1-b)*t := by
    have h := (Nat.cast_le (α := ℝ)).mpr hcol
    push_cast [Nat.cast_sub hbM] at h
    exact h
  have htR : (1:ℝ) ≤ t := by exact_mod_cast ht
  rw [weight_profile]
  change (if (none,none) ∈ s then (2:ℝ) else 0)+((t:ℝ)+1)*((a:ℝ)+b)+2*r ≤ _
  by_cases hh : (none,none) ∈ s
  · have ha : a = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact (hub_excludes_mixed t s hs hh i).1 ((mem_mixedA t s i).mp hi)
    have hb : b = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact (hub_excludes_mixed t s hs hh i).2 ((mem_mixedB t s i).mp hi)
    simp only [hh,ite_true,ha,hb,Nat.cast_zero] at *
    nlinarith
  · simp only [hh,ite_false,zero_add]
    by_cases ha : a = 0
    · have hb0 : (0:ℝ) ≤ b := Nat.cast_nonneg _
      have hh := mul_nonneg (sub_nonneg.mpr htR) hb0
      simp only [ha,Nat.cast_zero,zero_add] at *
      nlinarith
    · by_cases hb : b = 0
      · have ha0 : (0:ℝ) ≤ a := Nat.cast_nonneg _
        have hh := mul_nonneg (sub_nonneg.mpr htR) ha0
        simp only [hb,Nat.cast_zero,add_zero] at *
        nlinarith
      · have ha1 : 1 ≤ a := by omega
        have hb1 : 1 ≤ b := by omega
        have hA : (mixedA t s).Nonempty := Finset.card_pos.mp (by omega)
        have hB : (mixedB t s).Nonempty := Finset.card_pos.mp (by omega)
        have hgrid := deletion_grid_bound t (mixedA t s) (mixedB t s) hA hB
          (rimSet t s) (rim_avoids_mixed t s hs) (rim_grid_independent t s hs)
        change 2*r ≤ (2*t+1-a)*(2*t+1-b)+(a-1)*(b-1) at hgrid
        have hgR : 2*(r:ℝ) ≤ (2*(t:ℝ)+1-a)*(2*(t:ℝ)+1-b)+((a:ℝ)-1)*((b:ℝ)-1) := by
          have h := (Nat.cast_le (α := ℝ)).mpr hgrid
          push_cast [Nat.cast_sub haM, Nat.cast_sub hbM, Nat.cast_sub ha1, Nat.cast_sub hb1] at h
          exact h
        have hF := two_sided_arithmetic (t:ℝ) (a:ℝ) (b:ℝ)
          (by exact_mod_cast ha1) (by exact_mod_cast hat)
          (by exact_mod_cast hb1) (by exact_mod_cast hbt)
        nlinarith

/-- The lower half of Conjecture 7.3, with no combinatorial hypotheses left. -/
theorem wheelSquare_fractional_lower (t : ℕ) (ht : 1 ≤ t) :
    (6*(t:ℝ)^2+7*(t:ℝ)+3)/(2*(t:ℝ)^2+(t:ℝ)+1) ≤
      fracChromatic (wheelSquare t) := by
  have hD : 0 < 2*(t:ℝ)^2+(t:ℝ)+1 := by positivity
  have h := weighted_lower_inf (wheelSquare t) (vertexWeight t)
    (vertexWeight_nonnegative t) (2*(2*(t:ℝ)^2+(t:ℝ)+1)) (by positivity)
    (fun s => vertexWeight_independent_bound t ht s.val s.property)
  rw [vertexWeight_total] at h
  have he : 2*(6*(t:ℝ)^2+7*(t:ℝ)+3)/(2*(2*(t:ℝ)^2+(t:ℝ)+1)) =
      (6*(t:ℝ)^2+7*(t:ℝ)+3)/(2*(t:ℝ)^2+(t:ℝ)+1) := by field_simp
  rwa [he] at h
end WheelFormal
