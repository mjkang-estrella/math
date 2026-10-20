/- Copyright (c) 2026 Myeongjin Kang. Released under the MIT license.
   Exact rational witnesses and countermodels; not geometric/probabilistic instances. -/
import T088P133

namespace T088P133Controls
open T088P133

-- Complete hypotheses for a mixed example with just one strict moment.
theorem rational_example_hypotheses :
    (0:ℝ)<2/3 ∧ (0:ℝ)<4/3 ∧ (2/3:ℝ)+4/3=2 ∧
    (0:ℝ)<1/3 ∧ (1/3:ℝ)<1 ∧ (2/3:ℝ)=1-1/3 ∧
    (0:ℝ)≤3/2 ∧ (0:ℝ)<1/2 ∧ (0:ℝ)<4/3 ∧
    2*(3/2:ℝ)*(1/3)^2<1/2 ∧ 2*(3/2:ℝ)*(2/3)^2=4/3 := by norm_num

theorem rational_example_bound :
    (1+(3/2:ℝ))*((1/3)*(2/3)/(2/3+(1/2)/(1/3))+
      (2/3)*(4/3)/(4/3+(4/3)/(2/3))) < 1 := by
  apply rational_mixture_lt_one <;> norm_num

theorem rational_example_value :
    mixture (2/3) (4/3) (1/3) (2/3) (3/2) ((1/2)/(1/3)) ((4/3)/(2/3)) = 12/13 := by
  norm_num [mixture]

theorem zero_d_bound :
    (1+(0:ℝ))*((1/2)*1/(1+1/(1/2))+(1/2)*1/(1+1/(1/2))) < 1 := by
  apply rational_mixture_lt_one <;> norm_num

theorem zero_d_value : mixture 1 1 (1/2) (1/2) 0 2 2 = 1/3 := by
  norm_num [mixture]

-- All remaining strict-theorem hypotheses hold; only the first strict moment is lost.
theorem nonstrict_equality_hypotheses :
    (0:ℝ)<1 ∧ (1:ℝ)+1=2 ∧ (0:ℝ)<1/2 ∧ (1/2:ℝ)<1 ∧
    (1/2:ℝ)=1-1/2 ∧ (0:ℝ)≤1 ∧ (0:ℝ)<1/2 ∧
    2*(1:ℝ)*(1/2)^2=1/2 ∧ mixture 1 1 (1/2) (1/2) 1 1 1 = 1 := by
  norm_num [mixture]

theorem nonstrict_example_bound :
    (1+(1:ℝ))*((1/2)*1/(1+(1/2)/(1/2))+(1/2)*1/(1+(1/2)/(1/2))) ≤ 1 := by
  apply rational_mixture_le_one <;> norm_num

theorem nonstrict_cannot_imply_strict : ¬ mixture 1 1 (1/2) (1/2) 1 1 1 < 1 := by
  norm_num [mixture]

-- Failure of first moment even as a weak inequality; second moment still holds.
theorem missing_first_moment :
    (0:ℝ)<1 ∧ (1:ℝ)+1=2 ∧ (0:ℝ)<1/2 ∧ (1/2:ℝ)<1 ∧
    (1/2:ℝ)=1-1/2 ∧ (0:ℝ)≤1 ∧ (0:ℝ)<1/8 ∧ (0:ℝ)<1/2 ∧
    ¬ (2*(1:ℝ)*(1/2)^2 ≤ 1/8) ∧ 2*(1:ℝ)*(1/2)^2≤1/2 ∧
    mixture 1 1 (1/2) (1/2) 1 ((1/8)/(1/2)) ((1/2)/(1/2)) = 13/10 ∧
    (1:ℝ)<13/10 := by norm_num [mixture]

-- The strict first moment holds; removing only the second moment breaks the bound.
theorem missing_second_moment :
    (0:ℝ)<1 ∧ (1:ℝ)+1=2 ∧ (0:ℝ)<1/2 ∧ (1/2:ℝ)<1 ∧
    (1/2:ℝ)=1-1/2 ∧ (0:ℝ)≤1 ∧ (0:ℝ)<1 ∧ (0:ℝ)<1/8 ∧
    2*(1:ℝ)*(1/2)^2<1 ∧ ¬ (2*(1:ℝ)*(1/2)^2≤1/8) ∧
    mixture 1 1 (1/2) (1/2) 1 (1/(1/2)) ((1/8)/(1/2)) = 17/15 ∧
    (1:ℝ)<17/15 := by norm_num [mixture]

theorem missing_sum_normalization :
    (0:ℝ)<2 ∧ (2:ℝ)+2≠2 ∧ (0:ℝ)<1/2 ∧ (1/2:ℝ)<1 ∧
    (1/2:ℝ)=1-1/2 ∧ (0:ℝ)≤1 ∧ (0:ℝ)<1 ∧ (0:ℝ)<1/2 ∧
    2*(1:ℝ)*(1/2)^2<1 ∧ 2*(1:ℝ)*(1/2)^2≤1/2 ∧
    mixture 2 2 (1/2) (1/2) 1 (1/(1/2)) ((1/2)/(1/2)) = 7/6 ∧
    (1:ℝ)<7/6 := by norm_num [mixture]

-- Nonzero denominators: this failure is not an artifact of Lean's total division.
theorem missing_alpha_positivity :
    (-2:ℝ)<0 ∧ (0:ℝ)<4 ∧ (-2:ℝ)+4=2 ∧
    (0:ℝ)<1/2 ∧ (1/2:ℝ)<1 ∧ (1/2:ℝ)=1-1/2 ∧ (0:ℝ)≤1 ∧
    (0:ℝ)<3/4 ∧ (0:ℝ)<1/2 ∧
    2*(1:ℝ)*(1/2)^2<3/4 ∧ 2*(1:ℝ)*(1/2)^2≤1/2 ∧
    (-2:ℝ)+(3/4)/(1/2)≠0 ∧ (4:ℝ)+(1/2)/(1/2)≠0 ∧
    mixture (-2) 4 (1/2) (1/2) 1 ((3/4)/(1/2)) ((1/2)/(1/2)) = 24/5 ∧
    (1:ℝ)<24/5 := by norm_num [mixture]

theorem missing_beta_positivity :
    (0:ℝ)<4 ∧ (-2:ℝ)<0 ∧ (4:ℝ)+(-2)=2 ∧
    (0:ℝ)<1/2 ∧ (1/2:ℝ)<1 ∧ (1/2:ℝ)=1-1/2 ∧ (0:ℝ)≤1 ∧
    (0:ℝ)<1 ∧ (0:ℝ)<3/4 ∧
    2*(1:ℝ)*(1/2)^2<1 ∧ 2*(1:ℝ)*(1/2)^2≤3/4 ∧
    (4:ℝ)+1/(1/2)≠0 ∧ (-2:ℝ)+(3/4)/(1/2)≠0 ∧
    mixture 4 (-2) (1/2) (1/2) 1 (1/(1/2)) ((3/4)/(1/2)) = 14/3 ∧
    (1:ℝ)<14/3 := by norm_num [mixture]

-- q is free here; p remains strictly between 0 and 1.
theorem missing_weight_normalization :
    (0:ℝ)<1 ∧ (1:ℝ)+1=2 ∧ (0:ℝ)<1/2 ∧ (1/2:ℝ)<1 ∧
    (1:ℝ)≠1-1/2 ∧ (0:ℝ)≤0 ∧ (0:ℝ)<1/8 ∧ (0:ℝ)<1/4 ∧
    2*(0:ℝ)*(1/2)^2<1/8 ∧ 2*(0:ℝ)*1^2≤1/4 ∧
    mixture 1 1 (1/2) 1 0 ((1/8)/(1/2)) ((1/4)/1) = 6/5 ∧
    (1:ℝ)<6/5 := by norm_num [mixture]

theorem missing_probability_range :
    (0:ℝ)<1 ∧ (1:ℝ)+1=2 ∧ (0:ℝ)<2 ∧ ¬ (2:ℝ)<1 ∧
    (-1:ℝ)=1-2 ∧ (0:ℝ)≤0 ∧ (0:ℝ)<1 ∧ (0:ℝ)<2 ∧
    2*(0:ℝ)*2^2<1 ∧ 2*(0:ℝ)*(-1)^2≤2 ∧
    (1:ℝ)+1/2≠0 ∧ (1:ℝ)+2/(-1)≠0 ∧
    mixture 1 1 2 (-1) 0 (1/2) (2/(-1)) = 7/3 ∧
    (1:ℝ)<7/3 := by norm_num [mixture]

theorem endpoint_examples :
    (1+(1:ℝ))/(1+2/1)<1 ∧ (1+(1:ℝ))/(1+2/1)<1 := by
  constructor
  · exact p_one_bound 1 1 1 2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact p_zero_bound 1 1 1 2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)

theorem endpoint_zero_d : (1+(0:ℝ))/(1+1/1)<1 := by
  exact one_sided_lt_one 1 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem endpoint_upper_boundary :
    (0:ℝ)<2 ∧ 2*(1:ℝ)≤2 ∧ (1+(1:ℝ))/(1+2/2)=1 := by norm_num

theorem endpoint_zero_moment :
    (0:ℝ)<1 ∧ (1:ℝ)<2 ∧ 2*(0:ℝ)≤0 ∧ (1+(0:ℝ))/(1+0/1)=1 := by norm_num

theorem endpoint_missing_moment :
    (0:ℝ)<1 ∧ (1:ℝ)<2 ∧ (0:ℝ)<1 ∧ ¬ 2*(2:ℝ)≤1 ∧
    (1+(2:ℝ))/(1+1/1)=3/2 ∧ (1:ℝ)<3/2 := by norm_num

end T088P133Controls
