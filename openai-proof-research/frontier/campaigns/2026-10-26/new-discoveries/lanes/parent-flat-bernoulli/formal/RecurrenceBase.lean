import GridKernel

open Finset
namespace FlatBernoulli

theorem renewal_value_0 : renewalCoefficient 0 = (1/1:ℝ) := by
  rw [renewalCoefficient]
  norm_num

theorem renewal_value_1 : renewalCoefficient 1 = (0/1:ℝ) := by
  rw [renewalCoefficient]
  norm_num

theorem renewal_value_2 : renewalCoefficient 2 = (1/2:ℝ) := by
  rw [renewalCoefficient]
  norm_num [Finset.sum_range_succ,renewal_value_0,renewal_value_1]

theorem renewal_value_3 : renewalCoefficient 3 = (1/6:ℝ) := by
  rw [renewalCoefficient]
  norm_num [Finset.sum_range_succ,renewal_value_0,renewal_value_1,renewal_value_2]

theorem renewal_value_4 : renewalCoefficient 4 = (1/3:ℝ) := by
  rw [renewalCoefficient]
  norm_num [Finset.sum_range_succ,renewal_value_0,renewal_value_1,renewal_value_2,renewal_value_3]

theorem renewal_value_5 : renewalCoefficient 5 = (13/60:ℝ) := by
  rw [renewalCoefficient]
  norm_num [Finset.sum_range_succ,renewal_value_0,renewal_value_1,renewal_value_2,renewal_value_3,renewal_value_4]

theorem renewal_value_6 : renewalCoefficient 6 = (97/360:ℝ) := by
  rw [renewalCoefficient]
  norm_num [Finset.sum_range_succ,renewal_value_0,renewal_value_1,renewal_value_2,renewal_value_3,renewal_value_4,renewal_value_5]

theorem renewal_value_7 : renewalCoefficient 7 = (571/2520:ℝ) := by
  rw [renewalCoefficient]
  norm_num [Finset.sum_range_succ,renewal_value_0,renewal_value_1,renewal_value_2,renewal_value_3,renewal_value_4,renewal_value_5,renewal_value_6]

theorem renewal_value_8 : renewalCoefficient 8 = (1217/5040:ℝ) := by
  rw [renewalCoefficient]
  norm_num [Finset.sum_range_succ,renewal_value_0,renewal_value_1,renewal_value_2,renewal_value_3,renewal_value_4,renewal_value_5,renewal_value_6,renewal_value_7]

theorem renewal_value_9 : renewalCoefficient 9 = (3391/15120:ℝ) := by
  rw [renewalCoefficient]
  norm_num [Finset.sum_range_succ,renewal_value_0,renewal_value_1,renewal_value_2,renewal_value_3,renewal_value_4,renewal_value_5,renewal_value_6,renewal_value_7,renewal_value_8]

theorem renewal_value_10 : renewalCoefficient 10 = (953/4200:ℝ) := by
  rw [renewalCoefficient]
  norm_num [Finset.sum_range_succ,renewal_value_0,renewal_value_1,renewal_value_2,renewal_value_3,renewal_value_4,renewal_value_5,renewal_value_6,renewal_value_7,renewal_value_8,renewal_value_9]

theorem renewal_value_11 : renewalCoefficient 11 = (13003/59400:ℝ) := by
  rw [renewalCoefficient]
  norm_num [Finset.sum_range_succ,renewal_value_0,renewal_value_1,renewal_value_2,renewal_value_3,renewal_value_4,renewal_value_5,renewal_value_6,renewal_value_7,renewal_value_8,renewal_value_9,renewal_value_10]

theorem renewal_value_12 : renewalCoefficient 12 = (434737/1995840:ℝ) := by
  rw [renewalCoefficient]
  norm_num [Finset.sum_range_succ,renewal_value_0,renewal_value_1,renewal_value_2,renewal_value_3,renewal_value_4,renewal_value_5,renewal_value_6,renewal_value_7,renewal_value_8,renewal_value_9,renewal_value_10,renewal_value_11]

theorem renewal_value_13 : renewalCoefficient 13 = (2767231/12972960:ℝ) := by
  rw [renewalCoefficient]
  norm_num [Finset.sum_range_succ,renewal_value_0,renewal_value_1,renewal_value_2,renewal_value_3,renewal_value_4,renewal_value_5,renewal_value_6,renewal_value_7,renewal_value_8,renewal_value_9,renewal_value_10,renewal_value_11,renewal_value_12]

theorem renewal_value_14 : renewalCoefficient 14 = (383735791/1816214400:ℝ) := by
  rw [renewalCoefficient]
  norm_num [Finset.sum_range_succ,renewal_value_0,renewal_value_1,renewal_value_2,renewal_value_3,renewal_value_4,renewal_value_5,renewal_value_6,renewal_value_7,renewal_value_8,renewal_value_9,renewal_value_10,renewal_value_11,renewal_value_12,renewal_value_13]

theorem renewal_base_third : renewalCoefficient 3-renewalCoefficient 2 = -(1/3:ℝ) := by
  rw [renewal_value_3,renewal_value_2]
  norm_num

theorem renewal_base_twelve : renewalCoefficient 12-renewalCoefficient 11 < -(1/2000:ℝ) := by
  rw [renewal_value_12,renewal_value_11]
  norm_num

theorem renewal_base_fourteen : renewalCoefficient 14-renewalCoefficient 13 <
    renewalCoefficient 12-renewalCoefficient 11 := by
  rw [renewal_value_14,renewal_value_13,renewal_value_12,renewal_value_11]
  norm_num

end FlatBernoulli
