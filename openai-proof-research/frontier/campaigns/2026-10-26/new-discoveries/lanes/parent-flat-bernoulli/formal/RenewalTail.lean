import RecurrenceBase
import ArrowheadCriterion

open Finset Filter
open scoped Topology
namespace FlatBernoulli
noncomputable section

def gridIncrement (N n : ℕ) : ℝ := gridMoment N n-gridMoment N (n-1)
def renewalIncrement (n : ℕ) : ℝ := renewalCoefficient n-renewalCoefficient (n-1)

theorem gridIncrement_tendsto (n : ℕ) :
    Tendsto (fun N : ℕ => gridIncrement N n) atTop (𝓝 (renewalIncrement n)) :=
  (gridMoment_tendsto n).sub (gridMoment_tendsto (n-1))

theorem renewal_even_bound (m : ℕ) :
    renewalIncrement (12+2*m) ≤ -(1/2000:ℝ)*(1/4)^m := by
  have he12 := (gridIncrement_tendsto 12).eventually_lt_const renewal_base_twelve
  have hdiff : renewalIncrement 14-renewalIncrement 12 < 0 := by
    change (renewalCoefficient 14-renewalCoefficient 13)-
      (renewalCoefficient 12-renewalCoefficient 11) < 0
    linarith [renewal_base_fourteen]
  have he14 := ((gridIncrement_tendsto 14).sub
    (gridIncrement_tendsto 12)).eventually_lt_const hdiff
  apply le_of_tendsto (gridIncrement_tendsto (12+2*m))
  filter_upwards [he12,he14,Filter.eventually_atTop.2 ⟨1,fun N hN => hN⟩] with N h12 h14 hN
  have hNpos : 0 < N := by omega
  have hsecond : 1/2 ≤ ∑ i : Fin N, (gridS N i*gridR N i)^2 := gridV_second_lower N hNpos
  have hb := arrowhead_even_increment_bound (gridNode N) (gridR N) (gridS N)
    (gridNode_nonneg N) (gridR_mass N hNpos) (gridS_sq N hNpos) hsecond
    (c := (1/2000:ℝ)) (by norm_num) h12.le (by
      change gridIncrement N 14 ≤ gridIncrement N 12
      linarith) m
  have hv : (fun i : Fin N => gridS N i*gridR N i) = gridV N := rfl
  rw [hv] at hb
  change centerMoment (gridNode N) (gridV N) (12+2*m)-
    centerMoment (gridNode N) (gridV N) (12+2*m-1) ≤ _
  rw [show 12+2*m-1=11+2*m by omega]
  exact hb

theorem renewal_odd_bound (m : ℕ) : renewalIncrement (2*m+1) ≤ -(1/4:ℝ)^m := by
  have hthird : renewalIncrement 3 < -(1/4:ℝ) := by
    change renewalCoefficient 3-renewalCoefficient 2 < -(1/4:ℝ)
    rw [renewal_base_third]
    norm_num
  have he3 := (gridIncrement_tendsto 3).eventually_lt_const hthird
  apply le_of_tendsto (gridIncrement_tendsto (2*m+1))
  filter_upwards [he3,Filter.eventually_atTop.2 ⟨1,fun N hN => hN⟩] with N h3 hN
  have hNpos : 0 < N := by omega
  have hb := arrowhead_odd_increment_bound (gridNode N) (gridR N) (gridS N)
    (gridNode_nonneg N) (gridR_mass N hNpos) (gridS_sq N hNpos) h3.le m
  have hv : (fun i : Fin N => gridS N i*gridR N i) = gridV N := rfl
  rw [hv] at hb
  change centerMoment (gridNode N) (gridV N) (2*m+1)-
    centerMoment (gridNode N) (gridV N) (2*m+1-1) ≤ _
  rw [Nat.add_sub_cancel]
  exact hb

theorem renewal_tail_negative (n : ℕ) (hn : 11 ≤ n) : renewalIncrement n < 0 := by
  obtain ⟨k,he | ho⟩ := Nat.even_or_odd' n
  · have he' : n = 12+2*(k-6) := by omega
    rw [he']
    have h := renewal_even_bound (k-6)
    have hp : 0 < (1/2000:ℝ)*(1/4:ℝ)^(k-6) := by positivity
    linarith
  · rw [ho]
    have h := renewal_odd_bound k
    have hp : 0 < (1/4:ℝ)^k := by positivity
    linarith

end
end FlatBernoulli
