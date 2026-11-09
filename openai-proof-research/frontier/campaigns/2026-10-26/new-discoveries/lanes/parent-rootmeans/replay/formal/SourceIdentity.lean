import OddMeanIdentity

noncomputable section
open Finset Polynomial
namespace OddRootMeans

def normalizedParameters (p : ℂ[X]) (i : ℕ) : ℂ :=
  p.coeff (p.natDegree-i) / p.leadingCoeff / (p.natDegree.choose i : ℂ)

lemma normalizedParameters_zero (p : ℂ[X]) (hp : p≠0) : normalizedParameters p 0 = 1 := by
  simp [normalizedParameters, coeff_natDegree, leadingCoeff_ne_zero.mpr hp]

lemma polynomial_eq_appell (p : ℂ[X]) (hp : p≠0) :
    p = C p.leadingCoeff * appell (normalizedParameters p) p.natDegree := by
  ext j
  rw [coeff_C_mul, appell_coeff]
  by_cases hj : j≤p.natDegree
  · have hchoose : (p.natDegree.choose j : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hj)
    simp only [normalizedParameters, Nat.sub_sub_self hj, Nat.choose_symm hj]
    field_simp [leadingCoeff_ne_zero.mpr hp]
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, mul_zero,
      coeff_eq_zero_of_natDegree_lt (by omega)]

lemma derivativeRootMean_scale (p : ℂ[X]) (c : ℂ) (hc : c≠0) (r : ℕ) :
    derivativeRootMean (C c * p) r = c * derivativeRootMean p r := by
  rw [derivativeRootMean, iterate_derivative_C_mul, roots_C_mul _ hc,
    natDegree_C_mul hc]
  simp only [eval_mul, eval_C, Multiset.sum_map_mul_left, derivativeRootMean]
  ring

theorem source_conjecture_336466 (p : ℂ[X]) (hodd : Odd p.natDegree) :
    (∑ r ∈ Ioo 0 p.natDegree, (-1 : ℂ)^r * (p.natDegree.choose r : ℂ) *
      derivativeRootMean p r) = 0 := by
  have hp : p≠0 := by
    intro hp
    simp [hp] at hodd
  let a := normalizedParameters p
  have ha : a 0 = 1 := normalizedParameters_zero p hp
  have hm := appell_odd_identity a ha p.natDegree hodd
  have hscale (r : ℕ) : derivativeRootMean p r =
      p.leadingCoeff * derivativeRootMean (appell a p.natDegree) r := by
    conv_lhs => rw [polynomial_eq_appell p hp]
    exact derivativeRootMean_scale _ _ (leadingCoeff_ne_zero.mpr hp) r
  simp_rw [hscale]
  calc
    (∑ r ∈ Ioo 0 p.natDegree, (-1 : ℂ)^r * (p.natDegree.choose r : ℂ) *
      (p.leadingCoeff * derivativeRootMean (appell a p.natDegree) r)) =
      p.leadingCoeff * (∑ r ∈ Ioo 0 p.natDegree,
        (-1 : ℂ)^r * (p.natDegree.choose r : ℂ) * derivativeRootMean (appell a p.natDegree) r) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro r _
          ring
    _ = 0 := by rw [hm, mul_zero]

end OddRootMeans
