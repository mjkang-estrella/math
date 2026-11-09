import FairEntropy333569
import Mathlib.Analysis.Normed.Group.Tannery

namespace MathDB333569
noncomputable section
open Filter Finset

def entropySeries (l t : ℝ) : ℝ :=
  (∑' g : ℕ, (1/2:ℝ)^(g+1)*conditionalEntropy (l^(g+1)) t) - conditionalEntropy l t

def triangularEntropy (l t : ℝ) (n g : ℕ) : ℝ :=
  if g < n then ((n-g : ℕ) : ℝ)/(n+1) * ((1/2:ℝ)^(g+1)*conditionalEntropy (l^(g+1)) t) else 0

theorem triangularEntropy_tendsto {l t : ℝ} (hl : l ∈ Set.Icc 0 1)
    (ht : t ∈ Set.Icc (-1) 1) :
    Tendsto (fun n => ∑' g, triangularEntropy l t n g) atTop
      (nhds (∑' g : ℕ, (1/2:ℝ)^(g+1)*conditionalEntropy (l^(g+1)) t)) := by
  have hdiv : Tendsto (fun n : ℕ => (1:ℝ)/(n+1)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  apply tendsto_tsum_of_dominated_convergence geometricMajorant_summable
  · intro g
    have hc : Tendsto (fun n : ℕ => 1-(g+1:ℝ)/(n+1)) atTop (nhds 1) := by
      have h := (tendsto_const_nhds (x := (1:ℝ))).sub (hdiv.const_mul (g+1:ℝ))
      simpa only [mul_zero, sub_zero, mul_one_div] using h
    have hh := hc.mul_const ((1/2:ℝ)^(g+1)*conditionalEntropy (l^(g+1)) t)
    simp only [one_mul] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop g] with n hn
    unfold triangularEntropy
    rw [ite_eq_left hn, Nat.cast_sub hn.le]
    congr 1
    field_simp
    ring
  · apply Filter.Eventually.of_forall
    intro n g
    have hH := conditionalEntropy_nonneg
      (show l^(g+1) ∈ Set.Icc (0:ℝ) 1 from ⟨pow_nonneg hl.1 _, pow_le_one₀ hl.1 hl.2⟩) ht
    have hbound := conditionalEntropy_le (r := l^(g+1)) ht
    unfold triangularEntropy
    split_ifs with hgn
    · have hcoef : 0 ≤ ((n-g:ℕ):ℝ)/(n+1) := by positivity
      have hcoef1 : ((n-g:ℕ):ℝ)/(n+1) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        have h := Nat.sub_le n g
        exact_mod_cast (show n-g ≤ n+1 by omega)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hcoef (mul_nonneg (by positivity) hH))]
      exact (mul_le_of_le_one_left (mul_nonneg (by positivity) hH) hcoef1).trans
        (mul_le_mul_of_nonneg_left hbound (by positivity))
    · simp only [norm_zero]
      positivity

theorem fair_gap_weight (n g : ℕ) (hg : g < n) :
    2 * (2:ℝ)^(n-g-1) / (2:ℝ)^(n+1) = (1/2:ℝ)^(g+1) := by
  have he : n+1 = (n-g-1)+(g+1)+1 := by omega
  rw [he, pow_add, pow_add, pow_one, div_pow, one_pow]
  field_simp

/-- Literal uniform weights and the finite-size boundary term. -/
theorem fairEntropy_average {l t : ℝ} (hl : 0 < l) (hl1 : l < 1)
    (ht : -1 < t) (ht1 : t < 1) (n : ℕ) :
    2 * (∑ S : Finset (Fin (n+1)), sampleEntropy (chart l t) n S) / (2:ℝ)^(n+1) =
      2*(1-(1/2:ℝ)^(n+1))*initialEntropy (chart l t) +
      ∑ g : Fin n, (n-g.val:ℕ) * (1/2:ℝ)^(g.val+1) * conditionalEntropy (l^(g.val+1)) t := by
  rw [fairEntropy_gap_sum hl hl1 ht ht1]
  rw [mul_add, add_div, Finset.mul_sum, Finset.sum_div]
  congr 1
  · rw [div_pow, one_pow]
    field_simp
  · apply sum_congr rfl
    intro g _
    have h := fair_gap_weight n g.val g.isLt
    calc
      _ = ((n-g.val:ℕ):ℝ) * (2*(2:ℝ)^(n-g.val-1)/(2:ℝ)^(n+1)) *
          conditionalEntropy (l^(g.val+1)) t := by ring
      _ = _ := by rw [h]


theorem triangularEntropy_tsum (l t : ℝ) (n : ℕ) :
    (∑' g, triangularEntropy l t n g) =
      (∑ g : Fin n, (n-g.val:ℕ) * (1/2:ℝ)^(g.val+1)*conditionalEntropy (l^(g.val+1)) t)/(n+1) := by
  rw [tsum_eq_sum (s := Finset.range n) (fun g hg => by
    simp only [Finset.mem_range] at hg
    simp [triangularEntropy,hg])]
  rw [← Fin.sum_univ_eq_sum_range, Finset.sum_div]
  apply sum_congr rfl
  intro g _
  rw [triangularEntropy, ite_eq_left g.isLt]
  ring

/-- Exact finite source expression, with an explicit vanishing boundary term. -/
theorem finiteIntricacy_series_boundary {l t : ℝ} (hl : 0 < l) (hl1 : l < 1)
    (ht : -1 < t) (ht1 : t < 1) (n : ℕ) :
    finiteIntricacy (chart l t) n =
      (((1-2*(1/2:ℝ)^(n+1))*initialEntropy (chart l t)+conditionalEntropy l t)/(n+1)) +
        (∑' g, triangularEntropy l t n g) - conditionalEntropy l t := by
  unfold finiteIntricacy
  rw [fairEntropy_average hl hl1 ht ht1, sampleEntropy_univ,
    wordEntropy_eq _ (chart_mem_interior hl hl1 ht ht1),
    transitionEntropy_chart (ne_of_lt hl1), triangularEntropy_tsum]
  field_simp
  ring

/-- The source finite-subset intricacy converges to the entropy series for every
interior chart parameter, not merely on the symmetric slice. -/
theorem finiteIntricacy_tendsto_series {l t : ℝ} (hl : 0 < l) (hl1 : l < 1)
    (ht : -1 < t) (ht1 : t < 1) :
    Tendsto (finiteIntricacy (chart l t)) atTop (nhds (entropySeries l t)) := by
  have hg : Tendsto (fun n : ℕ => (1/2:ℝ)^(n+1)) atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)).mul_const (1/2:ℝ)
    simpa only [pow_succ, zero_mul] using h
  have hnum : Tendsto (fun n : ℕ => (1-2*(1/2:ℝ)^(n+1))*initialEntropy (chart l t)+conditionalEntropy l t)
      atTop (nhds (initialEntropy (chart l t)+conditionalEntropy l t)) := by
    convert (((tendsto_const_nhds (x := (1:ℝ))).sub (hg.const_mul 2)).mul_const
      (initialEntropy (chart l t))).add_const (conditionalEntropy l t) using 1
    ring
  have hboundary := hnum.div_atTop
    (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ))))
  have hsum := triangularEntropy_tendsto (l := l) (t := t) ⟨hl.le,hl1.le⟩ ⟨ht.le,ht1.le⟩
  have h := (hboundary.add hsum).sub_const (conditionalEntropy l t)
  have he : finiteIntricacy (chart l t) = (fun n =>
      (((1-2*(1/2:ℝ)^(n+1))*initialEntropy (chart l t)+conditionalEntropy l t)/(n+1)) +
        (∑' g, triangularEntropy l t n g) - conditionalEntropy l t) :=
    funext (finiteIntricacy_series_boundary hl hl1 ht ht1)
  rw [he]
  simpa only [zero_add, entropySeries] using h

theorem sourceIntricacy_eq_series {l t : ℝ} (hl : 0 < l) (hl1 : l < 1)
    (ht : -1 < t) (ht1 : t < 1) :
    sourceIntricacy (chart l t) = entropySeries l t := by
  exact (finiteIntricacy_tendsto_series hl hl1 ht ht1).limUnder_eq

/-- Actual rank-zero uniform intricacy of the stationary two-sided law has this
limit, with all measure and finite-subset identifications proved. -/
theorem rankZeroFiniteIntricacy_tendsto_series {l t : ℝ} (hl : 0 < l) (hl1 : l < 1)
    (ht : -1 < t) (ht1 : t < 1) (k : ℤ) :
    Tendsto (rankZeroFiniteIntricacy
      (twoSidedLaw (chart l t) (chart_mem_interior hl hl1 ht ht1)) k) atTop
      (nhds (entropySeries l t)) := by
  have he : rankZeroFiniteIntricacy
      (twoSidedLaw (chart l t) (chart_mem_interior hl hl1 ht ht1)) k = finiteIntricacy (chart l t) :=
    funext (rankZeroFiniteIntricacy_eq _ _ k)
  rw [he]
  exact finiteIntricacy_tendsto_series hl hl1 ht ht1

end
end MathDB333569
