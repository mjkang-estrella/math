import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic

/-!
Original support code by Myeongjin Kang. MIT.
Scoped scalar and finite-sum interfaces for ANS263. This file does not formalize
the Coulomb Hamiltonian, event conditioning, conditional PDE, or the full result.
-/

open Finset Filter
open scoped Topology

namespace ANS263

noncomputable def probabilityExponent : ℝ := 99 / 100
noncomputable def packetExponent : ℝ := 1 / 10000
noncomputable def baselineExponent : ℝ := 1 / 100000
noncomputable def badBandExponent : ℝ := probabilityExponent - 15 * packetExponent
noncomputable def initialExponent : ℝ := probabilityExponent - 9 * packetExponent

theorem exact_exponents :
    badBandExponent = 1977 / 2000 ∧ initialExponent = 9891 / 10000 ∧
    7 * badBandExponent / 2 - 3 = 1839 / 4000 := by
  norm_num [badBandExponent, initialExponent, probabilityExponent, packetExponent]

theorem simultaneous_parameter_margins :
    0 < (1 - probabilityExponent) / 4 - (5 / 2) * packetExponent ∧
    0 < (1 - probabilityExponent) - 3 * packetExponent ∧
    0 < (1 - probabilityExponent) / 2 - packetExponent / 2 ∧
    0 < (1 / 100 : ℝ) - 4 * baselineExponent ∧
    0 < (2 / 100 : ℝ) / 4 - (5 / 2) * baselineExponent ∧
    6 / 7 < badBandExponent ∧ badBandExponent < 1 ∧
    0 < (7 / 3 : ℝ) * initialExponent - 1 := by
  norm_num [badBandExponent, initialExponent, probabilityExponent,
    packetExponent, baselineExponent]

theorem dyadic_gain_positive {α : ℝ} (hα : 6 / 7 < α) :
    0 < 7 * α / 2 - 3 := by linarith

theorem dyadic_ratio_bounds {g : ℝ} (hg : 0 < g) :
    0 ≤ (1 / 2 : ℝ) ^ g ∧ (1 / 2 : ℝ) ^ g < 1 := by
  exact ⟨Real.rpow_nonneg (by norm_num) _,
    Real.rpow_lt_one (by norm_num) (by norm_num) hg⟩

theorem finite_geometric_bound {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    (∑ j ∈ range n, q ^ j) ≤ 1 / (1 - q) := by
  simpa using (geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hq hq1)

theorem weighted_finite_budget {q E : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hE : 0 ≤ E) (n : ℕ) (mass : ℕ → ℝ)
    (hm : ∀ j ∈ range n, mass j ≤ E * q ^ j) :
    (∑ j ∈ range n, mass j) ≤ E / (1 - q) := by
  calc
    (∑ j ∈ range n, mass j) ≤ ∑ j ∈ range n, E * q ^ j := sum_le_sum hm
    _ = E * (∑ j ∈ range n, q ^ j) := (mul_sum _ _ _).symm
    _ ≤ E * (1 / (1 - q)) := mul_le_mul_of_nonneg_left
      (finite_geometric_bound hq hq1 n) hE
    _ = E / (1 - q) := by ring

theorem dyadic_weighted_budget {e β g : ℝ} (he : 0 ≤ e) (hg : 0 < g)
    (n : ℕ) (mass : ℕ → ℝ)
    (hm : ∀ j ∈ range n, mass j ≤ e ^ β * ((1 / 2 : ℝ) ^ g) ^ j) :
    (∑ j ∈ range n, mass j) ≤ e ^ β / (1 - (1 / 2 : ℝ) ^ g) := by
  obtain ⟨hq, hq1⟩ := dyadic_ratio_bounds hg
  exact weighted_finite_budget hq hq1 (Real.rpow_nonneg he β) n mass hm

theorem sum_of_two_weighted_budgets {q t E F : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (ht : 0 ≤ t) (ht1 : t < 1)
    (hE : 0 ≤ E) (hF : 0 ≤ F) (n : ℕ) (mass : ℕ → ℝ)
    (hm : ∀ j ∈ range n, mass j ≤ E * q ^ j + F * t ^ j) :
    (∑ j ∈ range n, mass j) ≤ E / (1 - q) + F / (1 - t) := by
  calc
    (∑ j ∈ range n, mass j) ≤ ∑ j ∈ range n, (E * q ^ j + F * t ^ j) := sum_le_sum hm
    _ = (∑ j ∈ range n, E * q ^ j) + ∑ j ∈ range n, F * t ^ j := sum_add_distrib
    _ ≤ E / (1 - q) + F / (1 - t) := add_le_add
      (weighted_finite_budget hq hq1 hE n _ (fun _ _ => le_rfl))
      (weighted_finite_budget ht ht1 hF n _ (fun _ _ => le_rfl))

theorem vanishing_budget {e : ℕ → ℝ} {β q : ℝ}
    (he : Tendsto e atTop (𝓝 0)) (hβ : 0 < β) (_hq : q < 1) :
    Tendsto (fun n => e n ^ β / (1 - q)) atTop (𝓝 0) := by
  simpa using (he.rpow_const_nhds_zero hβ).div_const (1 - q)

theorem scaled_annular_identity {s D x β : ℝ} (hs : 0 < s)
    (hD : 0 ≤ D) (hx : 0 ≤ x) :
    s ^ 3 * D ^ β * (s * x) ^ (7 * β - 3) =
      (D * s ^ 7) ^ β * x ^ (7 * β - 3) := by
  rw [Real.mul_rpow hs.le hx, Real.rpow_sub hs,
    Real.mul_rpow hD (pow_nonneg hs.le 7)]
  rw [Real.rpow_ofNat, ← Real.rpow_ofNat s 7, ← Real.rpow_mul hs.le]
  field_simp [ne_of_gt hs]

theorem arbitrary_depth_budget_vanishes {e : ℕ → ℝ} {β q : ℝ}
    (he : Tendsto e atTop (𝓝 0)) (he0 : ∀ n, 0 ≤ e n)
    (hβ : 0 < β) (hq : 0 ≤ q) (hq1 : q < 1)
    (depth : ℕ → ℕ) (mass : ℕ → ℕ → ℝ)
    (hm0 : ∀ n j, 0 ≤ mass n j)
    (hm : ∀ n j, j ∈ range (depth n) → mass n j ≤ e n ^ β * q ^ j) :
    Tendsto (fun n => ∑ j ∈ range (depth n), mass n j) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => sum_nonneg (fun j _ => hm0 n j))
    (fun n => weighted_finite_budget hq hq1 (Real.rpow_nonneg (he0 n) β)
      (depth n) (mass n) (hm n))
  exact vanishing_budget he hβ hq1

theorem two_rate_arbitrary_depth_vanishes {e s : ℕ → ℝ} {β γ q t : ℝ}
    (he : Tendsto e atTop (𝓝 0)) (hs : Tendsto s atTop (𝓝 0))
    (he0 : ∀ n, 0 ≤ e n) (hs0 : ∀ n, 0 ≤ s n)
    (hβ : 0 < β) (hγ : 0 < γ)
    (hq : 0 ≤ q) (hq1 : q < 1) (ht : 0 ≤ t) (ht1 : t < 1)
    (depth : ℕ → ℕ) (mass : ℕ → ℕ → ℝ)
    (hm0 : ∀ n j, 0 ≤ mass n j)
    (hm : ∀ n j, j ∈ range (depth n) →
      mass n j ≤ e n ^ β * q ^ j + s n ^ γ * t ^ j) :
    Tendsto (fun n => ∑ j ∈ range (depth n), mass n j) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => sum_nonneg (fun j _ => hm0 n j))
    (fun n => sum_of_two_weighted_budgets hq hq1 ht ht1
      (Real.rpow_nonneg (he0 n) β) (Real.rpow_nonneg (hs0 n) γ)
      (depth n) (mass n) (hm n))
  simpa using (vanishing_budget (q := q) he hβ hq1).add (vanishing_budget (q := t) hs hγ ht1)

theorem positive_mass_tail_bound {r d : ℝ} (hr : 0 < r) (hd : 2 * r ≤ d) :
    (1 / 2 : ℝ) ≤ 1 - r / d := by
  have hd0 : 0 < d := by linarith
  have hdiv : r / d ≤ 1 / 2 := (div_le_iff₀ hd0).2 (by linarith)
  linarith

theorem finite_neutral_tail_bound {ι : Type*} (I : Finset ι)
    (weight distance : ι → ℝ) {r : ℝ} (hr : 0 < r)
    (hw : ∀ i ∈ I, 0 ≤ weight i) (hd : ∀ i ∈ I, 2 * r ≤ distance i) :
    (∑ i ∈ I, weight i) ≤ 2 * ∑ i ∈ I, (1 - r / distance i) * weight i := by
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have h := mul_le_mul_of_nonneg_right (positive_mass_tail_bound hr (hd i hi)) (hw i hi)
  nlinarith

noncomputable def thresholdRadius (mass : ℝ → ℝ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ mass r ≤ 1}

theorem threshold_bracket {mass : ℝ → ℝ} (hmono : Antitone mass)
    {a b : ℝ} (hb : 0 ≤ b) (haMass : 1 < mass a) (hbMass : mass b ≤ 1) :
    a ≤ thresholdRadius mass ∧ thresholdRadius mass ≤ b := by
  have hne : ({r : ℝ | 0 ≤ r ∧ mass r ≤ 1} : Set ℝ).Nonempty := ⟨b, hb, hbMass⟩
  constructor
  · apply le_csInf hne
    intro r hr
    by_contra h
    have hlt : r < a := lt_of_not_ge h
    have hma := hmono hlt.le
    exact (not_le_of_gt haMass) (hma.trans hr.2)
  · apply csInf_le
    · exact ⟨0, fun r hr => hr.1⟩
    · exact ⟨hb, hbMass⟩

end ANS263
