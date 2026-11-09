import ArrowheadSpectral

open Finset Matrix
namespace FlatBernoulli
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_arrowhead_spectral_parameter (t r s : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hr : ∑ i, r i^2 = 1) (hs : ∀ i, s i^2 = 1-t i)
    (hsecond : 1/2 ≤ ∑ i, (s i*r i)^2) :
    ∃ q : ℝ, 1/2 ≤ q ∧ q ≤ 1 ∧
      ∀ i, (arrowhead_isHermitian t (fun j => s j*r j)).eigenvalues i < 0 →
        (arrowhead_isHermitian t (fun j => s j*r j)).eigenvalues i = -q := by
  let v := fun i => s i*r i
  let μ := (arrowhead_isHermitian t v).eigenvalues
  let w := centerWeight t v
  have hw : ∀ i, 0 ≤ w i := centerWeight_nonneg t v
  have hx : ∀ i, μ i ≤ 1 := fun i => (arrowhead_spectral_interval t r s ht hr hs i).2
  have hmean : ∑ i, w i*μ i = 0 := centerWeight_mean t v
  have htwo : 1/2 ≤ ∑ i, w i*μ i^2 := by
    rw [← centerMoment_spectral, centerMoment_two]
    exact hsecond
  obtain ⟨i, hi⟩ := exists_negative_spectral w μ hw hx hmean (by linarith)
  refine ⟨-μ i, ?_, ?_, ?_⟩
  · apply spectral_negative_size w μ hw hx (by linarith) ?_ (centerWeight_mass t v) hmean htwo
    intro j hj
    have hij := arrowhead_negative_index_unique t v ht i j hi hj
    simp only [neg_neg]
    rw [hij]
  · have hlow := (arrowhead_spectral_interval t r s ht hr hs i).1
    change -μ i ≤ 1
    linarith
  · intro j hj
    have hij := arrowhead_negative_index_unique t v ht i j hi hj
    simpa only [neg_neg] using congrArg μ hij.symm

theorem arrowhead_even_increment_bound (t r s : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hr : ∑ i, r i^2 = 1) (hs : ∀ i, s i^2 = 1-t i)
    (hsecond : 1/2 ≤ ∑ i, (s i*r i)^2) {c : ℝ} (hc : 0 < c)
    (hbase : centerMoment t (fun i => s i*r i) 12-
      centerMoment t (fun i => s i*r i) 11 ≤ -c)
    (hnext : centerMoment t (fun i => s i*r i) 14-
      centerMoment t (fun i => s i*r i) 13 ≤
      centerMoment t (fun i => s i*r i) 12-centerMoment t (fun i => s i*r i) 11)
    (m : ℕ) : centerMoment t (fun i => s i*r i) (12+2*m)-
      centerMoment t (fun i => s i*r i) (11+2*m) ≤ -c*(1/4)^m := by
  let v := fun i => s i*r i
  obtain ⟨q,hq0,hq1,hneg⟩ := exists_arrowhead_spectral_parameter t r s ht hr hs hsecond
  have hb : spectralIncrement (centerWeight t v) (arrowhead_isHermitian t v).eigenvalues 12 ≤ -c := by
    rw [← centerMoment_increment t v 12 (by norm_num)]
    exact hbase
  have hn : spectralIncrement (centerWeight t v) (arrowhead_isHermitian t v).eigenvalues 14 ≤
      spectralIncrement (centerWeight t v) (arrowhead_isHermitian t v).eigenvalues 12 := by
    rw [← centerMoment_increment t v 14 (by norm_num),
      ← centerMoment_increment t v 12 (by norm_num)]
    exact hnext
  have hbnd := spectralIncrement_even_bound (centerWeight t v)
    (arrowhead_isHermitian t v).eigenvalues (centerWeight_nonneg t v)
    (fun i => (arrowhead_spectral_interval t r s ht hr hs i).2) hq0 hq1 hc hneg hb hn m
  rw [← centerMoment_increment t v (12+2*m) (by omega)] at hbnd
  simpa only [show 12+2*m-1 = 11+2*m by omega] using hbnd

theorem arrowhead_odd_increment_bound (t r s : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hr : ∑ i, r i^2 = 1) (hs : ∀ i, s i^2 = 1-t i)
    (hthird : centerMoment t (fun i => s i*r i) 3-
      centerMoment t (fun i => s i*r i) 2 ≤ -(1/4)) (m : ℕ) :
    centerMoment t (fun i => s i*r i) (2*m+1)-
      centerMoment t (fun i => s i*r i) (2*m) ≤ -(1/4:ℝ)^m := by
  let v := fun i => s i*r i
  have hb : spectralIncrement (centerWeight t v) (arrowhead_isHermitian t v).eigenvalues 3 ≤ -(1/4) := by
    rw [← centerMoment_increment t v 3 (by norm_num)]
    exact hthird
  have hbnd := spectralIncrement_odd_bound (centerWeight t v)
    (arrowhead_isHermitian t v).eigenvalues (centerWeight_nonneg t v)
    (fun i => (arrowhead_spectral_interval t r s ht hr hs i).2)
    (centerWeight_mass t v) (centerWeight_mean t v) hb m
  rw [← centerMoment_increment t v (2*m+1) (by omega)] at hbnd
  simpa only [Nat.add_sub_cancel] using hbnd

end
end FlatBernoulli
