import GammaRatio
import ConvexExtrapolation
import BinomialAnchors
import GridMajorization

open Set Real Filter
open scoped Topology

namespace FractionalBinomial

noncomputable def generalizedBinomial (k j : ℕ) (a : ℝ) : ℝ :=
  Real.Gamma (a*k+1)/(Real.Gamma (a*j+1)*Real.Gamma (a*((k-j:ℕ):ℝ)+1))

noncomputable def binomialSum (k : ℕ) (a p q : ℝ) : ℝ :=
  ∑ j∈Finset.range (k+1), generalizedBinomial k j a*p^(a*j)*q^(a*((k-j:ℕ):ℝ))

noncomputable def logTerm (j l : ℕ) (p q a : ℝ) : ℝ :=
  Real.log (Real.Gamma ((j+l:ℕ)*a+1))-Real.log (Real.Gamma ((j:ℝ)*a+1))-
    Real.log (Real.Gamma ((l:ℝ)*a+1))+a*j*Real.log p+a*l*Real.log q

lemma convex_logTerm_of_grid (hgrid : GridMajorizes) (j l : ℕ) (p q : ℝ) :
    ConvexOn ℝ (Ioi 0) (logTerm j l p q) := by
  have hlin : ConvexOn ℝ (Ioi 0) (fun a : ℝ => a*j*Real.log p+a*l*Real.log q) := by
    refine ⟨convex_Ioi 0, ?_⟩
    intro x _ y _ a b _ _ _
    simp only [smul_eq_mul]
    ring_nf
    exact le_rfl
  have h := (scaledGammaLog_convex_nonneg_of_grid hgrid j l).add hlin
  convert h using 1
  ext a
  dsimp [logTerm]
  ring

lemma exp_logTerm_eq {k j : ℕ} (hjk : j ≤ k) {a p q : ℝ}
    (ha : 0<a) (hp : 0<p) (hq : 0<q) :
    Real.exp (logTerm j (k-j) p q a)=generalizedBinomial k j a*p^(a*j)*q^(a*((k-j:ℕ):ℝ)) := by
  have hsum : j+(k-j)=k := Nat.add_sub_of_le hjk
  have hΓk : 0<Real.Gamma (a*k+1) := Real.Gamma_pos_of_pos (by positivity)
  have hΓj : 0<Real.Gamma (a*j+1) := Real.Gamma_pos_of_pos (by positivity)
  have hΓl : 0<Real.Gamma (a*((k-j:ℕ):ℝ)+1) := Real.Gamma_pos_of_pos (by positivity)
  simp only [logTerm, hsum, Real.exp_add, Real.exp_sub, mul_comm (k:ℝ) a,
    mul_comm (j:ℝ) a, mul_comm ((k-j:ℕ):ℝ) a,
    Real.exp_log hΓk, Real.exp_log hΓj, Real.exp_log hΓl,
    Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hq, generalizedBinomial]
  rw [mul_comm (Real.log p), mul_comm (Real.log q)]
  ring

lemma binomialSum_log_convex_of_grid (hgrid : GridMajorizes) (k : ℕ) {p q : ℝ}
    (hp : 0<p) (hq : 0<q) :
    ConvexOn ℝ (Ioi 0) (fun a => Real.log (binomialSum k a p q)) := by
  have h := convex_log_sum_exp (Finset.range (k+1)) (by simp) (convex_Ioi (0:ℝ))
    (fun j a => logTerm j (k-j) p q a) (fun j _ => convex_logTerm_of_grid hgrid j (k-j) p q)
  apply h.congr
  intro a ha
  dsimp only
  unfold binomialSum
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact exp_logTerm_eq (by have := Finset.mem_range.mp hj; omega) ha hp hq

lemma generalizedBinomial_nat {k j : ℕ} (hjk : j ≤ k) (m : ℕ) :
    generalizedBinomial k j (m:ℝ)=((m*k).choose (m*j):ℝ) := by
  simp only [generalizedBinomial, ← Nat.cast_mul, Real.Gamma_nat_eq_factorial]
  rw [Nat.cast_choose ℝ (Nat.mul_le_mul_left m hjk), ← Nat.mul_sub_left_distrib]
  push_cast
  rfl

lemma binomialSum_one (k : ℕ) (p q : ℝ) :
    binomialSum k 1 p q=(p+q)^k := by
  unfold binomialSum
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
  have hgen := generalizedBinomial_nat hjk 1
  norm_num only [Nat.cast_one, one_mul] at hgen
  rw [hgen]
  simp only [one_mul, Real.rpow_natCast]
  ring

lemma binomialSum_two (k : ℕ) (p q : ℝ) :
    2*binomialSum k 2 p q=(p+q)^(2*k)+(-p+q)^(2*k) := by
  rw [even_binomial_identity]
  congr 1
  unfold binomialSum
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
  have hgen := generalizedBinomial_nat hjk 2
  norm_num only [Nat.cast_ofNat] at hgen
  rw [hgen]
  have hcast (n : ℕ) : (2:ℝ)*(n:ℝ)=((2*n:ℕ):ℝ) := by norm_num
  simp only [hcast, Real.rpow_natCast]

lemma gridMajorizes_proved : GridMajorizes := GridMajorization.antitone_grid_sum

lemma generalizedBinomial_pos (k j : ℕ) {a : ℝ} (ha : 0<a) :
    0<generalizedBinomial k j a := by
  unfold generalizedBinomial
  exact div_pos (Real.Gamma_pos_of_pos (by positivity))
    (mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.Gamma_pos_of_pos (by positivity)))

lemma generalizedBinomial_zero (k : ℕ) {a : ℝ} (ha : 0<a) : generalizedBinomial k 0 a=1 := by
  simp [generalizedBinomial, (Real.Gamma_pos_of_pos (show 0<a*k+1 by positivity)).ne']

lemma generalizedBinomial_self (k : ℕ) {a : ℝ} (ha : 0<a) : generalizedBinomial k k a=1 := by
  simp [generalizedBinomial, (Real.Gamma_pos_of_pos (show 0<a*k+1 by positivity)).ne']

lemma binomialSum_pos (k : ℕ) {a p q : ℝ} (ha : 0<a) (hp : 0<p) (hq : 0<q) :
    0<binomialSum k a p q := by
  unfold binomialSum
  apply Finset.sum_pos
  · intro j _
    exact mul_pos (mul_pos (generalizedBinomial_pos k j ha) (Real.rpow_pos_of_pos hp _))
      (Real.rpow_pos_of_pos hq _)
  · simp

/-- Exact normalized conjecture, using the independently certified grid theorem. -/
theorem normalized_converse (k : ℕ) {a p q : ℝ} (ha : 2 ≤ a) (hp : 0<p) (hq : 0<q)
    (hs : p+q=1) : 1 ≤ (2:ℝ)^(a-1)*binomialSum k a p q := by
  apply bound_of_log_convex (binomialSum_log_convex_of_grid gridMajorizes_proved k hp hq)
  · rw [binomialSum_one, hs, one_pow]
  · have h := binomialSum_two k p q
    rw [hs, one_pow] at h
    have hn : 0 ≤ (-p+q)^(2*k) := by
      rw [Nat.mul_comm 2 k, pow_mul]
      exact sq_nonneg ((-p+q)^k)
    linarith
  · exact ha
  · exact binomialSum_pos k (by linarith) hp hq

lemma binomialSum_scale (k : ℕ) (a : ℝ) {p q c : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hc : 0<c) :
    binomialSum k a (c*p) (c*q)=c^(a*k)*binomialSum k a p q := by
  unfold binomialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
  have hexp : a*(j:ℝ)+a*((k-j:ℕ):ℝ)=a*(k:ℝ) := by
    rw [Nat.cast_sub hjk]
    ring
  rw [Real.mul_rpow hc.le hp, Real.mul_rpow hc.le hq]
  calc
    generalizedBinomial k j a*(c^(a*j)*p^(a*j))*(c^(a*((k-j:ℕ):ℝ))*q^(a*((k-j:ℕ):ℝ))) =
        (c^(a*j)*c^(a*((k-j:ℕ):ℝ)))*
          (generalizedBinomial k j a*p^(a*j)*q^(a*((k-j:ℕ):ℝ))) := by ring
    _ = _ := by rw [← Real.rpow_add hc, hexp]

lemma binomialSum_endpoint_left (k : ℕ) {a p q : ℝ} (ha : 0<a)
    (hp : 0 ≤ p) (hq : 0 ≤ q) : q^(a*k) ≤ binomialSum k a p q := by
  have h := Finset.single_le_sum (fun j (_ : j∈Finset.range (k+1)) =>
    mul_nonneg (mul_nonneg (generalizedBinomial_pos k j ha).le (Real.rpow_nonneg hp (a*j)))
      (Real.rpow_nonneg hq (a*((k-j:ℕ):ℝ)))) (show 0∈Finset.range (k+1) by simp)
  simpa only [binomialSum, generalizedBinomial_zero k ha, Nat.cast_zero, mul_zero, Real.rpow_zero,
    mul_one, one_mul, Nat.sub_zero] using h

lemma binomialSum_endpoint_right (k : ℕ) {a p q : ℝ} (ha : 0<a)
    (hp : 0 ≤ p) (hq : 0 ≤ q) : p^(a*k) ≤ binomialSum k a p q := by
  have h := Finset.single_le_sum (fun j (_ : j∈Finset.range (k+1)) =>
    mul_nonneg (mul_nonneg (generalizedBinomial_pos k j ha).le (Real.rpow_nonneg hp (a*j)))
      (Real.rpow_nonneg hq (a*((k-j:ℕ):ℝ)))) (show k∈Finset.range (k+1) by simp)
  simpa only [binomialSum, generalizedBinomial_self k ha, Nat.sub_self, Nat.cast_zero, mul_zero,
    Real.rpow_zero, mul_one, one_mul] using h

/-- Gerhold–Simon Conjecture3.2 / MathDB352508, all real alpha≥2 and all x,y≥0. -/
theorem source_conjecture_352508 (k : ℕ) {a x y : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) : (x+y)^(a*k) ≤ (2:ℝ)^(a-1)*binomialSum k a x y := by
  have ha0 : 0<a := by linarith
  have hfac : 1 ≤ (2:ℝ)^(a-1) := Real.one_le_rpow (by norm_num) (by linarith)
  by_cases hx0 : x=0
  · subst x
    have h := binomialSum_endpoint_left k ha0 (le_refl 0) hy
    have hn := Real.rpow_nonneg hy (a*k)
    simp only [zero_add]
    nlinarith
  by_cases hy0 : y=0
  · subst y
    have h := binomialSum_endpoint_right k ha0 hx (le_refl 0)
    have hn := Real.rpow_nonneg hx (a*k)
    simp only [add_zero]
    nlinarith
  have hxp : 0<x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hyp : 0<y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hc : 0<x+y := add_pos hxp hyp
  have hp : 0<x/(x+y) := div_pos hxp hc
  have hq : 0<y/(x+y) := div_pos hyp hc
  have hs : x/(x+y)+y/(x+y)=1 := by field_simp
  have h := normalized_converse k ha hp hq hs
  have hh := binomialSum_scale k a hp.le hq.le hc
  rw [mul_div_cancel₀ x hc.ne', mul_div_cancel₀ y hc.ne'] at hh
  have hm := mul_le_mul_of_nonneg_left h (Real.rpow_pos_of_pos hc (a*k)).le
  rw [mul_one] at hm
  nlinarith

end FractionalBinomial
