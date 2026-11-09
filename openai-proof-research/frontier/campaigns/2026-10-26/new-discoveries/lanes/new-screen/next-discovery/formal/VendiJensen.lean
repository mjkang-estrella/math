import Mathlib

open Finset Set Real
namespace VendiJensen

lemma convexOn_rpow_nonpos (p : ℝ) (hp : p≤0) :
    ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x^p) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hm : 0<a*x+b*y := (convex_Ioi (0:ℝ)) hx hy ha hb hab
  have hl := strictConcaveOn_log_Ioi.concaveOn.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hl ⊢
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy, Real.rpow_def_of_pos hm]
  calc
    _ ≤ Real.exp (a*(Real.log x*p)+b*(Real.log y*p)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hp (sub_nonneg.mpr hl)]
    _ ≤ _ := convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

/-- Finite weighted Jensen on the positive spectrum, with no full-rank hypothesis. -/
theorem spectral_energy_bound {I J : Type*} [Fintype I]
    (s : Finset J) (lam : J → ℝ) (u : I → J → ℝ)
    (hlam : ∀ j∈s,0<lam j) (hu : ∀ i j,j∈s → 0≤u i j)
    (hdiag : ∀ i, ∑j∈s,lam j*u i j=1)
    (hcol : ∀ j∈s,∑i,u i j=1)
    (q : ℝ) (hq : q<1) :
    (∑i,(∑j∈s,(lam j)^2*u i j)^(q-1)) ≤ ∑j∈s,(lam j)^q := by
  classical
  have hrow : ∀ i, (∑j∈s,(lam j)^2*u i j)^(q-1) ≤
      ∑j∈s,((lam j)^q)*u i j := by
    intro i
    have hj := (convexOn_rpow_nonpos (q-1) (by linarith)).map_sum_le
      (t:=s) (w:=fun j=>lam j*u i j) (p:=lam)
      (by intro j hj; exact mul_nonneg (hlam j hj).le (hu i j hj))
      (hdiag i) (by intro j hj; exact hlam j hj)
    simp only [smul_eq_mul] at hj
    convert hj using 1
    · congr 1
      apply Finset.sum_congr rfl
      intro j hj
      ring
    · apply Finset.sum_congr rfl
      intro j hj
      have hp : lam j * (lam j)^(q-1)=(lam j)^q := by
        calc
          _ = (lam j)^(1:ℝ)*(lam j)^(q-1) := by rw [Real.rpow_one]
          _ = (lam j)^(1+(q-1)) := (Real.rpow_add (hlam j hj) _ _).symm
          _ = _ := by congr 1; ring
      rw [mul_assoc, mul_comm (u i j), ← mul_assoc, hp]
  calc
    _ ≤ ∑i,∑j∈s,((lam j)^q)*u i j := Finset.sum_le_sum (fun i _=>hrow i)
    _ = ∑j∈s,(lam j)^q := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.mul_sum, hcol j hj, mul_one]

lemma energy_pos {J : Type*} (s : Finset J) (lam u : J → ℝ)
    (hlam : ∀ j∈s,0<lam j) (hu : ∀ j∈s,0≤u j)
    (hdiag : ∑j∈s,lam j*u j=1) : 0<∑j∈s,(lam j)^2*u j := by
  have hs : (0:ℝ)<∑j∈s,lam j*u j := by rw [hdiag]; norm_num
  obtain ⟨j,hj,hp⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun j hj => mul_nonneg (hlam j hj).le (hu j hj))).mp hs
  apply Finset.sum_pos'
  · intro j hj
    exact mul_nonneg (sq_nonneg _) (hu j hj)
  · refine ⟨j,hj,?_⟩
    have hjlam := hlam j hj
    have hju : 0<u j := by nlinarith
    positivity

/-- The row-energy comparison supplies the support-power inequality at arbitrary rank. -/
theorem spectral_row_bound {I J : Type*} [Fintype I]
    (s : Finset J) (lam : J → ℝ) (u : I → J → ℝ)
    (hlam : ∀ j∈s,0<lam j) (hu : ∀ i j,j∈s → 0≤u i j)
    (hdiag : ∀ i, ∑j∈s,lam j*u i j=1)
    (hcol : ∀ j∈s,∑i,u i j=1)
    (r : I → ℝ) (hr : ∀ i,(∑j∈s,(lam j)^2*u i j)≤r i)
    (q : ℝ) (hq : q<1) :
    (∑i,(r i)^(q-1)) ≤ ∑j∈s,(lam j)^q := by
  calc
    _ ≤ ∑i,(∑j∈s,(lam j)^2*u i j)^(q-1) := by
      apply Finset.sum_le_sum
      intro i _
      exact Real.rpow_le_rpow_of_nonpos
        (energy_pos s lam (u i) hlam (hu i) (hdiag i)) (hr i) (by linarith)
    _ ≤ _ := spectral_energy_bound s lam u hlam hu hdiag hcol q hq

lemma min_le_energy {J : Type*} (s : Finset J) (lam u : J → ℝ)
    (hlam : ∀ j∈s,0<lam j) (hu : ∀ j∈s,0≤u j)
    (hdiag : ∑j∈s,lam j*u j=1) (m : ℝ) (hm : ∀ j∈s,m≤lam j) :
    m≤∑j∈s,(lam j)^2*u j := by
  calc
    m = ∑j∈s,m*(lam j*u j) := by rw [← Finset.mul_sum,hdiag,mul_one]
    _ ≤ ∑j∈s,lam j*(lam j*u j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (hm j hj) (mul_nonneg (hlam j hj).le (hu j hj))
    _ = _ := by apply Finset.sum_congr rfl; intro j _; ring

end VendiJensen
