import Mathlib

open Polynomial

namespace BergmanRootAllocation

lemma reverse_multiset_prod (s : Multiset ℂ[X]) :
    s.prod.reverse = (s.map Polynomial.reverse).prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using (Polynomial.reverse_C (1 : ℂ))
  | cons a s ih => simp [ih]

lemma reverse_linear (a : ℂ) (ha : a ≠ 0) :
    (X - C a).reverse = C (-a) * (X - C a⁻¹) := by
  have hx : (X : ℂ[X]).reverse = 1 := by
    calc
      (X : ℂ[X]).reverse = (1 : ℂ[X]).reverse := by simpa using Polynomial.reverse_mul_X (1 : ℂ[X])
      _ = 1 := by simpa using Polynomial.reverse_C (1 : ℂ)
  rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.reverse_add_C, hx]
  simp only [natDegree_X, pow_one]
  rw [mul_sub, ← C_mul]
  simp [ha]
  ring

lemma reverse_linear_roots (a : ℂ) (ha : a ≠ 0) :
    (X - C a).reverse.roots = {a⁻¹} := by
  rw [reverse_linear a ha, roots_C_mul _ (neg_ne_zero.mpr ha), roots_X_sub_C]

theorem roots_reverse (p : ℂ[X]) (h0 : p.coeff 0 ≠ 0) :
    p.reverse.roots = p.roots.map (fun z => z⁻¹) := by
  have hp : p ≠ 0 := by intro he; simp [he] at h0
  have hn (a : ℂ) (ha : a ∈ p.roots) : a ≠ 0 := by
    intro he
    have hr := (Polynomial.mem_roots hp).mp ha
    exact h0 (by simpa [he, Polynomial.IsRoot, Polynomial.coeff_zero_eq_eval_zero] using hr)
  have hf := (IsAlgClosed.splits p).eq_prod_roots
  have he := congrArg Polynomial.reverse hf
  rw [Polynomial.reverse_mul_of_domain, Polynomial.reverse_C,
    reverse_multiset_prod, Multiset.map_map] at he
  rw [he, roots_C_mul _ (Polynomial.leadingCoeff_ne_zero.mpr hp)]
  rw [Polynomial.roots_multiset_prod]
  · rw [Multiset.bind_map]
    simp_rw [Function.comp_apply]
    have hbind : (p.roots.bind fun a => (X - C a).reverse.roots) =
        p.roots.bind (fun a => ({a⁻¹} : Multiset ℂ)) := by
      apply Multiset.bind_congr
      intro a ha
      exact reverse_linear_roots a (hn a ha)
    rw [hbind]
    simp
  · intro hq
    rcases Multiset.mem_map.mp hq with ⟨a, _, heq⟩
    exact Polynomial.X_sub_C_ne_zero a (Polynomial.reverse_eq_zero.mp heq)

/-- Reciprocal pairing with multiplicities gives exactly half of the roots in the
punctured unit disc, when the polynomial has no root on the unit circle. -/
theorem reciprocal_root_allocation (p : ℂ[X]) (k : ℕ)
    (hdeg : p.natDegree = 2*k) (hrev : p.reverse = p) (h0 : p.coeff 0 ≠ 0)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 → p.eval z ≠ 0) :
    (p.roots.filter (fun z => z ≠ 0 ∧ ‖z‖ < 1)).card = k := by
  classical
  have hp : p ≠ 0 := by intro he; simp [he] at h0
  have hn (z : ℂ) (hz : z ∈ p.roots) : z ≠ 0 := by
    intro he
    have hr := (Polynomial.mem_roots hp).mp hz
    exact h0 (by simpa [he, Polynomial.IsRoot, Polynomial.coeff_zero_eq_eval_zero] using hr)
  have hnorm (z : ℂ) (hz : z ∈ p.roots) : ‖z‖ ≠ 1 := by
    intro he
    exact hcircle z he ((Polynomial.mem_roots hp).mp hz)
  have hmap : p.roots.map (fun z => z⁻¹) = p.roots := by
    rw [← roots_reverse p h0, hrev]
  have hfilters :
      (p.roots.filter (fun z => z ≠ 0 ∧ ‖z‖ < 1)).card =
      (p.roots.filter (fun z => 1 < ‖z‖)).card := by
    conv_lhs => rw [← hmap]
    rw [Multiset.filter_map, Multiset.card_map]
    congr 1
    apply Multiset.filter_congr
    intro z hz
    dsimp only [Function.comp_def]
    rw [norm_inv]
    constructor
    · intro h
      exact (inv_lt_one₀ (norm_pos_iff.mpr (hn z hz))).mp h.2
    · intro h
      exact ⟨inv_ne_zero (hn z hz), (inv_lt_one₀ (norm_pos_iff.mpr (hn z hz))).mpr h⟩
  have hcompl :
      p.roots.filter (fun z => ¬ (z ≠ 0 ∧ ‖z‖ < 1)) =
      p.roots.filter (fun z => 1 < ‖z‖) := by
    apply Multiset.filter_congr
    intro z hz
    have hz0 := hn z hz
    have hz1 := hnorm z hz
    constructor
    · intro h
      have hh : ¬ ‖z‖ < 1 := fun hlt => h ⟨hz0,hlt⟩
      exact lt_of_le_of_ne (le_of_not_gt hh) (Ne.symm hz1)
    · intro h hh
      exact (not_lt_of_ge (le_of_lt h)) hh.2
  have hsum := congrArg Multiset.card
    (Multiset.filter_add_not (fun z : ℂ => z ≠ 0 ∧ ‖z‖ < 1) p.roots)
  rw [Multiset.card_add, hcompl, ← hfilters] at hsum
  have hcard := (IsAlgClosed.splits p).natDegree_eq_card_roots
  omega

end BergmanRootAllocation
