import Cayley382145Main

/-! # MathDB 382145 — reviewer r2 independent audit module (SEPARATELY LABELED)

Written by the independent r2 replay reviewer AFTER the nine-module author baseline replay.
It is not part of the author's frozen appendix and changes none of the author's declarations.

1. `adjoint_barycentre`: native-scope bridge. For every full-dimensional lattice polytope the
   barycentre of the generators lies in `P^(1/|V|)`, so the shift set `{s > 0 : P^(s) ≠ ∅}` is
   never empty (the empty-set junk value of `sSup` never arises).
2. `qCodegree_eq_zero_of_unbounded`: an unbounded shift set gives `qCodegree = 0`, matching the
   native convention `1/∞ = 0`; the strict hypothesis then fails.
3. `realExt_mul_symm`, `realExt_symm_mul`: the real extension of the integral isomorphism is an
   invertible real matrix whose inverse is the real extension of the integral inverse.
4. `rank_split`: an isomorphism `ℤ^n ≅ ℤ^k × ℤ^t` forces `n = k + t`.
5. `dickensteinNill_cayley_expanded`: the endpoint with all of this data made explicit.
-/

namespace Cayley382145
namespace ReviewR2

open Finset
open scoped Matrix

theorem isPrimitive_ne_zero {n : ℕ} {a : Fin n → ℤ} (ha : IsPrimitive a) : a ≠ 0 := by
  rintro rfl
  have h := ha 2 (fun _ => dvd_zero 2)
  rw [Int.isUnit_iff] at h
  omega

theorem adjoint_barycentre {n : ℕ} {V : Finset (Fin n → ℤ)}
    (hfull : affineSpan ℝ (latticeHull V) = ⊤) :
    0 < 1 / (V.card : ℝ) ∧
      ((1 / (V.card : ℝ)) • ∑ v ∈ V, castPt v) ∈ adjointSet (latticeHull V) (1 / (V.card : ℝ)) := by
  classical
  have hV := nonempty_of_full hfull
  have hc : (0 : ℝ) < (V.card : ℝ) := by exact_mod_cast hV.card_pos
  have hc0 : (V.card : ℝ) ≠ 0 := ne_of_gt hc
  refine ⟨by positivity, fun a ha => ?_⟩
  obtain ⟨v₀, _, hoff, hmin, -⟩ := facetOffset_latticeHull hV a
  obtain ⟨w, hwV, hw⟩ := exists_zDot_ne_of_full hfull (isPrimitive_ne_zero ha.1) (zDot a v₀)
  have hx : intDot a ((1 / (V.card : ℝ)) • ∑ v ∈ V, castPt v) =
      (1 / (V.card : ℝ)) * ∑ v ∈ V, (zDot a v : ℝ) := by
    rw [← intDotL_apply, map_smul, map_sum, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [intDotL_apply, intDot_castPt]
  have hint : (V.card : ℤ) * zDot a v₀ + 1 ≤ ∑ v ∈ V, zDot a v := by
    have h1 : ∀ v ∈ V, 0 ≤ zDot a v - zDot a v₀ := fun v hv => sub_nonneg.mpr (hmin v hv)
    have h2 : 1 ≤ zDot a w - zDot a v₀ := by
      have := hmin w hwV
      omega
    have h3 : zDot a w - zDot a v₀ ≤ ∑ v ∈ V, (zDot a v - zDot a v₀) :=
      Finset.single_le_sum h1 hwV
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h3
    try push_cast at h3
    linarith
  have hreal : (V.card : ℝ) * (zDot a v₀ : ℝ) + 1 ≤ ∑ v ∈ V, (zDot a v : ℝ) := by
    exact_mod_cast hint
  rw [hoff, hx, one_div_mul_eq_div, le_div_iff₀ hc, add_mul, one_div_mul_cancel hc0]
  linarith [hreal, mul_comm (V.card : ℝ) (zDot a v₀ : ℝ)]

theorem shiftSet_nonempty {n : ℕ} {V : Finset (Fin n → ℤ)}
    (hfull : affineSpan ℝ (latticeHull V) = ⊤) :
    {s : ℝ | 0 < s ∧ (adjointSet (latticeHull V) s).Nonempty}.Nonempty := by
  obtain ⟨h1, h2⟩ := adjoint_barycentre hfull
  exact ⟨_, h1, _, h2⟩

theorem qCodegree_eq_zero_of_unbounded {n : ℕ} (P : Set (Fin n → ℝ))
    (h : ¬ BddAbove {s : ℝ | 0 < s ∧ (adjointSet P s).Nonempty}) : qCodegree P = 0 := by
  unfold qCodegree
  rw [Real.sSup_of_not_bddAbove h, inv_zero]

theorem realExt_mul_of_comp {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (f : (ι → ℤ) →ₗ[ℤ] (κ → ℤ)) (h : (κ → ℤ) →ₗ[ℤ] (ι → ℤ)) (hfh : f.comp h = LinearMap.id) :
    realExt f * realExt h = 1 := by
  have hAB : LinearMap.toMatrix' f * LinearMap.toMatrix' h = 1 := by
    rw [← LinearMap.toMatrix'_comp, hfh, LinearMap.toMatrix'_id]
  have hm : (LinearMap.toMatrix' f).map (Int.cast : ℤ → ℝ) * (LinearMap.toMatrix' h).map (Int.cast : ℤ → ℝ)
      = (LinearMap.toMatrix' f * LinearMap.toMatrix' h).map (Int.cast : ℤ → ℝ) :=
    (Matrix.map_mul (f := Int.castRingHom ℝ)).symm
  unfold realExt
  rw [hm, hAB]
  exact Matrix.map_one _ Int.cast_zero Int.cast_one

theorem realExt_mul_symm {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (g : (ι → ℤ) ≃ₗ[ℤ] (κ → ℤ)) :
    realExt (g : (ι → ℤ) →ₗ[ℤ] (κ → ℤ)) * realExt (g.symm : (κ → ℤ) →ₗ[ℤ] (ι → ℤ)) = 1 :=
  realExt_mul_of_comp _ _ (LinearMap.ext fun x => by simp)

theorem realExt_symm_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (g : (ι → ℤ) ≃ₗ[ℤ] (κ → ℤ)) :
    realExt (g.symm : (κ → ℤ) →ₗ[ℤ] (ι → ℤ)) * realExt (g : (ι → ℤ) →ₗ[ℤ] (κ → ℤ)) = 1 :=
  realExt_mul_of_comp _ _ (LinearMap.ext fun x => by simp)

theorem rank_split {n k t : ℕ} (g : (Fin n → ℤ) ≃ₗ[ℤ] (Fin k ⊕ Fin t → ℤ)) : k + t = n := by
  have h := g.finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_sum] at h
  omega

theorem dickensteinNill_cayley_expanded (n : ℕ) (V : Finset (Fin n → ℤ))
    (hfull : affineSpan ℝ (latticeHull V) = ⊤)
    (hμ : ((n : ℝ) + 1) / 2 < qCodegree (latticeHull V)) :
    ∃ (k t : ℕ) (g : (Fin n → ℤ) ≃ₗ[ℤ] (Fin k ⊕ Fin t → ℤ)) (z : Fin n → ℤ)
      (Q : Option (Fin t) → Finset (Fin k → ℤ)),
      k + t = n ∧ (k : ℤ) ≤ ⌊2 * ((n : ℝ) + 1 - qCodegree (latticeHull V))⌋ ∧ 1 ≤ t ∧
      realExt (g : (Fin n → ℤ) →ₗ[ℤ] (Fin k ⊕ Fin t → ℤ)) *
          realExt (g.symm : (Fin k ⊕ Fin t → ℤ) →ₗ[ℤ] (Fin n → ℤ)) = 1 ∧
      realExt (g.symm : (Fin k ⊕ Fin t → ℤ) →ₗ[ℤ] (Fin n → ℤ)) *
          realExt (g : (Fin n → ℤ) →ₗ[ℤ] (Fin k ⊕ Fin t → ℤ)) = 1 ∧
      (∀ p : Fin n → ℤ, realExt (g : (Fin n → ℤ) →ₗ[ℤ] (Fin k ⊕ Fin t → ℤ)) *ᵥ castPt p =
          castPt (g p)) ∧
      (∀ i, (Q i).Nonempty) ∧
      (fun x => realExt (g : (Fin n → ℤ) →ₗ[ℤ] (Fin k ⊕ Fin t → ℤ)) *ᵥ (x - castPt z)) ''
          latticeHull V = convexHull ℝ (⋃ i, cayleyEmbed i '' latticeHull (Q i)) := by
  obtain ⟨k, t, hk, ht, g, z, Q, hQ, himg⟩ :=
    dickensteinNill_cayley n (latticeHull V) V rfl hfull hμ
  exact ⟨k, t, g, z, Q, rank_split g, hk, ht, realExt_mul_symm g, realExt_symm_mul g,
    fun p => realExt_mulVec_castPt _ p, hQ, himg⟩

end ReviewR2
end Cayley382145

#print axioms Cayley382145.ReviewR2.adjoint_barycentre
#print axioms Cayley382145.ReviewR2.shiftSet_nonempty
#print axioms Cayley382145.ReviewR2.qCodegree_eq_zero_of_unbounded
#print axioms Cayley382145.ReviewR2.realExt_mul_symm
#print axioms Cayley382145.ReviewR2.realExt_symm_mul
#print axioms Cayley382145.ReviewR2.rank_split
#print axioms Cayley382145.ReviewR2.dickensteinNill_cayley_expanded
