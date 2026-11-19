import Cayley382145Finite
import Cayley382145Projection
import Cayley382145Lattice

/-! # MathDB 382145: the Dickenstein–Nill Cayley decomposition conjecture (literal endpoint)

`dickensteinNill_cayley`: for every `n` and every full-dimensional lattice polytope
`P = conv V ⊆ ℝ^n` with native Q-codegree `μ(P) > (n+1)/2`, `P` is a nontrivial Cayley sum of
lattice polytopes in `ℝ^k` with `k ≤ ⌊2(n+1-μ(P))⌋`. No external Cayley theorem is assumed. -/

namespace Cayley382145

open Finset

theorem dickensteinNill_cayley (n : ℕ) (P : Set (Fin n → ℝ)) (V : Finset (Fin n → ℤ))
    (hP : P = latticeHull V) (hfull : affineSpan ℝ P = ⊤)
    (hμ : ((n : ℝ) + 1) / 2 < qCodegree P) :
    ∃ k t : ℕ, (k : ℤ) ≤ ⌊2 * ((n : ℝ) + 1 - qCodegree P)⌋ ∧ IsCayleySumIn P k t := by
  subst hP
  classical
  have hV := nonempty_of_full hfull
  have hfin := facetNormals_finite hfull
  set N := hfin.toFinset with hN
  have hmemN : ∀ a, a ∈ N ↔ IsFacetNormal (latticeHull V) a := fun a => by simp [hN]
  let α : N → Fin n → ℝ := fun i => castPt (i : Fin n → ℤ)
  let βr : N → ℝ := fun i => facetOffset (latticeHull V) (i : Fin n → ℤ)
  have hT : {s : ℝ | 0 < s ∧ (adjointSet (latticeHull V) s).Nonempty} = shiftSet α βr := by
    ext s
    constructor
    · rintro ⟨hs, x, hx⟩
      exact ⟨hs, x, fun i => hx i ((hmemN i).mp i.2)⟩
    · rintro ⟨hs, x, hx⟩
      exact ⟨hs, x, fun a ha => hx ⟨a, (hmemN a).mpr ha⟩⟩
  have hq : qCodegree (latticeHull V) = (sSup (shiftSet α βr))⁻¹ := by
    rw [qCodegree, hT]
  set σ := sSup (shiftSet α βr) with hσdef
  rw [hq] at hμ ⊢
  have hσpos : 0 < σ := by
    have h1 : 0 < σ⁻¹ := lt_of_le_of_lt (by positivity) hμ
    exact inv_pos.mp h1
  have hne : (shiftSet α βr).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [hσdef, h, Real.sSup_empty] at hσpos
    exact lt_irrefl 0 hσpos
  have hbdd : BddAbove (shiftSet α βr) := by
    by_contra h
    rw [hσdef, Real.sSup_of_not_bddAbove h] at hσpos
    exact lt_irrefl 0 hσpos
  obtain ⟨y, ⟨hy0, hy1, hya, hyb⟩, hind⟩ := exists_min_cert α βr hne hbdd
  rw [← hσdef] at hyb
  have hoff : ∀ i : N, ∃ b : ℤ, facetOffset (latticeHull V) (i : Fin n → ℤ) = b ∧
      ∀ v ∈ V, b ≤ zDot (i : Fin n → ℤ) v := by
    intro i
    obtain ⟨v₀, -, h1, h2, -⟩ := facetOffset_latticeHull hV (i : Fin n → ℤ)
    exact ⟨zDot (i : Fin n → ℤ) v₀, h1, h2⟩
  choose βz hβz hβnn using hoff
  have hsum : ∀ v ∈ V, ∑ i, y i * ((zDot (i : Fin n → ℤ) v - βz i : ℤ) : ℝ) = σ := by
    intro v _
    have e : ∀ i : N, ((zDot (i : Fin n → ℤ) v - βz i : ℤ) : ℝ) = rdot (α i) (castPt v) - βr i := by
      intro i
      show ((zDot (i : Fin n → ℤ) v - βz i : ℤ) : ℝ) =
        intDot (i : Fin n → ℤ) (castPt v) - facetOffset (latticeHull V) (i : Fin n → ℤ)
      rw [Int.cast_sub, intDot_castPt, hβz i]
    simp only [e, mul_sub, Finset.sum_sub_distrib]
    rw [← rdot_sum, hya, rdot_zero_left, hyb]
    ring
  have hprim : ∀ i : N, (i : Fin n → ℤ) ≠ 0 := fun i => ((hmemN i).mp i.2).1.ne_zero
  obtain ⟨J, hJne, hJbound, h01, hone, hzero, hhitJ⟩ :=
    projection_core (fun i : N => (i : Fin n → ℤ)) βz V y σ hσpos hy0 hy1 hya hind hβnn hsum
      (fun c hc d => exists_zDot_ne_of_full hfull hc d) hprim hμ
  set t := J.card with ht
  let e : Fin t ≃ J := J.equivFin.symm
  let A : (Fin n → ℤ) →ₗ[ℤ] (Fin t → ℤ) :=
    { toFun := fun x j => zDot (((e j : N) : Fin n → ℤ)) x
      map_add' := fun x y => by
        funext j
        simp only [zDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        funext j
        simp only [zDot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring }
  let cvec : Fin t → ℤ := fun j => βz (e j)
  have hAv : ∀ v (j : Fin t), (A v - cvec) j = zDot (((e j : N) : Fin n → ℤ)) v - βz (e j) :=
    fun v j => rfl
  have hsome : ∀ v ∈ V, ∀ j₁ : Fin t, zDot (((e j₁ : N) : Fin n → ℤ)) v - βz (e j₁) = 1 →
      A v - cvec = zVertex (some j₁) := by
    intro v hv j₁ h1
    funext j
    rw [hAv]
    by_cases hj : j = j₁
    · subst hj
      simpa [zVertex] using h1
    · have hne' : (e j : N) ≠ (e j₁ : N) := fun h => hj (e.injective (Subtype.ext h))
      rcases h01 v hv (e j) (e j).2 with h0 | h1'
      · simpa [zVertex, hj] using h0
      · exact absurd (hone v hv (e j) (e j).2 (e j₁) (e j₁).2 h1' h1) hne'
  have himg : ∀ v ∈ V, ∃ i : Option (Fin t), A v - cvec = zVertex i := by
    intro v hv
    by_cases hall : ∀ j ∈ J, zDot ((j : N) : Fin n → ℤ) v - βz j = 0
    · refine ⟨none, ?_⟩
      funext j
      rw [hAv]
      exact hall (e j) (e j).2
    · push Not at hall
      obtain ⟨j₀, hj₀, hne⟩ := hall
      have h1 : zDot ((j₀ : N) : Fin n → ℤ) v - βz j₀ = 1 := (h01 v hv j₀ hj₀).resolve_left hne
      refine ⟨some (e.symm ⟨j₀, hj₀⟩), hsome v hv _ ?_⟩
      rw [Equiv.apply_symm_apply]
      exact h1
  have hhitA : ∀ i : Option (Fin t), ∃ v ∈ V, A v - cvec = zVertex i := by
    intro i
    cases i with
    | none =>
      obtain ⟨v, hv, hv0⟩ := hzero
      exact ⟨v, hv, funext fun j => by rw [hAv]; exact hv0 (e j) (e j).2⟩
    | some j₁ =>
      obtain ⟨v, hv, hv1⟩ := hhitJ (e j₁) (e j₁).2
      exact ⟨v, hv, hsome v hv j₁ hv1⟩
  have ht1 : 1 ≤ t := Finset.card_pos.mpr hJne
  obtain ⟨k, hkt, hcay⟩ := cayley_of_projection V A cvec ht1 himg hhitA
  refine ⟨k, t, ?_, hcay⟩
  rw [Int.le_floor]
  have hk : (k : ℝ) + t = n := by exact_mod_cast hkt
  push_cast
  linarith

/-- MathDB 382145 holds in the literal native formulation. -/
theorem dickensteinNillCayleyConjecture_holds : DickensteinNillCayleyConjecture :=
  fun n P V hP hfull hμ => dickensteinNill_cayley n P V hP hfull hμ

end Cayley382145
