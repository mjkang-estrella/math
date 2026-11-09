import Literal
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.Dual.Lemmas
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace FullereneGeometry
def normalMap : E →ₗ[ℝ] (E →ₗ[ℝ] ℝ) where
  toFun := normal
  map_add' a b := by
    apply LinearMap.ext; intro x
    change dot (a + b) x = dot a x + dot b x
    simp [dot, add_mul, Finset.sum_add_distrib]
  map_smul' r a := by
    apply LinearMap.ext; intro x
    change dot (r • a) x = r * dot a x
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    congr 1; ext k; ring

theorem active_independent_triple {n : ℕ} (q : Fin n → E) (x : E)
    (hk : ∀ d : E, (∀ i, dot (q i) x = 1 → dot (q i) d = 0) → d = 0) :
    ∃ ids : Fin 3 → Fin n, (∀ k, dot (q (ids k)) x = 1) ∧
      LinearIndependent ℝ (fun k => q (ids k)) := by
  classical
  let s : Set (E →ₗ[ℝ] ℝ) := {f | ∃ i, dot (q i) x = 1 ∧ f = normal (q i)}
  have hs : Submodule.span ℝ s = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro d hd
    by_contra h
    apply hd
    apply hk d
    intro i hi
    by_contra hne
    exact h ⟨normal (q i), ⟨i, hi, rfl⟩, hne⟩
  let b := Module.Basis.ofSpan hs.ge
  let I := ↥((linearIndepOn_empty ℝ id).extend (Set.empty_subset s))
  let : Fintype I := Fintype.ofFinite I
  have hb : Fintype.card I = 3 := by
    rw [← Module.finrank_eq_card_basis b, Subspace.dual_finrank_eq]
    exact Module.finrank_fin_fun ℝ
  let c := b.reindex (Fintype.equivFinOfCardEq hb)
  have hc : ∀ k, c k ∈ s := by
    intro k
    apply Module.Basis.ofSpan_subset hs.ge
    exact ⟨(Fintype.equivFinOfCardEq hb).symm k, by simp [c, b]⟩
  choose ids ha he using hc
  refine ⟨ids, ha, ?_⟩
  apply LinearIndependent.of_comp normalMap
  have hh : (normalMap ∘ fun k => q (ids k)) = c := by
    funext k
    exact (he k).symm
  rw [hh]
  exact c.linearIndependent

theorem extreme_active_independent_triple {n : ℕ} (q : Fin n → E) (x : E)
    (hx : x ∈ (poly q).extremePoints ℝ) :
    ∃ ids : Fin 3 → Fin n, (∀ k, dot (q (ids k)) x = 1) ∧
      LinearIndependent ℝ (fun k => q (ids k)) :=
  active_independent_triple q x (active_kernel_trivial q x hx)

/-- This interface requires completeness for every independent active triple,
not just feasibility and extremality of the listed points. -/
theorem complete_vertices_of_triple_certificates {n m : ℕ} (q : Fin n → E)
    (p : Fin m → E)
    (complete : ∀ (ids : Fin 3 → Fin n), LinearIndependent ℝ (fun k => q (ids k)) →
      ∀ x ∈ poly q, (∀ k, dot (q (ids k)) x = 1) → x ∈ Set.range p)
    (listed : ∀ j, p j ∈ poly q ∧ ∃ ids : Fin 3 → Fin n,
      (∀ k, dot (q (ids k)) (p j) = 1) ∧
      (∀ y : E, (∀ k, dot (q (ids k)) y = 1) → y = p j)) :
    (poly q).extremePoints ℝ = Set.range p := by
  ext x
  constructor
  · intro hx
    obtain ⟨ids, ha, hi⟩ := extreme_active_independent_triple q x hx
    exact complete ids hi x hx.1 ha
  · rintro ⟨j, rfl⟩
    obtain ⟨hf, ids, ha, hu⟩ := listed j
    exact extreme_of_active_unique q (p j) hf ids ha hu
theorem hull_of_complete_vertices {n : ℕ} (q : Fin n → E)
    (hc : IsCompact (poly q)) {m : ℕ} (p : Fin m → E)
    (hv : (poly q).extremePoints ℝ = Set.range p) :
    poly q = convexHull ℝ (Set.range p) := by
  have h := closure_convexHull_extremePoints hc (poly_convex q)
  rw [hv, ((Set.finite_range p).isClosed_convexHull ℝ).closure_eq] at h
  exact h.symm

theorem section_hull_of_complete_vertices {n : ℕ} (q : Fin n → E)
    (hc : IsCompact (poly q)) {m : ℕ} (p : Fin m → E)
    (hv : (poly q).extremePoints ℝ = Set.range p) (i : Fin n) :
    facetSection q i = convexHull ℝ {x ∈ Set.range p | dot (q i) x = 1} := by
  have hs : IsClosed (facetSection q i) :=
    (poly_closed q).inter (isClosed_eq (dot_continuous (q i)) continuous_const)
  have hcomp : IsCompact (facetSection q i) := hc.of_isClosed_subset hs (fun _ h => h.1)
  have hconv : Convex ℝ (facetSection q i) := by
    intro x hx y hy a b ha hb hab
    refine ⟨poly_convex q hx.1 hy.1 ha hb hab, ?_⟩
    change (normal (q i)) (a • x + b • y) = 1
    rw [map_add, map_smul, map_smul]
    change a * dot (q i) x + b * dot (q i) y = 1
    rw [hx.2, hy.2]; linarith
  have he : (facetSection q i).extremePoints ℝ = {x ∈ Set.range p | dot (q i) x = 1} := by
    ext x
    constructor
    · intro hx
      exact ⟨hv ▸ (facetSection_extreme q i).extremePoints_subset_extremePoints hx, hx.1.2⟩
    · rintro ⟨hx, hi⟩
      have hx' : x ∈ (poly q).extremePoints ℝ := hv.symm ▸ hx
      refine ⟨⟨hx'.1, hi⟩, ?_⟩
      intro y hy z hz hseg
      exact hx'.2 hy.1 hz.1 hseg
  have h := closure_convexHull_extremePoints hcomp hconv
  rw [he, (((Set.finite_range p).subset (fun _ h => h.1)).isClosed_convexHull ℝ).closure_eq] at h
  exact h.symm
end FullereneGeometry
