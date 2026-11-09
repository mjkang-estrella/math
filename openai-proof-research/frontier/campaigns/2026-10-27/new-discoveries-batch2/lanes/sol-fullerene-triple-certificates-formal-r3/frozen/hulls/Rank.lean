import Literal
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
end FullereneGeometry
