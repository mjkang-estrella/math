module
public import URMatchingSurvivorGraph
public import URMatchingBase
@[expose] public section
namespace URMatching
open scoped Classical
theorem permutation_degree_bound {N : ℕ} (σ : PermutationTuples N 100) :
    DegreeBound (permutationGraph σ) 100 := by
  classical
  intro v
  cases v with
  | inl x =>
    let E := Finset.univ.image (fun c : Fin 100 => (Sum.inr (σ c x) : BipartiteVertex N))
    have hs : (Finset.univ.filter ((permutationGraph σ).Adj (Sum.inl x))) ⊆ E := by
      intro v hv
      have ha := (Finset.mem_filter.mp hv).2
      cases v with
      | inl z => exact False.elim ha
      | inr y =>
        obtain ⟨c,hc⟩ := ha
        exact Finset.mem_image.mpr ⟨c,Finset.mem_univ _,congrArg Sum.inr hc⟩
    exact (Finset.card_le_card hs).trans (by simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin 100))) (f := fun c => (Sum.inr (σ c x) : BipartiteVertex N)))
  | inr y =>
    let E := Finset.univ.image (fun c : Fin 100 => (Sum.inl ((σ c).symm y) : BipartiteVertex N))
    have hs : (Finset.univ.filter ((permutationGraph σ).Adj (Sum.inr y))) ⊆ E := by
      intro v hv
      have ha := (Finset.mem_filter.mp hv).2
      cases v with
      | inr z => exact False.elim ha
      | inl x =>
        obtain ⟨c,hc⟩ := ha
        apply Finset.mem_image.mpr
        refine ⟨c,Finset.mem_univ _,?_⟩
        exact congrArg Sum.inl ((σ c).symm_apply_eq.mpr hc.symm)
    exact (Finset.card_le_card hs).trans (by simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin 100))) (f := fun c => (Sum.inl ((σ c).symm y) : BipartiteVertex N)))

theorem induced_degree_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Set V) [Fintype P] (d : ℕ) (hd : DegreeBound G d) :
    DegreeBound (inducedGraph G P) d := by
  classical
  intro v
  let A := Finset.univ.filter ((inducedGraph G P).Adj v)
  have hs : A.image Subtype.val ⊆ Finset.univ.filter (G.Adj v.val) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
  have he : (A.image Subtype.val).card = A.card := Finset.card_image_of_injective _ Subtype.val_injective
  exact (he ▸ Finset.card_le_card hs).trans (hd v.val)

noncomputable instance survivor_fintype {N : ℕ} (h : ℕ) (σ : PermutationTuples N 100) :
    Fintype (Survivor h σ) := Fintype.ofFinite _

theorem survivor_degree_bound {N : ℕ} (h : ℕ) (σ : PermutationTuples N 100) :
    DegreeBound (survivorGraph h σ) 100 :=
  @induced_degree_bound (BipartiteVertex N) _ _ (permutationGraph σ)
    {v | v ∉ removedVertices N h σ} (survivor_fintype h σ) 100 (permutation_degree_bound σ)
end URMatching
