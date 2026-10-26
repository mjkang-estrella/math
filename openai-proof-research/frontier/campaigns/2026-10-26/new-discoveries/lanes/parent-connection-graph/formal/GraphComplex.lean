import IncidenceBlocks

open Finset Matrix

namespace ConnectionGraph
noncomputable section
variable {V : Type*} [Fintype V] [LinearOrder V]

omit [Fintype V] in
theorem simplex_injective {E : Finset (V × V)} (hE : ValidEdges E) :
    Function.Injective (simplex E) := by
  intro i j hij
  cases i with
  | inl a =>
    cases j with
    | inl b =>
      have h : a = b := singleton_inj.mp hij
      exact congrArg Sum.inl h
    | inr f =>
      have hc := congrArg Finset.card hij
      simp only [simplex, card_singleton, card_pair (edge_ne hE f)] at hc
      omega
  | inr e =>
    cases j with
    | inl b =>
      have hc := congrArg Finset.card hij
      simp only [simplex, card_singleton, card_pair (edge_ne hE e)] at hc
      omega
    | inr f =>
      change ({e.val.1, e.val.2} : Finset V) = {f.val.1, f.val.2} at hij
      have hleft : e.val.1 = f.val.1 := by
        have ha : e.val.1 ∈ ({f.val.1, f.val.2} : Finset V) := by
          rw [← hij]
          simp
        have hb : f.val.1 ∈ ({e.val.1, e.val.2} : Finset V) := by
          rw [hij]
          simp
        have he := hE e.val e.property
        have hf := hE f.val f.property
        simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with h | h
        · exact h
        · rcases hb with h' | h'
          · exact h'.symm
          · rw [h, h'.symm] at he
            exact (lt_asymm he hf).elim
      have hright : e.val.2 = f.val.2 := by
        have ha : e.val.2 ∈ ({f.val.1, f.val.2} : Finset V) := by
          rw [← hij]
          simp
        simp only [mem_insert, mem_singleton] at ha
        rcases ha with h | h
        · have he := edge_ne hE e
          exact (he (hleft.trans h.symm)).elim
        · exact h
      exact congrArg Sum.inr (Subtype.ext (Prod.ext hleft hright))

def graphFaces (E : Finset (V × V)) : Finset (Finset V) := univ.image (simplex E)

theorem singleton_mem_graphFaces (E : Finset (V × V)) (v : V) : {v} ∈ graphFaces E :=
  mem_image.mpr ⟨Sum.inl v, mem_univ _, rfl⟩

theorem simplex_mem_graphFaces (E : Finset (V × V)) (i : V ⊕ E) :
    simplex E i ∈ graphFaces E := mem_image.mpr ⟨i, mem_univ _, rfl⟩

theorem graphFaces_card {E : Finset (V × V)} (hE : ValidEdges E) :
    (graphFaces E).card = Fintype.card V + E.card := by
  rw [graphFaces, card_image_of_injective _ (simplex_injective hE), card_univ]
  simp

theorem graphFaces_no_empty (E : Finset (V × V)) : ∅ ∉ graphFaces E := by
  intro he
  obtain ⟨i, _, hi⟩ := mem_image.mp he
  cases i <;> simp [simplex] at hi

theorem graphFaces_card_one_or_two {E : Finset (V × V)} (hE : ValidEdges E)
    {s : Finset V} (hs : s ∈ graphFaces E) : s.card = 1 ∨ s.card = 2 := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp hs
  cases i with
  | inl v => exact Or.inl (by simp [simplex])
  | inr e => exact Or.inr (by simp [simplex, card_pair (edge_ne hE e)])

theorem graphFaces_closed (E : Finset (V × V)) {s t : Finset V}
    (hs : s ∈ graphFaces E) (ht : t.Nonempty) (hts : t ⊆ s) : t ∈ graphFaces E := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp hs
  cases i with
  | inl v =>
    change t ⊆ {v} at hts
    have heq : t = {v} := by
      apply Subset.antisymm hts
      obtain ⟨w, hw⟩ := ht
      have hv : w = v := mem_singleton.mp (hts hw)
      intro x hx
      have hxv : x = v := mem_singleton.mp hx
      rw [hxv]
      simpa only [hv] using hw
    rw [heq]
    exact singleton_mem_graphFaces E v
  | inr e =>
    change t ⊆ {e.val.1, e.val.2} at hts
    by_cases ha : e.val.1 ∈ t
    · by_cases hb : e.val.2 ∈ t
      · have heq : t = {e.val.1, e.val.2} := by
          apply Subset.antisymm hts
          intro v hv
          simp only [mem_insert, mem_singleton] at hv
          rcases hv with rfl | rfl <;> assumption
        rw [heq]
        exact simplex_mem_graphFaces E (Sum.inr e)
      · have heq : t = {e.val.1} := by
          ext v
          have hs' : v ∈ t → v = e.val.1 ∨ v = e.val.2 := by
            intro hv
            simpa only [mem_insert, mem_singleton] using hts hv
          simp only [mem_singleton]
          constructor
          · intro hv
            rcases hs' hv with h | h
            · exact h
            · exact (hb (h ▸ hv)).elim
          · intro h
            simpa only [h] using ha
        rw [heq]
        exact singleton_mem_graphFaces E e.val.1
    · have heq : t = {e.val.2} := by
        ext v
        obtain ⟨w, hw⟩ := ht
        have hs' : ∀ v ∈ t, v = e.val.1 ∨ v = e.val.2 := by
          intro v hv
          simpa only [mem_insert, mem_singleton] using hts hv
        have hb : e.val.2 ∈ t := by
          rcases hs' w hw with h | h
          · exact (ha (h ▸ hw)).elim
          · exact h ▸ hw
        simp only [mem_singleton]
        constructor
        · intro hv
          rcases hs' v hv with h | h
          · exact (ha (h ▸ hv)).elim
          · exact h
        · intro h
          simpa only [h] using hb
      rw [heq]
      exact singleton_mem_graphFaces E e.val.2

def simplexEquiv {E : Finset (V × V)} (hE : ValidEdges E) : (V ⊕ E) ≃ graphFaces E :=
  Equiv.ofBijective (fun i => ⟨simplex E i, simplex_mem_graphFaces E i⟩)
    ⟨fun i j hij => simplex_injective hE (congrArg Subtype.val hij), by
      intro s
      obtain ⟨i, _, hi⟩ := mem_image.mp s.property
      exact ⟨i, Subtype.ext hi⟩⟩

theorem simplexEquiv_coe {E : Finset (V × V)} (hE : ValidEdges E) (i : V ⊕ E) :
    (simplexEquiv hE i).val = simplex E i := rfl

def faceConnectionMatrix (E : Finset (V × V)) : Matrix (graphFaces E) (graphFaces E) ℝ :=
  fun s t => if (s.val ∩ t.val).Nonempty then 1 else 0

theorem face_connection_pullback {E : Finset (V × V)} (hE : ValidEdges E) :
    (faceConnectionMatrix E).submatrix (simplexEquiv hE) (simplexEquiv hE) =
      connectionMatrix E := rfl

end
end ConnectionGraph
