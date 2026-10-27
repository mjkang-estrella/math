import FamilyMatrices

open Finset Matrix

namespace ConnectionGraph
noncomputable section
variable {X : Type*} [LinearOrder X]

def supportVertices (F : Finset (Finset X)) : Finset X := F.biUnion id

def restrictedFace (F : Finset (Finset X)) (s : Finset X) : Finset (supportVertices F) :=
  univ.filter fun x => x.val ∈ s

def restrictedFamily (F : Finset (Finset X)) : Finset (Finset (supportVertices F)) :=
  univ.image fun s : F => restrictedFace F s.val

theorem face_vertex_mem_support {F : Finset (Finset X)} {s : Finset X}
    (hs : s ∈ F) {x : X} (hx : x ∈ s) : x ∈ supportVertices F :=
  mem_biUnion.mpr ⟨s, hs, hx⟩

theorem mem_restrictedFace (F : Finset (Finset X)) (s : Finset X)
    (x : supportVertices F) : x ∈ restrictedFace F s ↔ x.val ∈ s := by
  simp [restrictedFace]

theorem restrictedFace_restore {F : Finset (Finset X)} {s : Finset X} (hs : s ∈ F) :
    (restrictedFace F s).image Subtype.val = s := by
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hx
    exact (mem_restrictedFace F s w).mp hw
  · intro hx
    let w : supportVertices F := ⟨x, face_vertex_mem_support hs hx⟩
    exact mem_image.mpr ⟨w, (mem_restrictedFace F s w).mpr hx, rfl⟩

theorem restrictedFace_card {F : Finset (Finset X)} {s : Finset X} (hs : s ∈ F) :
    (restrictedFace F s).card = s.card := by
  have ht := congrArg Finset.card (restrictedFace_restore hs)
  rwa [card_image_of_injective _ Subtype.val_injective] at ht

theorem restrictedFace_injective (F : Finset (Finset X)) :
    Function.Injective (fun s : F => restrictedFace F s.val) := by
  intro s t h
  apply Subtype.ext
  calc
    s.val = (restrictedFace F s.val).image Subtype.val := (restrictedFace_restore s.property).symm
    _ = (restrictedFace F t.val).image Subtype.val := congrArg (fun a => a.image Subtype.val) h
    _ = t.val := restrictedFace_restore t.property

def restrictEquiv (F : Finset (Finset X)) : F ≃ restrictedFamily F :=
  Equiv.ofBijective (fun s => ⟨restrictedFace F s.val, mem_image.mpr ⟨s, mem_univ _, rfl⟩⟩)
    ⟨fun s t h => restrictedFace_injective F (congrArg Subtype.val h), by
      intro t
      obtain ⟨s, _, hs⟩ := mem_image.mp t.property
      exact ⟨s, Subtype.ext hs⟩⟩

theorem restrictEquiv_coe (F : Finset (Finset X)) (s : F) :
    (restrictEquiv F s).val = restrictedFace F s.val := rfl

theorem restrictedFamily_card (F : Finset (Finset X)) : (restrictedFamily F).card = F.card := by
  have h := Fintype.card_congr (restrictEquiv F)
  simpa using h.symm

theorem restrictedFamily_singletons (F : Finset (Finset X))
    (hclosed : ∀ s ∈ F, ∀ t ⊆ s, t.Nonempty → t ∈ F)
    (v : supportVertices F) : {v} ∈ restrictedFamily F := by
  obtain ⟨s, hs, hv⟩ := mem_biUnion.mp v.property
  have hsingle : {v.val} ∈ F := hclosed s hs _ (singleton_subset_iff.mpr hv) (singleton_nonempty _)
  have heq : restrictedFace F {v.val} = {v} := by
    ext w
    simp only [mem_restrictedFace, mem_singleton, Subtype.val_inj]
  rw [← heq]
  exact mem_image.mpr ⟨⟨{v.val}, hsingle⟩, mem_univ _, rfl⟩

theorem restrictedFamily_face_cards (F : Finset (Finset X))
    (hc : ∀ s ∈ F, s.card = 1 ∨ s.card = 2) :
    ∀ s ∈ restrictedFamily F, s.card = 1 ∨ s.card = 2 := by
  intro s hs
  obtain ⟨t, _, rfl⟩ := mem_image.mp hs
  rw [restrictedFace_card t.property]
  exact hc t.val t.property

theorem supportVertices_nonempty (F : Finset (Finset X)) (hF : F.Nonempty)
    (hc : ∀ s ∈ F, s.card = 1 ∨ s.card = 2) : (supportVertices F).Nonempty := by
  obtain ⟨s, hs⟩ := hF
  have hsc : 0 < s.card := by rcases hc s hs with h | h <;> omega
  obtain ⟨v, hv⟩ := card_pos.mp hsc
  exact ⟨v, face_vertex_mem_support hs hv⟩

theorem restrictedFace_inter {F : Finset (Finset X)} {s t : Finset X}
    (hs : s ∈ F) :
    (restrictedFace F s ∩ restrictedFace F t).Nonempty ↔ (s ∩ t).Nonempty := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨hws, hwt⟩ := mem_inter.mp hw
    exact ⟨w.val, mem_inter.mpr
      ⟨(mem_restrictedFace F s w).mp hws, (mem_restrictedFace F t w).mp hwt⟩⟩
  · rintro ⟨x, hx⟩
    obtain ⟨hxs, hxt⟩ := mem_inter.mp hx
    let w : supportVertices F := ⟨x, face_vertex_mem_support hs hxs⟩
    exact ⟨w, mem_inter.mpr
      ⟨(mem_restrictedFace F s w).mpr hxs, (mem_restrictedFace F t w).mpr hxt⟩⟩

theorem restrictedFace_subset {F : Finset (Finset X)} {s t : Finset X}
    (hs : s ∈ F) : restrictedFace F s ⊆ restrictedFace F t ↔ s ⊆ t := by
  constructor
  · intro h x hx
    let w : supportVertices F := ⟨x, face_vertex_mem_support hs hx⟩
    exact (mem_restrictedFace F t w).mp (h ((mem_restrictedFace F s w).mpr hx))
  · intro h w hw
    exact (mem_restrictedFace F t w).mpr (h ((mem_restrictedFace F s w).mp hw))

theorem restrictedFace_order {F : Finset (Finset X)} {s t : Finset X}
    (hs : s ∈ F) (ht : t ∈ F) :
    (∀ x ∈ restrictedFace F s, ∀ y ∈ restrictedFace F t, x ≤ y) ↔
      ∀ x ∈ s, ∀ y ∈ t, x ≤ y := by
  constructor
  · intro h x hx y hy
    let a : supportVertices F := ⟨x, face_vertex_mem_support hs hx⟩
    let b : supportVertices F := ⟨y, face_vertex_mem_support ht hy⟩
    exact h a ((mem_restrictedFace F s a).mpr hx) b ((mem_restrictedFace F t b).mpr hy)
  · intro h x hx y hy
    exact h x.val ((mem_restrictedFace F s x).mp hx) y.val ((mem_restrictedFace F t y).mp hy)

section Matrices
variable [Fintype X]

omit [Fintype X] in
theorem restricted_connection_pullback (F : Finset (Finset X)) :
    (familyConnectionMatrix (restrictedFamily F)).submatrix (restrictEquiv F) (restrictEquiv F) =
      familyConnectionMatrix F := by
  ext s t
  change (if (restrictedFace F s.val ∩ restrictedFace F t.val).Nonempty then (1 : ℝ) else 0) =
    (if (s.val ∩ t.val).Nonempty then 1 else 0)
  by_cases h : (s.val ∩ t.val).Nonempty
  · have hr := (restrictedFace_inter (t := t.val) s.property).mpr h
    simp only [h, hr, ↓reduceIte]
  · have hr : ¬ (restrictedFace F s.val ∩ restrictedFace F t.val).Nonempty :=
      fun hh => h ((restrictedFace_inter (t := t.val) s.property).mp hh)
    simp only [h, hr, ↓reduceIte]

theorem restricted_boundary_pullback (F : Finset (Finset X)) :
    (familyBoundaryMatrix (restrictedFamily F)).submatrix (restrictEquiv F) (restrictEquiv F) =
      familyBoundaryMatrix F := by
  ext s t
  simp only [familyBoundaryMatrix, submatrix_apply, restrictEquiv_coe,
    restrictedFace_card s.property, restrictedFace_card t.property,
    restrictedFace_subset s.property, restrictedFace_order s.property t.property]

theorem restricted_dirac_pullback (F : Finset (Finset X)) :
    (familyDiracMatrix (restrictedFamily F)).submatrix (restrictEquiv F) (restrictEquiv F) =
      familyDiracMatrix F := by
  change (familyBoundaryMatrix (restrictedFamily F)).submatrix (restrictEquiv F) (restrictEquiv F) +
    ((familyBoundaryMatrix (restrictedFamily F)).submatrix (restrictEquiv F) (restrictEquiv F))ᵀ = _
  rw [restricted_boundary_pullback]
  rfl

omit [Fintype X] in
theorem restricted_connection_reindex (F : Finset (Finset X)) :
    (familyConnectionMatrix F).reindex (restrictEquiv F) (restrictEquiv F) =
      familyConnectionMatrix (restrictedFamily F) := by
  rw [← restricted_connection_pullback F]
  ext s t
  simp

theorem restricted_dirac_reindex (F : Finset (Finset X)) :
    (familyDiracMatrix F).reindex (restrictEquiv F) (restrictEquiv F) =
      familyDiracMatrix (restrictedFamily F) := by
  rw [← restricted_dirac_pullback F]
  ext s t
  simp

omit [Fintype X] in
theorem restricted_connection_spectral_sum (F : Finset (Finset X)) (k : ℕ) :
    spectralTopSum (family_connection_hermitian (restrictedFamily F)) k =
      spectralTopSum (family_connection_hermitian F) k := by
  have h := spectralTopSum_reindex (family_connection_hermitian F) (restrictEquiv F) k
  simpa only [restricted_connection_reindex F] using h

theorem restricted_dirac_spectral_sum (F : Finset (Finset X)) (k : ℕ) :
    spectralTopSum (family_dirac_hermitian (restrictedFamily F)) k =
      spectralTopSum (family_dirac_hermitian F) k := by
  have h := spectralTopSum_reindex (family_dirac_hermitian F) (restrictEquiv F) k
  simpa only [restricted_dirac_reindex F] using h

end Matrices

end
end ConnectionGraph
