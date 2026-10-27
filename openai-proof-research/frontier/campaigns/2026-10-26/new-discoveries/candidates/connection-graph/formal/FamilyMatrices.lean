import FaceMatrices
import ComplexEncoding

open Finset Matrix

namespace ConnectionGraph
noncomputable section
variable {V : Type*} [Fintype V] [LinearOrder V]

def familyConnectionMatrix (F : Finset (Finset V)) : Matrix F F ℝ :=
  fun s t => if (s.val ∩ t.val).Nonempty then 1 else 0

def familyBoundaryMatrix (F : Finset (Finset V)) : Matrix F F ℝ :=
  fun s t => if s.val.card = 1 ∧ t.val.card = 2 ∧ s.val ⊆ t.val then
    (if ∀ x ∈ s.val, ∀ y ∈ t.val, x ≤ y then -1 else 1) else 0

def familyDiracMatrix (F : Finset (Finset V)) : Matrix F F ℝ :=
  familyBoundaryMatrix F + (familyBoundaryMatrix F)ᵀ

omit [Fintype V] in
theorem family_connection_hermitian (F : Finset (Finset V)) :
    (familyConnectionMatrix F).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro s t
  simp [familyConnectionMatrix, inter_comm]

theorem family_dirac_hermitian (F : Finset (Finset V)) :
    (familyDiracMatrix F).IsHermitian := by
  simp [familyDiracMatrix, Matrix.IsHermitian, add_comm]

omit [Fintype V] in
theorem family_connection_sum_congr {F G : Finset (Finset V)} (h : F = G) (k : ℕ) :
    spectralTopSum (family_connection_hermitian F) k =
      spectralTopSum (family_connection_hermitian G) k := by
  subst G
  rfl

theorem family_dirac_sum_congr {F G : Finset (Finset V)} (h : F = G) (k : ℕ) :
    spectralTopSum (family_dirac_hermitian F) k =
      spectralTopSum (family_dirac_hermitian G) k := by
  subst G
  rfl

theorem complex_connection_spectral_sum (F : Finset (Finset V))
    (hsingle : ∀ v : V, {v} ∈ F)
    (hcard : ∀ s ∈ F, s.card = 1 ∨ s.card = 2) (k : ℕ) :
    spectralTopSum (family_connection_hermitian F) k =
      spectralTopSum (connection_hermitian (complexEdges F)) k := by
  calc
    _ = spectralTopSum (family_connection_hermitian (graphFaces (complexEdges F))) k :=
      family_connection_sum_congr (graphFaces_complexEdges F hsingle hcard).symm k
    _ = spectralTopSum (face_connection_hermitian (complexEdges F)) k := rfl
    _ = _ := face_connection_spectral_sum (complexEdges_valid F) k

theorem complex_dirac_spectral_sum (F : Finset (Finset V))
    (hsingle : ∀ v : V, {v} ∈ F)
    (hcard : ∀ s ∈ F, s.card = 1 ∨ s.card = 2) (k : ℕ) :
    spectralTopSum (family_dirac_hermitian F) k =
      spectralTopSum (dirac_hermitian (complexEdges F)) k := by
  calc
    _ = spectralTopSum (family_dirac_hermitian (graphFaces (complexEdges F))) k :=
      family_dirac_sum_congr (graphFaces_complexEdges F hsingle hcard).symm k
    _ = spectralTopSum (face_dirac_hermitian (complexEdges F)) k := rfl
    _ = _ := face_dirac_spectral_sum (complexEdges_valid F) k

end
end ConnectionGraph
