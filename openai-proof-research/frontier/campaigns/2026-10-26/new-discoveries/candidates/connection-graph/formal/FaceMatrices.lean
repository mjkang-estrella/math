import GraphComplex
import SpectralReindex

open Finset Matrix

namespace ConnectionGraph
noncomputable section
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The oriented boundary on actual singleton and two-element faces. The
smaller endpoint has coefficient -1 and the larger endpoint coefficient +1. -/
def faceBoundaryMatrix (E : Finset (V × V)) : Matrix (graphFaces E) (graphFaces E) ℝ :=
  fun s t => if s.val.card = 1 ∧ t.val.card = 2 ∧ s.val ⊆ t.val then
    (if ∀ x ∈ s.val, ∀ y ∈ t.val, x ≤ y then -1 else 1) else 0

def faceDiracMatrix (E : Finset (V × V)) : Matrix (graphFaces E) (graphFaces E) ℝ :=
  faceBoundaryMatrix E + (faceBoundaryMatrix E)ᵀ

theorem face_boundary_pullback {E : Finset (V × V)} (hE : ValidEdges E) :
    (faceBoundaryMatrix E).submatrix (simplexEquiv hE) (simplexEquiv hE) =
      boundaryMatrix E := by
  ext (a | e) (b | f)
  · simp [faceBoundaryMatrix, simplexEquiv_coe, simplex, boundaryMatrix]
  · have hf := hE f.val f.property
    have hn := edge_ne hE f
    have hback := not_lt.mpr hf.le
    by_cases h1 : a = f.val.1 <;> by_cases h2 : a = f.val.2 <;>
      simp_all [faceBoundaryMatrix, simplexEquiv_coe, simplex, boundaryMatrix,
        signedIncidence, card_pair hn, not_le.mpr hf]
  · have he := edge_ne hE e
    simp [faceBoundaryMatrix, simplexEquiv_coe, simplex, boundaryMatrix, card_pair he]
  · have he := edge_ne hE e
    simp [faceBoundaryMatrix, simplexEquiv_coe, simplex, boundaryMatrix, card_pair he]

theorem face_dirac_pullback {E : Finset (V × V)} (hE : ValidEdges E) :
    (faceDiracMatrix E).submatrix (simplexEquiv hE) (simplexEquiv hE) =
      diracMatrix E := by
  change (faceBoundaryMatrix E).submatrix (simplexEquiv hE) (simplexEquiv hE) +
    ((faceBoundaryMatrix E).submatrix (simplexEquiv hE) (simplexEquiv hE))ᵀ = _
  rw [face_boundary_pullback hE]
  rfl

theorem face_connection_reindex {E : Finset (V × V)} (hE : ValidEdges E) :
    (connectionMatrix E).reindex (simplexEquiv hE) (simplexEquiv hE) =
      faceConnectionMatrix E := by
  rw [← face_connection_pullback hE]
  ext s t
  simp

theorem face_dirac_reindex {E : Finset (V × V)} (hE : ValidEdges E) :
    (diracMatrix E).reindex (simplexEquiv hE) (simplexEquiv hE) =
      faceDiracMatrix E := by
  rw [← face_dirac_pullback hE]
  ext s t
  simp

theorem face_connection_hermitian (E : Finset (V × V)) : (faceConnectionMatrix E).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro s t
  simp [faceConnectionMatrix, inter_comm]

theorem face_dirac_hermitian (E : Finset (V × V)) : (faceDiracMatrix E).IsHermitian := by
  simp [faceDiracMatrix, Matrix.IsHermitian, add_comm]

theorem face_connection_spectral_sum {E : Finset (V × V)} (hE : ValidEdges E) (k : ℕ) :
    spectralTopSum (face_connection_hermitian E) k =
      spectralTopSum (connection_hermitian E) k := by
  have h := spectralTopSum_reindex (connection_hermitian E) (simplexEquiv hE) k
  simpa only [face_connection_reindex hE] using h

theorem face_dirac_spectral_sum {E : Finset (V × V)} (hE : ValidEdges E) (k : ℕ) :
    spectralTopSum (face_dirac_hermitian E) k =
      spectralTopSum (dirac_hermitian E) k := by
  have h := spectralTopSum_reindex (dirac_hermitian E) (simplexEquiv hE) k
  simpa only [face_dirac_reindex hE] using h

end
end ConnectionGraph
