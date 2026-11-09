import PDTAR.ReductionPaths
namespace PDTAR

/-- The published reduction, proved with the Hamming-isometry replacement route. -/
theorem reductionRemaining : ReductionRemaining := by
  intro V W _ _ _ _ G H hG hH hiso
  obtain ⟨φ⟩ := hiso
  obtain ⟨e,R,he⟩ := reduction_affine_of_hamming reductionHammingRemaining H G hH hG φ
  have hfamily := reduction_affine_family H G φ e R he
  have hnormal := reduction_affine_normalize H G e R hfamily
  apply reduction_of_family_equiv G H e.symm
  intro S
  have hmap : (S.map e.symm.toEmbedding).map e.toEmbedding = S := by
    ext x; simp
  have hh := hnormal (S.map e.symm.toEmbedding)
  rw [hmap] at hh
  exact hh.symm
end PDTAR
