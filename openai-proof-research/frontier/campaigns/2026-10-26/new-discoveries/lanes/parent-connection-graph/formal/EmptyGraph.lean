import HighConnection

open Finset Matrix

namespace ConnectionGraph
noncomputable section
variable {V : Type*} [Fintype V] [LinearOrder V]

omit [Fintype V] in
theorem dirac_empty_edges {E : Finset (V × V)} (hE : E = ∅) : diracMatrix E = 0 := by
  have hC : signedIncidence E = 0 := by
    ext v e
    have he := e.property
    simp [hE] at he
  rw [dirac_block, hC, transpose_zero, fromBlocks_zero]

theorem dirac_empty_spectral_sum {E : Finset (V × V)} (hE : E = ∅)
    {k : ℕ} (hk : k ≤ Fintype.card V + E.card) :
    spectralTopSum (dirac_hermitian E) k = 0 := by
  have hz : (dirac_hermitian E).eigenvalues = 0 :=
    (dirac_hermitian E).eigenvalues_eq_zero_iff.mpr (dirac_empty_edges hE)
  unfold spectralTopSum
  rw [hz]
  change sortedTopSum (fun _ : V ⊕ E => (0 : ℝ)) k = 0
  have hk' : k ≤ Fintype.card (V ⊕ E) := by simpa using hk
  simpa using sortedTopSum_const (α := V ⊕ E) 0 hk'

theorem empty_graph_strict_gap {E : Finset (V × V)} (hE : E = ∅)
    {k : ℕ} (hk0 : 0 < k) (hk : k ≤ Fintype.card V + E.card) :
    Real.sqrt 2 - 1 ≤ spectralTopSum (connection_hermitian E) k -
      spectralTopSum (dirac_hermitian E) k := by
  rw [dirac_empty_spectral_sum hE hk, sub_zero]
  have hi := graph_connection_sum_ge_index E hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
  have hg := gap_lt_half
  linarith

end
end ConnectionGraph
