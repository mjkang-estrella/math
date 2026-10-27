import LowConnection
import EmptyGraph
import GroundSet
import DiracPositive

namespace ConnectionGraph

open Finset Matrix
noncomputable section
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem degree_top_sum_nonneg (E : Finset (V × V)) (k : ℕ) :
    0 ≤ sortedTopSum (degree E) k := by
  rw [sortedTopSum_eq_sum_topSet]
  exact Finset.sum_nonneg fun v _ => degree_nonneg E v

theorem graph_strict_spectral_gap [Nonempty V] {E : Finset (V × V)}
    (hE : ValidEdges E) {k : ℕ} (hk0 : 0 < k)
    (hk : k ≤ Fintype.card V + E.card) :
    Real.sqrt 2 - 1 ≤ spectralTopSum (connection_hermitian E) k -
      spectralTopSum (dirac_hermitian E) k := by
  by_cases he : E = ∅
  · exact empty_graph_strict_gap he hk0 hk
  · have hne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
    by_cases hkv : k ≤ Fintype.card V
    · have hl := graph_low_connection_bound hE hne hk0 hkv
      have hd := dirac_spectral_top_sum_le_sqrt E hkv
      have hs := sum_bound_ge_sqrt (show (0:ℝ) ≤ k by positivity)
        (degree_top_sum_nonneg E k)
      linarith
    · have hl := graph_high_connection_bound hE (Nat.le_of_lt (lt_of_not_ge hkv)) hk
      have hk' : k ≤ Fintype.card (V ⊕ E) := by simpa using hk
      have hd := dirac_spectral_top_sum_le_global E hE hk'
      have hg := gap_lt_half
      linarith

/-- Literal finite face-family endpoint; unused ambient vertices are allowed. -/
theorem source_graph_strict_gap (F : Finset (Finset V)) (hF : F.Nonempty)
    (hclosed : ∀ s ∈ F, ∀ t ⊆ s, t.Nonempty → t ∈ F)
    (hcard : ∀ s ∈ F, s.card = 1 ∨ s.card = 2)
    {k : ℕ} (hk0 : 0 < k) (hk : k ≤ F.card) :
    Real.sqrt 2 - 1 ≤ spectralTopSum (family_connection_hermitian F) k -
      spectralTopSum (family_dirac_hermitian F) k := by
  obtain ⟨v, hv⟩ := supportVertices_nonempty F hF hcard
  let : Nonempty (supportVertices F) := ⟨⟨v,hv⟩⟩
  let R := restrictedFamily F
  have hs : ∀ v : supportVertices F, {v} ∈ R := restrictedFamily_singletons F hclosed
  have hc : ∀ s ∈ R, s.card = 1 ∨ s.card = 2 := restrictedFamily_face_cards F hcard
  have hcount := complexEncoding_card R hs hc
  have hkR : k ≤ Fintype.card (supportVertices F) + (complexEdges R).card := by
    rw [← hcount]
    simpa only [R, restrictedFamily_card] using hk
  have h := graph_strict_spectral_gap (complexEdges_valid R) hk0 hkR
  rw [← complex_connection_spectral_sum R hs hc k,
    ← complex_dirac_spectral_sum R hs hc k] at h
  change Real.sqrt 2 - 1 ≤
    spectralTopSum (family_connection_hermitian (restrictedFamily F)) k -
    spectralTopSum (family_dirac_hermitian (restrictedFamily F)) k at h
  rwa [restricted_connection_spectral_sum F k, restricted_dirac_spectral_sum F k] at h

/-- The strict inequality in the exact dimension-at-most-one source case. -/
theorem source_graph_spectral_dominance (F : Finset (Finset V)) (hF : F.Nonempty)
    (hclosed : ∀ s ∈ F, ∀ t ⊆ s, t.Nonempty → t ∈ F)
    (hcard : ∀ s ∈ F, s.card = 1 ∨ s.card = 2)
    {k : ℕ} (hk0 : 0 < k) (hk : k ≤ F.card) :
    spectralTopSum (family_dirac_hermitian F) k <
      spectralTopSum (family_connection_hermitian F) k := by
  have h := source_graph_strict_gap F hF hclosed hcard hk0 hk
  have hg := gap_positive
  linarith

end
end ConnectionGraph
