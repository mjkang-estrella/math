module
public import GridTransposeGroup
@[expose] public section
namespace Grid343536
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem sym8_mem_A0 (k : ℕ) (i : Fin 8) : sym8 k i ∈ A0 k k := by
  fin_cases i
  · exact Subgroup.one_mem _
  · exact rowFlip_mem_A0 k k
  · exact colFlip_mem_A0 k k
  · exact Subgroup.mul_mem _ (rowFlip_mem_A0 k k) (colFlip_mem_A0 k k)
  · exact transpose_mem_A0 k
  · exact Subgroup.mul_mem _ (rowFlip_mem_A0 k k) (transpose_mem_A0 k)
  · exact Subgroup.mul_mem _ (colFlip_mem_A0 k k) (transpose_mem_A0 k)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (rowFlip_mem_A0 k k)
      (colFlip_mem_A0 k k)) (transpose_mem_A0 k)

theorem orbit2_table : ∀ a : Fin 15, relEquitable (G 2 2) (block2 a).r →
    ∀ u v, block2 a u v → ∃ i : Fin 8,
      (∀ x, block2 a (sym8 2 i x) x) ∧ sym8 2 i u = v := by decide

theorem main_orbit_two (r : Setoid (Fin 2 × Fin 2)) (hr : IsEquitable (G 2 2) r) :
    r = orbitSetoid (G 2 2) (Hpi r) := by
  obtain ⟨a,rfl⟩ := equitable2_complete r
  apply le_antisymm
  · intro u v huv
    obtain ⟨i,hi,hiv⟩ := orbit2_table a ((relEquitable_iff _ _).mpr hr) u v huv
    exact ⟨sym8 2 i, ⟨sym8_mem_A0 2 i,hi⟩,hiv⟩
  · exact Hpi_orbit_le _

theorem orbit3_table : ∀ a b : Fin 15, relEquitable (G 3 3) (block3 a b).r →
    ∀ u v, block3 a b u v → ∃ i : Fin 8,
      (∀ x, block3 a b (sym8 3 i x) x) ∧ sym8 3 i u = v := by decide

theorem main_orbit_three (r : Setoid (Fin 3 × Fin 3)) (hr : IsEquitable (G 3 3) r) :
    r = orbitSetoid (G 3 3) (Hpi r) := by
  obtain ⟨a,b,he⟩ := equitable3_complete r hr
  subst r
  apply le_antisymm
  · intro u v huv
    obtain ⟨i,hi,hiv⟩ := orbit3_table a b ((relEquitable_iff _ _).mpr hr) u v huv
    exact ⟨sym8 3 i, ⟨sym8_mem_A0 3 i,hi⟩,hiv⟩
  · exact Hpi_orbit_le _
end Grid343536
