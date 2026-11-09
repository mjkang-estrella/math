module
public import GridOrbitPaths
@[expose] public section
namespace Grid343536

/-- The actual conjugation homomorphism for switching the grid dimensions. -/
def transposeConj (m n : ℕ) : (G n m ≃g G n m) →* (G m n ≃g G m n) where
  toFun g := ((transpose m n).trans g).trans (transpose n m)
  map_one' := by apply DFunLike.ext; intro x; rfl
  map_mul' g h := by apply DFunLike.ext; intro x; rfl

theorem transposeConj_row (m n : ℕ) :
    transposeConj m n (rowFlip n m) = colFlip m n := by
  apply DFunLike.ext; intro x; rfl

theorem transposeConj_col (m n : ℕ) :
    transposeConj m n (colFlip n m) = rowFlip m n := by
  apply DFunLike.ext; intro x; rfl

theorem rowFlip_mem_A0 (m n : ℕ) : rowFlip m n ∈ A0 m n := by
  unfold A0
  split
  · subst n; apply Subgroup.subset_closure; simp
  · apply Subgroup.subset_closure; simp

theorem colFlip_mem_A0 (m n : ℕ) : colFlip m n ∈ A0 m n := by
  unfold A0
  split
  · subst n; apply Subgroup.subset_closure; simp
  · apply Subgroup.subset_closure; simp

theorem transpose_mem_A0 (n : ℕ) : transpose n n ∈ A0 n n := by
  unfold A0
  split
  · apply Subgroup.subset_closure; simp
  · rename_i h; exact False.elim (h rfl)

theorem transposeConj_mem {m n : ℕ} {g : G n m ≃g G n m} (hg : g ∈ A0 n m) :
    transposeConj m n g ∈ A0 m n := by
  have hle : A0 n m ≤ (A0 m n).comap (transposeConj m n) := by
    unfold A0
    split
    · subst m
      apply (Subgroup.closure_le _).mpr
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · exact colFlip_mem_A0 n n
      · exact rowFlip_mem_A0 n n
      · exact transpose_mem_A0 n
    · apply (Subgroup.closure_le _).mpr
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact colFlip_mem_A0 m n
      · exact rowFlip_mem_A0 m n
  exact hle hg

theorem main_orbit_row_path (n : ℕ) (hn : 1 ≤ n)
    (r : Setoid (Fin 1 × Fin n)) (hr : IsEquitable (G 1 n) r) :
    r = orbitSetoid (G 1 n) (Hpi r) := by
  let f := transpose 1 n
  let s := transportPartition f r
  have hs := main_orbit_column_path n hn s (transport_equitable f r hr)
  apply le_antisymm
  · intro u v huv
    have huv' : s (f u) (f v) := by change r (f.symm (f u)) (f.symm (f v)); simpa using huv
    rw [hs] at huv'
    obtain ⟨g,hg,hgv⟩ := huv'
    refine ⟨transposeConj 1 n g, ⟨transposeConj_mem hg.1, ?_⟩, ?_⟩
    · exact conjugate_preserves_partition f r g hg.2
    · exact conjugate_sends f g hgv
  · exact Hpi_orbit_le r
end Grid343536
