module
public import GridInternalFlags
@[expose] public section
namespace Grid343536
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-- Every non-corner border point lies in an explicit horizontal or vertical frame. -/
theorem internal_border_frame {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (v : Fin m × Fin n) (hv : gridLayer v = 1) (hc : (G m n).degree v ≠ 2) :
    (∃ f ∈ A0 m n, ∃ k : Fin n, 0 < k.val ∧ k.val+1<n ∧
      f (⟨0,by omega⟩,k) = v) ∨
    (∃ f ∈ A0 m n, ∃ k : Fin m, 0 < k.val ∧ k.val+1<m ∧
      f (k,⟨0,by omega⟩) = v) := by
  have vi := v.1.isLt
  have vj := v.2.isLt
  have hdeg := grid_degree_formula v
  have hb : v.1.val = 0 ∨ v.1.val = m-1 ∨ v.2.val = 0 ∨ v.2.val = n-1 := by
    unfold gridLayer at hv; omega
  by_cases h0 : v.1.val = 0
  · left
    refine ⟨1,(A0 m n).one_mem,v.2,?_,?_,?_⟩
    · rw [hdeg] at hc; simp only [h0] at hc; split_ifs at hc <;> omega
    · rw [hdeg] at hc; simp only [h0] at hc; split_ifs at hc <;> omega
    · exact Prod.ext (Fin.ext h0.symm) rfl
  by_cases hlast : v.1.val = m-1
  · left
    refine ⟨rowFlip m n,rowFlip_mem_A0 m n,v.2,?_,?_,?_⟩
    · rw [hdeg] at hc; simp only [hlast] at hc; split_ifs at hc <;> omega
    · rw [hdeg] at hc; simp only [hlast] at hc; split_ifs at hc <;> omega
    · apply Prod.ext
      · apply Fin.ext
        change m-1-0 = v.1.val
        omega
      · rfl
  right
  have hil : 0 < v.1.val := by omega
  have hir : v.1.val+1<m := by omega
  by_cases hj0 : v.2.val = 0
  · refine ⟨1,(A0 m n).one_mem,v.1,hil,hir,?_⟩
    exact Prod.ext rfl (Fin.ext hj0.symm)
  · refine ⟨colFlip m n,colFlip_mem_A0 m n,v.1,hil,hir,?_⟩
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change n-1-0 = v.2.val
      omega

/-- Non-corner transitivity with the source on the top side. -/
theorem top_internal_transitivity {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (r : Setoid (Fin m × Fin n)) (hr : IsEquitable (G m n) r)
    (j : Fin n) (hj : 0 < j.val) (hjn : j.val+1<n)
    (v : Fin m × Fin n) (hrel : r (⟨0,by omega⟩,j) v) :
    ∃ g ∈ Hpi r, g (⟨0,by omega⟩,j) = v := by
  have hu : gridLayer ((⟨0,by omega⟩,j) : Fin m × Fin n) = 1 := by
    unfold gridLayer; dsimp; omega
  have hv : gridLayer v = 1 := (grid_layer_invariant hm hn r hr _ _ hrel).symm.trans hu
  have hc : (G m n).degree v ≠ 2 := by
    intro hc
    have h := (corner_colour_invariant r hr hrel).mpr hc
    rw [grid_degree_formula] at h
    simp only [Fin.val_mk,Nat.lt_irrefl,show 0+1<m by omega,hj,hjn,↓reduceIte] at h
    omega
  rcases internal_border_frame hm hn v hv hc with h | h
  · obtain ⟨f,hf,k,hk,hkb,hfv⟩ := h
    have hrel' : r (⟨0,by omega⟩,⟨j.val,by omega⟩)
        (f (⟨0,by omega⟩,⟨k.val,by omega⟩)) := by simpa only [hfv] using hrel
    obtain ⟨e,_,he,_,hes,h0,h1⟩ := align_internal_chart hm hn hm hn r hr f
      j.val k.val hj hjn hk hkb hrel'
    refine ⟨e,color_flag_mem_Hpi hm hn r hr e ?_ h0 h1,hes.trans hfv⟩
    rcases he with rfl | rfl
    · exact hf
    · exact (A0 m n).mul_mem hf (colFlip_mem_A0 m n)
  · obtain ⟨f,hf,k,hk,hkb,hfv⟩ := h
    let F := (transpose n m).trans f
    have hrel' : r (⟨0,by omega⟩,⟨j.val,by omega⟩)
        (F (⟨0,by omega⟩,⟨k.val,by omega⟩)) := by
      change r (⟨0,by omega⟩,j) (f (k,⟨0,by omega⟩))
      rw [hfv]; exact hrel
    obtain ⟨e,_,he,hlen,hes,h0,h1⟩ := align_internal_chart hn hm hm hn r hr F
      j.val k.val hj hjn hk hkb hrel'
    subst n
    refine ⟨e,color_flag_mem_Hpi hm hm r hr e ?_ h0 h1,hes.trans hfv⟩
    rcases he with rfl | rfl
    · exact (A0 m m).mul_mem hf (transpose_mem_A0 m)
    · exact (A0 m m).mul_mem ((A0 m m).mul_mem hf (transpose_mem_A0 m))
        (colFlip_mem_A0 m m)
end Grid343536
