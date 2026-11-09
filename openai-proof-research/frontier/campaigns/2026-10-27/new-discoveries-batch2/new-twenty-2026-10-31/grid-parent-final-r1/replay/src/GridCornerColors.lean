module
public import GridColorTiming
@[expose] public section
namespace Grid343536
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- A corner admits a frame made of the two reflection generators. -/
theorem corner_frame {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (v : Fin m × Fin n) (hv : (G m n).degree v = 2) :
    ∃ f ∈ A0 m n, f (⟨0,by omega⟩,⟨0,by omega⟩) = v := by
  classical
  have vi := v.1.isLt
  have vj := v.2.isLt
  have hi : v.1.val = 0 ∨ v.1.val = m-1 := by
    rw [grid_degree_formula] at hv
    split_ifs at hv <;> omega
  have hj : v.2.val = 0 ∨ v.2.val = n-1 := by
    rw [grid_degree_formula] at hv
    split_ifs at hv <;> omega
  let a : G m n ≃g G m n := if v.1.val = 0 then 1 else rowFlip m n
  let b : G m n ≃g G m n := if v.2.val = 0 then 1 else colFlip m n
  refine ⟨a*b, (A0 m n).mul_mem ?_ ?_, ?_⟩
  · dsimp [a]; split_ifs
    · exact (A0 m n).one_mem
    · exact rowFlip_mem_A0 m n
  · dsimp [b]; split_ifs
    · exact (A0 m n).one_mem
    · exact colFlip_mem_A0 m n
  · apply Prod.ext <;> apply Fin.ext <;>
      dsimp [a,b] <;> split_ifs <;>
      simp_all [rowFlip,colFlip,Fin.val_rev] <;> omega

/-- The two neighbours in a corner frame are the oriented horizontal and vertical flags. -/
theorem corner_frame_neighbors {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (f : G m n ≃g G m n) (z : Fin m × Fin n)
    (hz : (G m n).Adj (f (⟨0,by omega⟩,⟨0,by omega⟩)) z) :
    z = f (⟨0,by omega⟩,⟨1,by omega⟩) ∨
    z = f (⟨1,by omega⟩,⟨0,by omega⟩) := by
  have h : (G m n).Adj (⟨0,by omega⟩,⟨0,by omega⟩) (f.symm z) := by
    apply f.map_rel_iff.mp
    simpa using hz
  have h' : f.symm z = (⟨0,by omega⟩,⟨1,by omega⟩) ∨
      f.symm z = (⟨1,by omega⟩,⟨0,by omega⟩) := by
    have hi := (f.symm z).1.isLt
    have hj := (f.symm z).2.isLt
    simp only [grid_adj_iff,Prod.ext_iff,Fin.ext_iff,Fin.val_mk] at h ⊢
    omega
  simpa only [f.symm_apply_eq] using h'

/-- Related top-left and arbitrary corners have a colour-preserving A0 witness. -/
theorem origin_corner_transitive {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (r : Setoid (Fin m × Fin n)) (hr : IsEquitable (G m n) r)
    (v : Fin m × Fin n)
    (hv : r (⟨0,by omega⟩,⟨0,by omega⟩) v) :
    ∃ g ∈ Hpi r, g (⟨0,by omega⟩,⟨0,by omega⟩) = v := by
  have hdeg : (G m n).degree v = 2 :=
    (corner_colour_invariant r hr hv).mp (by
      rw [grid_degree_formula]
      simp [show 1<m by omega,show 1<n by omega])
  obtain ⟨f,hf,hfv⟩ := corner_frame hm hn v hdeg
  have hadj : (G m n).Adj (⟨0,by omega⟩,⟨0,by omega⟩)
      (⟨0,by omega⟩,⟨1,by omega⟩) := by
    exact (grid_adj_iff _ _).mpr (Or.inl ⟨rfl,Or.inl rfl⟩)
  obtain ⟨z,hz,hzr⟩ := matching_neighbor hr hv hadj
  rw [← hfv] at hz
  have hzero : r (f (⟨0,by omega⟩,⟨0,by omega⟩))
      (⟨0,by omega⟩,⟨0,by omega⟩) := by rw [hfv]; exact r.symm hv
  rcases corner_frame_neighbors hm hn f z hz with hz | hz
  · refine ⟨f, color_flag_mem_Hpi hm hn r hr f hf hzero ?_, hfv⟩
    simpa only [hz] using hzr
  · have hone : r ((transpose n m).trans f (⟨0,by omega⟩,⟨1,by omega⟩))
        ((1 : G m n ≃g G m n) (⟨0,by omega⟩,⟨1,by omega⟩)) := by
      change r (f (⟨1,by omega⟩,⟨0,by omega⟩)) (⟨0,by omega⟩,⟨1,by omega⟩)
      simpa only [hz] using hzr
    have he : m = n := color_side_length_eq hn hm hm hn hm hn r hr
      ((transpose n m).trans f) 1 hzero hone
    subst n
    let g := (transpose m m).trans f
    refine ⟨g, color_flag_mem_Hpi hm hm r hr g ?_ hzero hone, hfv⟩
    exact (A0 m m).mul_mem hf (transpose_mem_A0 m)

/-- All related ordinary-grid corners have explicit colour-preserving A0 witnesses. -/
theorem ordinary_corner_transitivity {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (r : Setoid (Fin m × Fin n)) (hr : IsEquitable (G m n) r)
    (u v : Fin m × Fin n) (hu : (G m n).degree u = 2) (huv : r u v) :
    ∃ g ∈ Hpi r, g u = v := by
  obtain ⟨f,hf,hfu⟩ := corner_frame hm hn u hu
  let s := transportPartition f.symm r
  have hs := transport_equitable f.symm r hr
  have hrel : s (⟨0,by omega⟩,⟨0,by omega⟩) (f.symm v) := by
    change r (f (⟨0,by omega⟩,⟨0,by omega⟩)) (f (f.symm v))
    simpa only [hfu,f.apply_symm_apply] using huv
  obtain ⟨k,hk,hkv⟩ := origin_corner_transitive hm hn s hs (f.symm v) hrel
  let g := (f.symm.trans k).trans f
  refine ⟨g,⟨?_,conjugate_preserves_partition f.symm r k hk.2⟩,?_⟩
  · change f * k * f⁻¹ ∈ A0 m n
    exact (A0 m n).mul_mem ((A0 m n).mul_mem hf hk.1) ((A0 m n).inv_mem hf)
  · change f (k (f.symm u)) = v
    have hpre : f.symm u = (⟨0,by omega⟩,⟨0,by omega⟩) := f.symm_apply_eq.mpr hfu.symm
    rw [hpre,hkv,f.apply_symm_apply]
end Grid343536
