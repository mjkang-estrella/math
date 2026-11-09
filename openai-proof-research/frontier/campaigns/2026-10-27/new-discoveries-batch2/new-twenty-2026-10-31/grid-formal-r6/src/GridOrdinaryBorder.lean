module
public import GridBorderFrames
@[expose] public section
namespace Grid343536

/-- Left-side witnesses are transported through actual generator conjugation. -/
theorem left_internal_transitivity {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (r : Setoid (Fin m × Fin n)) (hr : IsEquitable (G m n) r)
    (i : Fin m) (hi : 0 < i.val) (him : i.val+1<m)
    (v : Fin m × Fin n) (hrel : r (i,⟨0,by omega⟩) v) :
    ∃ g ∈ Hpi r, g (i,⟨0,by omega⟩) = v := by
  let f := transpose m n
  let s := transportPartition f r
  have hs := transport_equitable f r hr
  have hrel' : s (⟨0,by omega⟩,i) (f v) := by
    change r (i,⟨0,by omega⟩) (f.symm (f v))
    simpa using hrel
  obtain ⟨g,hg,hgv⟩ := top_internal_transitivity hn hm s hs i hi him (f v) hrel'
  exact ⟨transposeConj m n g,
    ⟨transposeConj_mem hg.1,conjugate_preserves_partition f r g hg.2⟩,
    conjugate_sends f g hgv⟩

/-- Transfer an Hpi witness out of a reflection frame, including A0 membership. -/
theorem frame_witness_back {m n : ℕ} (r : Setoid (Fin m × Fin n))
    (f : G m n ≃g G m n) (hf : f ∈ A0 m n)
    (x v : Fin m × Fin n)
    (hw : ∃ k ∈ Hpi (transportPartition f.symm r), k x = f.symm v) :
    ∃ g ∈ Hpi r, g (f x) = v := by
  obtain ⟨k,hk,hkv⟩ := hw
  let g := (f.symm.trans k).trans f
  refine ⟨g,⟨?_,conjugate_preserves_partition f.symm r k hk.2⟩,?_⟩
  · change f*k*f⁻¹ ∈ A0 m n
    exact (A0 m n).mul_mem ((A0 m n).mul_mem hf hk.1) ((A0 m n).inv_mem hf)
  · change f (k (f.symm (f x))) = v
    rw [f.symm_apply_apply,hkv,f.apply_symm_apply]

/-- All related non-corner border vertices have colour-preserving A0 witnesses. -/
theorem ordinary_internal_border_transitivity {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (r : Setoid (Fin m × Fin n)) (hr : IsEquitable (G m n) r)
    (u v : Fin m × Fin n) (hu : gridLayer u = 1)
    (hc : (G m n).degree u ≠ 2) (huv : r u v) :
    ∃ g ∈ Hpi r, g u = v := by
  rcases internal_border_frame hm hn u hu hc with h | h
  · obtain ⟨f,hf,j,hj,hjn,hfu⟩ := h
    let s := transportPartition f.symm r
    have hs := transport_equitable f.symm r hr
    have hrel : s (⟨0,by omega⟩,j) (f.symm v) := by
      change r (f (⟨0,by omega⟩,j)) (f (f.symm v))
      simpa only [hfu,f.apply_symm_apply] using huv
    have hw := top_internal_transitivity hm hn s hs j hj hjn (f.symm v) hrel
    simpa only [hfu] using frame_witness_back r f hf (⟨0,by omega⟩,j) v hw
  · obtain ⟨f,hf,i,hi,him,hfu⟩ := h
    let s := transportPartition f.symm r
    have hs := transport_equitable f.symm r hr
    have hrel : s (i,⟨0,by omega⟩) (f.symm v) := by
      change r (f (i,⟨0,by omega⟩)) (f (f.symm v))
      simpa only [hfu,f.apply_symm_apply] using huv
    have hw := left_internal_transitivity hm hn s hs i hi him (f.symm v) hrel
    simpa only [hfu] using frame_witness_back r f hf (i,⟨0,by omega⟩) v hw

/-- The last ordinary-border obligation, without exceptions or additional premises. -/
theorem ordinary_border_transitivity : OrdinaryBorderTransitivity := by
  intro m n hm hn _ r hr u v hu huv
  by_cases hc : (G m n).degree u = 2
  · exact ordinary_corner_transitivity hm hn r hr u v hc huv
  · exact ordinary_internal_border_transitivity hm hn r hr u v hu hc huv

/-- Every positive grid has precisely the orbit partition of its Hpi subgroup. -/
theorem main_orbit_proved : MainOrbit :=
  main_orbit_of_ordinary_border ordinary_border_transitivity
end Grid343536
