module
public import GridSideAlignment
@[expose] public section
namespace Grid343536
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-- Align an arbitrary side chart with a related internal point on the top side.
The chart may be reversed; the resulting initial corner flag has matching colours. -/
theorem align_internal_chart {a b m n : ℕ}
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hm : 3 ≤ m) (hn : 3 ≤ n)
    (r : Setoid (Fin m × Fin n)) (hr : IsEquitable (G m n) r)
    (f : G a b ≃g G m n) (j k : ℕ)
    (hj : 0 < j) (hjn : j+1 < n) (hk : 0 < k) (hkb : k+1 < b)
    (hrel : r (⟨0,by omega⟩,⟨j,by omega⟩) (f (⟨0,by omega⟩,⟨k,by omega⟩))) :
    ∃ e : G a b ≃g G m n, ∃ hjb : j < b,
      (e = f ∨ e = (colFlip a b).trans f) ∧ n = b ∧
      e (⟨0,by omega⟩,⟨j,hjb⟩) = f (⟨0,by omega⟩,⟨k,by omega⟩) ∧
      r (e (⟨0,by omega⟩,⟨0,by omega⟩)) (⟨0,by omega⟩,⟨0,by omega⟩) ∧
      r (e (⟨0,by omega⟩,⟨1,by omega⟩)) (⟨0,by omega⟩,⟨1,by omega⟩) := by
  have hrB := restricted_equitable _ r hr {x | gridLayer x = 1} (by
    intro x y h
    change gridLayer x = 1 ↔ gridLayer y = 1
    rw [grid_layer_invariant hm hn r hr x y h])
  have hadj := (top_border_neighbors hm hn ⟨j,by omega⟩ hj hjn
    (⟨0,by omega⟩,⟨j-1,by omega⟩)).mpr (Or.inl rfl)
  obtain ⟨z,hz,hzr⟩ := matching_neighbor hrB hrel hadj
  rcases (chart_border_neighbors ha hb hm hn f k (by omega) hk hkb z).mp hz with hz | hz
  · have hp : r ((1 : G m n ≃g G m n) (⟨0,by omega⟩,⟨j-1,by omega⟩))
        (f (⟨0,by omega⟩,⟨k-1,by omega⟩)) := by
      rw [hz] at hzr; exact r.symm hzr
    obtain ⟨he,hlen,h0,h1⟩ := color_internal_side_alignment hm hn ha hb hm hn r hr
      1 f j k hj hjn hk hkb hrel hp
    refine ⟨f,by omega,Or.inl rfl,hlen,?_,r.symm h0,r.symm h1⟩
    subst k; rfl
  · let e := (colFlip a b).trans f
    have hpoint : e (⟨0,by omega⟩,⟨b-1-k,by omega⟩) =
        f (⟨0,by omega⟩,⟨k,by omega⟩) := by
      apply congrArg f
      apply Prod.ext <;> apply Fin.ext <;> simp only [colFlip, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
        Equiv.refl_apply, Fin.revPerm_apply, Fin.val_rev,Fin.val_mk] <;> omega
    have hprev : e (⟨0,by omega⟩,⟨b-1-k-1,by omega⟩) =
        f (⟨0,by omega⟩,⟨k+1,by omega⟩) := by
      apply congrArg f
      apply Prod.ext <;> apply Fin.ext <;> simp only [colFlip, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
        Equiv.refl_apply, Fin.revPerm_apply, Fin.val_rev,Fin.val_mk] <;> omega
    have hp : r ((1 : G m n ≃g G m n) (⟨0,by omega⟩,⟨j-1,by omega⟩))
        (e (⟨0,by omega⟩,⟨b-1-k-1,by omega⟩)) := by
      rw [hprev]; rw [hz] at hzr; exact r.symm hzr
    have hrel' : r ((1 : G m n ≃g G m n) (⟨0,by omega⟩,⟨j,by omega⟩))
        (e (⟨0,by omega⟩,⟨b-1-k,by omega⟩)) := by rw [hpoint]; exact hrel
    obtain ⟨he,hlen,h0,h1⟩ := color_internal_side_alignment hm hn ha hb hm hn r hr
      1 e j (b-1-k) hj hjn (by omega) (by omega) hrel' hp
    refine ⟨e,by omega,Or.inr rfl,hlen,?_,r.symm h0,r.symm h1⟩
    simpa only [he] using hpoint
end Grid343536
