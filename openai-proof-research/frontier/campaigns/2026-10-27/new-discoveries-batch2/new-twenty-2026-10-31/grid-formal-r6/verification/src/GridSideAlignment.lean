module
public import GridCornerColors
@[expose] public section
namespace Grid343536
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-- Backwards propagation from matching adjacent internal points, with explicit bounds. -/
theorem color_side_backward {a b c d m n : ℕ}
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) (hd : 3 ≤ d)
    (hm : 3 ≤ m) (hn : 3 ≤ n)
    (r : Setoid (Fin m × Fin n)) (hr : IsEquitable (G m n) r)
    (f : G a b ≃g G m n) (g : G c d ≃g G m n)
    (j k : ℕ) (hj : 0 < j) (hjb : j+1 < b) (hk : 0 < k) (hkd : k+1 < d)
    (hzero : r (f (⟨0,by omega⟩,⟨j,by omega⟩)) (g (⟨0,by omega⟩,⟨k,by omega⟩)))
    (hone : r (f (⟨0,by omega⟩,⟨j-1,by omega⟩)) (g (⟨0,by omega⟩,⟨k-1,by omega⟩))) :
    ∀ t, t ≤ min j k →
      r (f (⟨0,by omega⟩,⟨j-t,by omega⟩)) (g (⟨0,by omega⟩,⟨k-t,by omega⟩)) := by
  have hrB := restricted_equitable _ r hr {x | gridLayer x = 1} (by
    intro x y h
    change gridLayer x = 1 ↔ gridLayer y = 1
    rw [grid_layer_invariant hm hn r hr x y h])
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht
    by_cases h0 : t = 0
    · subst t; simpa only [Nat.sub_zero] using hzero
    by_cases h1 : t = 1
    · subst t; exact hone
    have hja : j-(t-1)+1 = j-(t-2) := by omega
    have hjb' : j-(t-1)-1 = j-t := by omega
    have hka : k-(t-1)+1 = k-(t-2) := by omega
    have hkb' : k-(t-1)-1 = k-t := by omega
    have h := two_neighbor_color _ r hrB
      (ih (t-1) (by omega) (by omega))
      (ih (t-2) (by omega) (by omega))
      (b := f (⟨0,by omega⟩,⟨j-t,by omega⟩))
      (d := g (⟨0,by omega⟩,⟨k-t,by omega⟩))
      (by intro he; have h := congrArg (fun x => (f.symm x).2.val) he; simp only [f.symm_apply_apply,g.symm_apply_apply,Fin.val_mk] at h; omega)
      (by intro he; have h := congrArg (fun x => (g.symm x).2.val) he; simp only [f.symm_apply_apply,g.symm_apply_apply,Fin.val_mk] at h; omega)
      (by intro z; simpa only [hja,hjb',or_comm] using
        chart_border_neighbors ha hb hm hn f (j-(t-1)) (by omega) (by omega) (by omega) z)
      (by intro z; simpa only [hka,hkb',or_comm] using
        chart_border_neighbors hc hd hm hn g (k-(t-1)) (by omega) (by omega) (by omega) z)
    exact h

/-- First-corner timing aligns the positions of matching oriented internal flags. -/
theorem color_side_position_eq {a b c d m n : ℕ}
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) (hd : 3 ≤ d)
    (hm : 3 ≤ m) (hn : 3 ≤ n)
    (r : Setoid (Fin m × Fin n)) (hr : IsEquitable (G m n) r)
    (f : G a b ≃g G m n) (g : G c d ≃g G m n)
    (j k : ℕ) (hj : 0 < j) (hjb : j+1 < b) (hk : 0 < k) (hkd : k+1 < d)
    (hzero : r (f (⟨0,by omega⟩,⟨j,by omega⟩)) (g (⟨0,by omega⟩,⟨k,by omega⟩)))
    (hone : r (f (⟨0,by omega⟩,⟨j-1,by omega⟩)) (g (⟨0,by omega⟩,⟨k-1,by omega⟩))) : j = k := by
  have h := color_side_backward ha hb hc hd hm hn r hr f g j k hj hjb hk hkd
    hzero hone (min j k) (Nat.le_refl _)
  have he := corner_colour_invariant r hr h
  rw [f.degree_eq,g.degree_eq,grid_degree_formula,grid_degree_formula] at he
  simp only [Fin.val_mk,Nat.lt_irrefl,show 0+1<a by omega,
    show 0+1<c by omega,show j-min j k+1<b by omega,
    show k-min j k+1<d by omega,↓reduceIte] at he
  split_ifs at he <;> omega

/-- Matching internal flags align both their coordinates and the full side lengths. -/
theorem color_internal_side_alignment {a b c d m n : ℕ}
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) (hd : 3 ≤ d)
    (hm : 3 ≤ m) (hn : 3 ≤ n)
    (r : Setoid (Fin m × Fin n)) (hr : IsEquitable (G m n) r)
    (f : G a b ≃g G m n) (g : G c d ≃g G m n)
    (j k : ℕ) (hj : 0 < j) (hjb : j+1 < b) (hk : 0 < k) (hkd : k+1 < d)
    (hzero : r (f (⟨0,by omega⟩,⟨j,by omega⟩)) (g (⟨0,by omega⟩,⟨k,by omega⟩)))
    (hone : r (f (⟨0,by omega⟩,⟨j-1,by omega⟩)) (g (⟨0,by omega⟩,⟨k-1,by omega⟩))) :
    j = k ∧ b = d ∧
      r (f (⟨0,by omega⟩,⟨0,by omega⟩)) (g (⟨0,by omega⟩,⟨0,by omega⟩)) ∧
      r (f (⟨0,by omega⟩,⟨1,by omega⟩)) (g (⟨0,by omega⟩,⟨1,by omega⟩)) := by
  have he := color_side_position_eq ha hb hc hd hm hn r hr f g j k hj hjb hk hkd hzero hone
  subst k
  have h := color_side_backward ha hb hc hd hm hn r hr f g j j hj hjb hj hkd hzero hone
  have h0 := h j (by omega)
  have h1 := h (j-1) (by omega)
  have h0' : r (f (⟨0,by omega⟩,⟨0,by omega⟩)) (g (⟨0,by omega⟩,⟨0,by omega⟩)) := by
    simpa only [Nat.sub_self] using h0
  have h1' : r (f (⟨0,by omega⟩,⟨1,by omega⟩)) (g (⟨0,by omega⟩,⟨1,by omega⟩)) := by
    simpa only [show j-(j-1)=1 by omega] using h1
  exact ⟨rfl,color_side_length_eq ha hb hc hd hm hn r hr f g h0' h1',h0',h1'⟩
end Grid343536
