module
public import GridSideRigidity
@[expose] public section
set_option linter.unusedSimpArgs false
namespace Grid343536

theorem nonsquare_free {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) (hne : m ≠ n) :
    HasFreeVertex (G m n) := by
  let z : Fin m × Fin n := (⟨0,by omega⟩,⟨0,by omega⟩)
  let a : Fin m × Fin n := (⟨0,by omega⟩,⟨1,by omega⟩)
  refine ⟨z, ?_⟩
  intro g hg
  have ha : (G m n).Adj z a := (grid_adj_iff _ _).mpr (Or.inl ⟨rfl,Or.inl rfl⟩)
  have hb := g.map_rel_iff.mpr ha
  rw [hg] at hb
  rcases (grid_adj_iff _ _).mp hb with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · have he : g a = a := by
      refine Prod.ext ?_ ?_
      · exact h1.symm
      apply Fin.ext
      change 0+1 = (g a).2.val ∨ (g a).2.val+1 = 0 at h2
      change (g a).2.val = 1
      omega
    exact fixed_flag_identity hm hn g hg he
  · have he : g a = (⟨1,by omega⟩,⟨0,by omega⟩) := by
      refine Prod.ext ?_ ?_
      rotate_left
      · exact h2.symm
      apply Fin.ext
      change 0+1 = (g a).1.val ∨ (g a).1.val+1 = 0 at h1
      change (g a).1.val = 1
      omega
    have hh := side_length_eq hm hn hn hm (g.trans (transpose m n))
      (by change (transpose m n) (g z) = _; rw [hg]; rfl)
      (by change (transpose m n) (g a) = _; rw [he]; rfl)
    exact False.elim (hne hh.symm)

theorem near_corner_unique {m n : ℕ} (hm : 3 ≤ m) (hn : 4 ≤ n)
    (x : Fin m × Fin n)
    (ha : (G m n).Adj (⟨0,by omega⟩,⟨1,by omega⟩) x)
    (hd : (G m n).degree x = 2) :
    x = (⟨0,by omega⟩,⟨0,by omega⟩) := by
  have hi := x.1.isLt
  have hj := x.2.isLt
  have ha' := (grid_adj_iff _ _).mp ha
  simp only [Fin.ext_iff, Fin.val_mk] at ha'
  rw [grid_degree_formula] at hd
  have hx : x.1.val = 0 ∧ x.2.val = 0 := by
    split_ifs at hd <;> omega
  exact Prod.ext (Fin.ext hx.1) (Fin.ext hx.2)

theorem large_square_free (n : ℕ) (hn : 4 ≤ n) : HasFreeVertex (G n n) := by
  let a : Fin n × Fin n := (⟨0,by omega⟩,⟨1,by omega⟩)
  let z : Fin n × Fin n := (⟨0,by omega⟩,⟨0,by omega⟩)
  refine ⟨a, ?_⟩
  intro g hg
  have hz : g z = z := by
    apply near_corner_unique (by omega) hn
    · have ha : (G n n).Adj a z := (grid_adj_iff _ _).mpr (Or.inl ⟨rfl,Or.inr rfl⟩)
      have hh := g.map_rel_iff.mpr ha
      rw [hg] at hh
      exact hh
    · rw [g.degree_eq, grid_degree_formula]
      simp only [z, Fin.val_mk, Nat.lt_irrefl, show 0+1 < n by omega, ↓reduceIte]
  exact fixed_flag_identity (by omega) (by omega) g hz hg

/-- Round 4 closes the full-automorphism free-vertex classification. -/
theorem free_classification : FreeClassification := by
  intro m n hm hn
  constructor
  · exact GridFinal2.free_implies_nonexceptional m n
  · intro h
    by_cases hm1 : m = 1
    · subst m; exact free_row_path n hn
    by_cases hn1 : n = 1
    · subst n; exact free_column_path m hm
    by_cases hm2 : m = 2
    · subst m
      exact ladder_free n (by omega)
    by_cases hn2 : n = 2
    · subst n
      exact free_vertex_iso (transpose 2 m) (ladder_free m (by omega))
    by_cases he : m = n
    · subst n
      exact large_square_free m (by omega)
    · exact nonsquare_free (by omega) (by omega) he
end Grid343536
