module
public import GridFinal5
@[expose] public section
namespace Grid343536
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-- Restriction to the border commutes with every actual grid automorphism. -/
def borderAut {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (g : G m n ≃g G m n) :
    restrictedGraph (G m n) {x | gridLayer x = 1} ≃g
      restrictedGraph (G m n) {x | gridLayer x = 1} where
  toEquiv := g.toEquiv
  map_rel_iff' := by
    intro x y
    change ((G m n).Adj (g x) (g y) ∧ gridLayer (g x) = 1 ∧ gridLayer (g y) = 1) ↔ _
    rw [g.map_rel_iff, grid_layer_automorphism hm hn g x,
      grid_layer_automorphism hm hn g y]
    rfl

/-- Two matching colours on an oriented top corner flag determine the entire side. -/
theorem color_flag_row {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (r : Setoid (Fin m × Fin n)) (hr : IsEquitable (G m n) r)
    (g : G m n ≃g G m n)
    (hzero : r (g (⟨0,by omega⟩,⟨0,by omega⟩)) (⟨0,by omega⟩,⟨0,by omega⟩))
    (hone : r (g (⟨0,by omega⟩,⟨1,by omega⟩)) (⟨0,by omega⟩,⟨1,by omega⟩)) :
    ∀ j : Fin n, r (g (⟨0,by omega⟩,j)) (⟨0,by omega⟩,j) := by
  let B := restrictedGraph (G m n) {x | gridLayer x = 1}
  have hb : IsEquitable B r := restricted_equitable _ r hr _ (by
    intro x y h
    change gridLayer x = 1 ↔ gridLayer y = 1
    rw [grid_layer_invariant hm hn r hr x y h])
  have key : ∀ k (hk : k < n),
      r (g (⟨0,by omega⟩,⟨k,hk⟩)) (⟨0,by omega⟩,⟨k,hk⟩) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases h0 : k = 0
      · subst k; exact hzero
      by_cases h1 : k = 1
      · subst k; exact hone
      apply unique_neighbor_determinism B r hb (borderAut hm hn g)
        (u := (⟨0,by omega⟩,⟨k-1,by omega⟩))
      · exact ih (k-1) (by omega) (by omega)
      · exact (top_border_neighbors hm hn ⟨k-1,by omega⟩ (by dsimp; omega)
          (by dsimp; omega) _).mpr (Or.inr (by apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega))
      · intro x hx hne
        rcases (top_border_neighbors hm hn ⟨k-1,by omega⟩ (by dsimp; omega)
          (by dsimp; omega) x).mp hx with hx | hx
        · subst x
          exact ih (k-1-1) (by omega) (by omega)
        · exact False.elim (hne (by simpa only [show k-1+1=k by omega] using hx))
  intro j
  exact key j.val j.isLt

/-- An actual A0 symmetry matching an oriented corner flag belongs to Hpi. -/
theorem color_flag_mem_Hpi {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (r : Setoid (Fin m × Fin n)) (hr : IsEquitable (G m n) r)
    (g : G m n ≃g G m n) (hg : g ∈ A0 m n)
    (hzero : r (g (⟨0,by omega⟩,⟨0,by omega⟩)) (⟨0,by omega⟩,⟨0,by omega⟩))
    (hone : r (g (⟨0,by omega⟩,⟨1,by omega⟩)) (⟨0,by omega⟩,⟨1,by omega⟩)) :
    g ∈ Hpi r := by
  refine ⟨hg, row_determinism r hr g ?_⟩
  intro j h0
  exact color_flag_row hm hn r hr g hzero hone j
end Grid343536
