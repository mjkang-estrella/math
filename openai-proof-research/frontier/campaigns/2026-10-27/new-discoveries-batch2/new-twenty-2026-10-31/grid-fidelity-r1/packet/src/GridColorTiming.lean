module
public import GridColorFlags
@[expose] public section
namespace Grid343536
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-- Border restriction also commutes with isomorphisms between different dimensions. -/
def borderIso {a b m n : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hm : 3 ≤ m) (hn : 3 ≤ n) (f : G a b ≃g G m n) :
    restrictedGraph (G a b) {x | gridLayer x = 1} ≃g
      restrictedGraph (G m n) {x | gridLayer x = 1} where
  toEquiv := f.toEquiv
  map_rel_iff' := by
    intro x y
    change ((G m n).Adj (f x) (f y) ∧ gridLayer (f x) = 1 ∧ gridLayer (f y) = 1) ↔
      ((G a b).Adj x y ∧ gridLayer x = 1 ∧ gridLayer y = 1)
    rw [f.map_rel_iff, grid_layer_one hm hn, grid_layer_one hm hn,
      grid_layer_one ha hb, grid_layer_one ha hb, f.degree_eq, f.degree_eq]

/-- Concrete side charts have precisely the two adjacent chart points as border neighbours. -/
theorem chart_border_neighbors {a b m n : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hm : 3 ≤ m) (hn : 3 ≤ n) (f : G a b ≃g G m n)
    (k : ℕ) (hk : k < b) (hl : 0 < k) (hu : k+1 < b)
    (z : Fin m × Fin n) :
    (restrictedGraph (G m n) {x | gridLayer x = 1}).Adj
      (f (⟨0,by omega⟩,⟨k,hk⟩)) z ↔
      z = f (⟨0,by omega⟩,⟨k-1,by omega⟩) ∨
      z = f (⟨0,by omega⟩,⟨k+1,hu⟩) := by
  have h := (borderIso ha hb hm hn f).map_rel_iff
    (a := (⟨0,by omega⟩,⟨k,hk⟩)) (b := f.symm z)
  change ((restrictedGraph (G m n) {x | gridLayer x = 1}).Adj
    (f (⟨0,by omega⟩,⟨k,hk⟩)) (f (f.symm z)) ↔ _) at h
  simpa only [f.apply_symm_apply,
    top_border_neighbors ha hb ⟨k,hk⟩ hl hu,
    f.symm_apply_eq] using h

/-- Matching oriented side charts agree in colour throughout their common prefix. -/
theorem color_side_prefix {a b c d m n : ℕ}
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) (hd : 3 ≤ d)
    (hm : 3 ≤ m) (hn : 3 ≤ n)
    (r : Setoid (Fin m × Fin n)) (hr : IsEquitable (G m n) r)
    (f : G a b ≃g G m n) (g : G c d ≃g G m n)
    (hzero : r (f (⟨0,by omega⟩,⟨0,by omega⟩)) (g (⟨0,by omega⟩,⟨0,by omega⟩)))
    (hone : r (f (⟨0,by omega⟩,⟨1,by omega⟩)) (g (⟨0,by omega⟩,⟨1,by omega⟩))) :
    ∀ k (hkb : k < b) (hkd : k < d),
      r (f (⟨0,by omega⟩,⟨k,hkb⟩)) (g (⟨0,by omega⟩,⟨k,hkd⟩)) := by
  have hrB := restricted_equitable _ r hr {x | gridLayer x = 1} (by
    intro x y h
    change gridLayer x = 1 ↔ gridLayer y = 1
    rw [grid_layer_invariant hm hn r hr x y h])
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hkb hkd
    by_cases h0 : k = 0
    · subst k; exact hzero
    by_cases h1 : k = 1
    · subst k; exact hone
    have he : k-1+1 = k := by omega
    have h := two_neighbor_color _ r hrB
      (ih (k-1) (by omega) (by omega) (by omega))
      (ih (k-1-1) (by omega) (by omega) (by omega))
      (a := f (⟨0,by omega⟩,⟨k-1-1,by omega⟩))
      (b := f (⟨0,by omega⟩,⟨k-1+1,by omega⟩))
      (c := g (⟨0,by omega⟩,⟨k-1-1,by omega⟩))
      (d := g (⟨0,by omega⟩,⟨k-1+1,by omega⟩))
      (fun h => top_side_nonbacktracking (by omega) ⟨k-1,by omega⟩
        (by dsimp; omega) (by dsimp; omega) (f.injective h))
      (fun h => top_side_nonbacktracking (by omega) ⟨k-1,by omega⟩
        (by dsimp; omega) (by dsimp; omega) (g.injective h))
      (chart_border_neighbors ha hb hm hn f (k-1) (by omega) (by omega) (by omega))
      (chart_border_neighbors hc hd hm hn g (k-1) (by omega) (by omega) (by omega))
    simpa only [he] using h

/-- First-corner timing forces equality of the lengths of matching side charts. -/
theorem color_side_length_eq {a b c d m n : ℕ}
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) (hd : 3 ≤ d)
    (hm : 3 ≤ m) (hn : 3 ≤ n)
    (r : Setoid (Fin m × Fin n)) (hr : IsEquitable (G m n) r)
    (f : G a b ≃g G m n) (g : G c d ≃g G m n)
    (hzero : r (f (⟨0,by omega⟩,⟨0,by omega⟩)) (g (⟨0,by omega⟩,⟨0,by omega⟩)))
    (hone : r (f (⟨0,by omega⟩,⟨1,by omega⟩)) (g (⟨0,by omega⟩,⟨1,by omega⟩))) : b = d := by
  have h := color_side_prefix ha hb hc hd hm hn r hr f g hzero hone
    (min b d - 1) (by omega) (by omega)
  have he := corner_colour_invariant r hr h
  rw [f.degree_eq, g.degree_eq, grid_degree_formula, grid_degree_formula] at he
  simp only [Fin.val_mk, Nat.lt_irrefl, show 0+1<a by omega,
    show 0+1<c by omega, show 0<min b d-1 by omega, ↓reduceIte] at he
  split_ifs at he <;> omega
end Grid343536
