module
public import GridBorderWalk
@[expose] public section
namespace Grid343536
set_option linter.unusedSimpArgs false

/-- Literal two-neighbour rule on the interior of the top side, including side length 3. -/
theorem top_border_neighbors {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (j : Fin n) (hleft : 0 < j.val) (hright : j.val+1 < n)
    (z : Fin m × Fin n) :
    (restrictedGraph (G m n) {x | gridLayer x = 1}).Adj (⟨0,by omega⟩,j) z ↔
      z = (⟨0,by omega⟩,⟨j.val-1,by omega⟩) ∨
      z = (⟨0,by omega⟩,⟨j.val+1,hright⟩) := by
  have zi := z.1.isLt
  have zj := z.2.isLt
  change ((G m n).Adj (⟨0,by omega⟩,j) z ∧
    gridLayer (⟨0,by omega⟩,j) = 1 ∧ gridLayer z = 1) ↔ _
  simp only [grid_adj_iff,Prod.ext_iff,Fin.ext_iff,Fin.val_mk]
  unfold gridLayer
  dsimp
  omega

/-- The preceding and following vertices of this side are distinct. -/
theorem top_side_nonbacktracking {m n : ℕ} (hm : 0 < m)
    (j : Fin n) (hleft : 0 < j.val) (hright : j.val+1 < n) :
    ((⟨0,hm⟩,⟨j.val-1,by omega⟩) : Fin m × Fin n) ≠
      (⟨0,hm⟩,⟨j.val+1,hright⟩) := by
  intro h
  have := congrArg (fun x : Fin m × Fin n => x.2.val) h
  dsimp at this
  omega

/-- Corner status, as required for first-corner timing, is a cell invariant. -/
theorem corner_colour_invariant {m n : ℕ} (r : Setoid (Fin m × Fin n))
    (hr : IsEquitable (G m n) r) {u v : Fin m × Fin n} (huv : r u v) :
    ((G m n).degree u = 2 ↔ (G m n).degree v = 2) := by
  have hd := equitable_degree (G m n) r hr huv
  have he : (G m n).degree u = (G m n).degree v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree]
    convert hd using 1 <;> apply congrArg Finset.card <;> ext a <;> simp
  rw [he]
end Grid343536
