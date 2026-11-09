module
public import GridLattice
@[expose] public section
namespace Grid343536
open Finset

theorem neighborCells_automorphism {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r : Setoid V) (g : G ≃g G) (u : V) :
    neighborCells G r (g u) =
      (by classical exact ((univ.filter (G.Adj u)).val).map (fun x => Quotient.mk r (g x))) := by
  classical
  have he : (univ.filter (G.Adj u)).map g.toEquiv.toEmbedding =
      univ.filter (G.Adj (g u)) := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact g.map_rel_iff.mpr hy
    · intro hx
      exact ⟨g⁻¹ x, by simpa using (g⁻¹).map_rel_iff.mpr hx, by simp⟩
  rw [neighborCells, ← he, map_val, Multiset.map_map]
  rfl

/-- If all but one entries agree, equal colour multisets force the last entries to agree. -/
theorem last_color_determined {V C : Type*} [DecidableEq V]
    (S : Finset V) {w : V} (hw : w ∈ S) (c d : V → C)
    (hm : S.val.map c = S.val.map d)
    (hk : ∀ x ∈ S, x ≠ w → c x = d x) : c w = d w := by
  classical
  have he : (S.erase w).val.map c = (S.erase w).val.map d := by
    apply Multiset.map_congr rfl
    intro x hx
    have hx' := mem_erase.mp (show x ∈ S.erase w from hx)
    exact hk x hx'.2 hx'.1
  have hins : w ∉ S.erase w := by simp
  rw [← insert_erase hw, insert_val_of_notMem hins, Multiset.map_cons, Multiset.map_cons, he] at hm
  simpa using hm

/-- The single-unknown-neighbour step used in row, column and side-walk determinism. -/
theorem unique_neighbor_determinism {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r : Setoid V) (hr : IsEquitable G r) (g : G ≃g G) {u w : V}
    (hu : r (g u) u) (huw : G.Adj u w)
    (hknown : ∀ x, G.Adj u x → x ≠ w → r (g x) x) : r (g w) w := by
  classical
  apply Quotient.exact
  apply last_color_determined (univ.filter (G.Adj u)) (by simpa using huw)
    (fun x => Quotient.mk r (g x)) (Quotient.mk r)
  · rw [← neighborCells_automorphism G r g u]
    change neighborCells G r (g u) = neighborCells G r u
    exact (equitable_iff_neighborCells G r).mp hr _ _ hu
  · intro x hx hne
    exact Quotient.sound (hknown x (mem_filter.mp hx).2 hne)

/-- Agreement on the first row forces agreement everywhere. -/
theorem row_determinism {m n : ℕ} (r : Setoid (Fin m × Fin n))
    (hr : IsEquitable (G m n) r) (g : G m n ≃g G m n)
    (hrow : ∀ j : Fin n, ∀ h0 : 0 < m, r (g (⟨0, h0⟩, j)) (⟨0, h0⟩, j)) :
    ∀ x, r (g x) x := by
  have key : ∀ k, ∀ i : Fin m, i.val = k → ∀ j : Fin n, r (g (i,j)) (i,j) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi j
      cases k with
      | zero =>
        have he : i = ⟨0, by have := i.isLt; omega⟩ := Fin.ext hi
        rw [he]
        exact hrow j _
      | succ k =>
        let a : Fin m × Fin n := (⟨k, by have := i.isLt; omega⟩, j)
        apply unique_neighbor_determinism (G m n) r hr g
          (u := a) (w := (i,j))
        · exact ih k (by omega) a.1 rfl j
        · apply (grid_adj_iff _ _).mpr
          exact Or.inr ⟨Or.inl hi.symm, rfl⟩
        · intro x hx hne
          have hsmall : x.1.val < k + 1 := by
            rcases (grid_adj_iff a x).mp hx with ⟨hfst, _⟩ | ⟨hfst, hsnd⟩
            · have he : x.1.val = k := congrArg Fin.val hfst.symm
              omega
            · rcases hfst with hfst | hfst
              · have he : x = (i,j) := Prod.ext (Fin.ext (by change k + 1 = x.1.val at hfst; change x.1.val = i.val; omega)) hsnd.symm
                exact False.elim (hne he)
              · change x.1.val + 1 = k at hfst
                omega
          exact ih x.1.val hsmall x.1 rfl x.2
  intro x
  exact key x.1.val x.1 rfl x.2
end Grid343536
