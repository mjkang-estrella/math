module
public import GridLadderLayers
@[expose] public section
namespace Grid343536
set_option linter.unusedSimpArgs false

/-- Determinism from the first row after any change of grid coordinates. -/
theorem transported_row_determinism {m n p q : ℕ}
    (f : G m n ≃g G p q) (r : Setoid (Fin m × Fin n))
    (hr : IsEquitable (G m n) r) (g : G m n ≃g G m n)
    (hrow : ∀ j : Fin q, ∀ h0 : 0 < p,
      r (g (f.symm (⟨0,h0⟩,j))) (f.symm (⟨0,h0⟩,j))) :
    ∀ x, r (g x) x := by
  let s := transportPartition f r
  let k := (f.symm.trans g).trans f
  have hk := row_determinism s (transport_equitable f r hr) k (by
    intro j h0
    change r (f.symm (f (g (f.symm (⟨0,h0⟩,j)))) ) (f.symm (⟨0,h0⟩,j))
    simpa using hrow j h0)
  intro x
  have h := hk (f x)
  change r (f.symm (f (g (f.symm (f x))))) (f.symm (f x)) at h
  simpa using h

/-- Each corner's vertical partner is determined by its colour. -/
theorem ladder_partner_related {n : ℕ} (hn : 3 ≤ n)
    (r : Setoid (Fin 2 × Fin n)) (hr : IsEquitable (G 2 n) r)
    {u v : Fin 2 × Fin n} (hu : ladderLayer u = 1) (huv : r u v) :
    r (rowFlip 2 n u) (rowFlip 2 n v) := by
  have hv := (ladder_layer_invariant hn r hr u v huv).symm.trans hu
  have adj : (G 2 n).Adj u (rowFlip 2 n u) := by
    apply (grid_adj_iff _ _).mpr
    right
    constructor
    · change u.1.val + 1 = (Fin.rev u.1).val ∨ (Fin.rev u.1).val + 1 = u.1.val
      rw [Fin.val_rev]
      have := u.1.isLt
      omega
    · rfl
  obtain ⟨b,hb,hbr⟩ := matching_neighbor hr huv adj
  have hl : ladderLayer b = 1 := by
    have he := ladder_layer_invariant hn r hr b (rowFlip 2 n u) hbr
    change ladderLayer b = ladderLayer u at he
    exact he.trans hu
  have be : b = rowFlip 2 n v := by
    have h := (grid_adj_iff _ _).mp hb
    have bi := b.1.isLt
    have bj := b.2.isLt
    have vi := v.1.isLt
    have vj := v.2.isLt
    unfold ladderLayer at hl hv
    simp only [Fin.ext_iff] at h
    apply Prod.ext
    · apply Fin.ext
      change b.1.val = (Fin.rev v.1).val
      rw [Fin.val_rev]
      omega
    · apply Fin.ext
      change b.2.val = v.2.val
      omega
  exact r.symm (be ▸ hbr)

/-- Colour-preserving reflection witness between any two related ladder corners. -/
theorem ladder_border_transitive {n : ℕ} (hn : 3 ≤ n)
    (r : Setoid (Fin 2 × Fin n)) (hr : IsEquitable (G 2 n) r)
    (u v : Fin 2 × Fin n) (hu : ladderLayer u = 1) (huv : r u v) :
    ∃ g ∈ Hpi r, g u = v := by
  classical
  have hv := (ladder_layer_invariant hn r hr u v huv).symm.trans hu
  let a : G 2 n ≃g G 2 n := if u.1 = v.1 then 1 else rowFlip 2 n
  let b : G 2 n ≃g G 2 n := if u.2 = v.2 then 1 else colFlip 2 n
  let g := a * b
  have ui := u.1.isLt
  have vi := v.1.isLt
  have uj := u.2.isLt
  have vj := v.2.isLt
  have hj : u.2.val + v.2.val = n-1 ∨ u.2 = v.2 := by
    unfold ladderLayer at hu hv
    by_cases he : u.2 = v.2
    · exact Or.inr he
    left
    have hne : u.2.val ≠ v.2.val := fun h => he (Fin.ext h)
    omega
  have hsend : g u = v := by
    apply Prod.ext
    · apply Fin.ext
      dsimp [g,a,b]
      split_ifs <;> simp_all [rowFlip,colFlip,Fin.val_rev,Fin.ext_iff] <;> omega
    · apply Fin.ext
      dsimp [g,a,b]
      split_ifs <;> simp_all [rowFlip,colFlip,Fin.val_rev,Fin.ext_iff] <;> omega
  have hcomm : ∀ x, g (rowFlip 2 n x) = rowFlip 2 n (g x) := by
    intro x
    dsimp [g,a,b]
    split_ifs <;> rfl
  have hcol : ∀ x : Fin 2 × Fin n, x.2 = u.2 → r (g x) x := by
    intro x hx
    have casesx : x = u ∨ x = rowFlip 2 n u := by
      by_cases he : x.1 = u.1
      · exact Or.inl (Prod.ext he hx)
      · right
        change x = (Fin.rev u.1,u.2)
        refine Prod.ext ?_ hx
        apply Fin.ext
        change x.1.val = (Fin.rev u.1).val
        rw [Fin.val_rev]
        have xi := x.1.isLt
        have hne : x.1.val ≠ u.1.val := fun h => he (Fin.ext h)
        omega
    rcases casesx with rfl | rfl
    · rw [hsend]; exact r.symm huv
    · rw [hcomm,hsend]
      exact r.symm (ladder_partner_related hn r hr hu huv)
  refine ⟨g, ⟨Subgroup.mul_mem _ ?_ ?_, ?_⟩, hsend⟩
  · dsimp [a]; split_ifs
    · exact Subgroup.one_mem _
    · exact rowFlip_mem_A0 _ _
  · dsimp [b]; split_ifs
    · exact Subgroup.one_mem _
    · exact colFlip_mem_A0 _ _
  · by_cases hz : u.2.val = 0
    · apply transported_row_determinism (transpose 2 n) r hr g
      intro j h0
      apply hcol
      apply Fin.ext
      exact hz.symm
    · apply transported_row_determinism ((colFlip 2 n).trans (transpose 2 n)) r hr g
      intro j h0
      apply hcol
      apply Fin.ext
      change (Fin.rev (⟨0,h0⟩ : Fin n)).val = u.2.val
      rw [Fin.val_rev]
      simp only [Fin.val_mk]
      unfold ladderLayer at hu
      omega

/-- MainOrbit on every non-square ladder, with no residual premise. -/
theorem main_orbit_ladder (n : ℕ) (hn : 3 ≤ n)
    (r : Setoid (Fin 2 × Fin n)) (hr : IsEquitable (G 2 n) r) :
    r = orbitSetoid (G 2 n) (Hpi r) := by
  apply positive_layer_propagation r hr ladderLayer
  · intro x
    have hi := x.2.isLt
    unfold ladderLayer
    omega
  · exact ladder_layer_invariant hn r hr
  · intro g hg x
    exact (ladder_layer_invariant hn (orbitSetoid (G 2 n) ⊤)
      (orbit_equitable _ _) x (g x) ⟨g,by trivial,rfl⟩).symm
  · exact ladder_layer_step
  · exact ladder_border_transitive hn r hr
end Grid343536
