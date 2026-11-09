import TotalBits
namespace XorMagic
variable {V : Type} [Fintype V] [DecidableEq V]

theorem connected_of_high_degree [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (reg : G.IsRegularOfDegree d) (high : Fintype.card V ≤ 2*d) :
    G.Connected := by
  classical
  refine ⟨?_⟩
  intro u v
  by_contra h
  let U := insert u (G.neighborFinset u)
  let W := insert v (G.neighborFinset v)
  have reach : ∀ a b, b ∈ insert a (G.neighborFinset a) → G.Reachable a b := by
    intro a b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact SimpleGraph.Reachable.rfl
    · exact ((G.mem_neighborFinset a b).mp hb).reachable
  have dis : Disjoint U W := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact h ((reach u x hx).trans (reach v x hy).symm)
  have cu : U.card = d+1 := by simp [U, reg u]
  have cw : W.card = d+1 := by simp [W, reg v]
  have bound := Finset.card_le_univ (s := U ∪ W)
  rw [Finset.card_union_of_disjoint dis, cu, cw] at bound
  omega

theorem closed_to_open_compl {n d : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph V) [DecidableRel G.Adj] (reg : G.IsRegularOfDegree d)
    (magic : ClosedMagic G n) (high : Fintype.card V ≤ 2*(Fintype.card V-1-d)) :
    OpenMagic Gᶜ n := by
  classical
  obtain ⟨conn, l, hl⟩ := magic
  have : Nonempty V := conn.nonempty
  refine ⟨connected_of_high_degree Gᶜ reg.compl high, l, ?_⟩
  intro v
  rw [complement_identity G l (total_labels hn l) v]
  exact hl v

theorem open_to_closed_compl {n d : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph V) [DecidableRel G.Adj] (reg : G.IsRegularOfDegree d)
    (magic : OpenMagic G n) (high : Fintype.card V ≤ 2*(Fintype.card V-1-d)) :
    ClosedMagic Gᶜ n := by
  classical
  obtain ⟨conn, l, hl⟩ := magic
  have : Nonempty V := conn.nonempty
  refine ⟨connected_of_high_degree Gᶜ reg.compl high, l, ?_⟩
  intro v
  rw [complement_identity G l (total_labels hn l) v, hl v, add_zero]
  exact bits_add_self _
end XorMagic
