import PDTAR.FinalComplete
open PDTAR
private def added : SimpleGraph (Fin 3 ⊕ Fin 3) where
  Adj x y := match x,y with
    | Sum.inl a, Sum.inl b => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)
    | Sum.inr _, Sum.inr _ => False
    | _,_ => True
  symm := ⟨by intro x y; cases x <;> cases y <;> simp_all only <;> tauto⟩
  loopless := ⟨by intro x; cases x <;> simp; omega⟩
example : Nonempty (added ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
  have hn : ¬ Nonempty (added ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
    rintro ⟨e⟩
    have hab : added.Adj (Sum.inl 0) (Sum.inl 1) := by change ((0 : Fin 3) = 0 ∧ (1 : Fin 3) = 1) ∨ ((0 : Fin 3) = 1 ∧ (1 : Fin 3) = 0); decide
    have hbc : added.Adj (Sum.inl 1) (Sum.inr 0) := by trivial
    have hca : added.Adj (Sum.inr 0) (Sum.inl 0) := by trivial
    exact small_bipartite_no_triangle _ _ _ (e.map_rel_iff.mpr hab)
      (e.map_rel_iff.mpr hbc) (e.map_rel_iff.mpr hca)
  exfalso
  simp_all
