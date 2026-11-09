module
public import GridExceptional
@[expose] public section
namespace Grid343536
theorem free_column_path (m : ℕ) (hm : 1 ≤ m) : HasFreeVertex (G m 1) := by
  let z : Fin m := ⟨0, by omega⟩
  refine ⟨(z,0), ?_⟩
  intro g hg
  have hr : IsEquitable (G m 1) (Setoid.ker (id : Fin m × Fin 1 → _)) := by
    intro u v h w
    change u = v at h
    subst v
    rfl
  have he := row_determinism (Setoid.ker (id : Fin m × Fin 1 → _)) hr g
    (by
      intro j h0
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact hg)
  apply DFunLike.ext
  intro x
  exact he x

theorem free_vertex_iso {V W : Type*} {F : SimpleGraph V} {E : SimpleGraph W}
    (f : F ≃g E) (h : HasFreeVertex F) : HasFreeVertex E := by
  obtain ⟨x,hx⟩ := h
  refine ⟨f x, ?_⟩
  intro g hg
  have he := hx ((f.trans g).trans f.symm) (by
    change f.symm (g (f x)) = x
    rw [hg]
    exact f.symm_apply_apply x)
  apply DFunLike.ext
  intro y
  have hi := congrArg (fun a : F ≃g F => a (f.symm y)) he
  change f.symm (g (f (f.symm y))) = f.symm y at hi
  apply f.symm.injective
  simpa using hi

theorem free_row_path (n : ℕ) (hn : 1 ≤ n) : HasFreeVertex (G 1 n) :=
  free_vertex_iso (transpose n 1) (free_column_path n hn)
end Grid343536
