import CodeLoopTransport
example : ∃ e : Equiv.Perm (Fin 50), ∀ v, v ∈ D50 0 ↔ (fun c => v (e.symm c)) ∈ D50 1 := by
  exact D50_no_permutation
