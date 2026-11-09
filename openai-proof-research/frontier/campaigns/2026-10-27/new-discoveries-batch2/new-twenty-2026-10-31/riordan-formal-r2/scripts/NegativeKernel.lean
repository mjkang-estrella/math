import EndpointStrong
example : ∀ i : Fin 8, Riordan.xR ⟨2*i.val, by omega⟩ = 0 := by
  intro i
  fin_cases i <;> norm_num [Riordan.xR, Riordan.x]
