import PolynexusLiteral
-- Independent review controls, outside immutable production.
example : psi 0 = 0 := by
  have h := polynexus_integer 0
  norm_num at h
  omega
example (X : Matrix (Fin 0) (Fin 0) ℕ) : X ∈ PSourceMn 0 ↔ X = 0 := by
  constructor
  · intro h
    rcases h with h | ⟨d,k,m,hl,_⟩
    · exact h
    · obtain ⟨h1,h2,h3,_⟩ := hl
      omega
  · exact Or.inl
example : psi 1 = 1 := polynexus_one
example (n : ℕ) : (psi n : ℚ) =
    ((n+1:ℚ)^7-(n:ℚ)^7-(n+1:ℚ)^3+(n:ℚ)^3)/120 := by
  have h := polynexus_rational n
  linear_combination (1/120:ℚ)*h
example : PSrcLeg 2 (-1) 2 2 := by norm_num [PSrcLeg]
example : PSrc 2 (-1) 2 2 = PBlk 2 1 0 0 := by
  have h := PSrc_eq_PBlk (show PSrcLeg 2 (-1) 2 2 by norm_num [PSrcLeg])
  simpa [srcA,srcB,srcE] using h
example : PBlk 2 0 0 1 (0 : Fin 2) (1 : Fin 2) = 0 := by
  apply PBlk_eq_zero
  norm_num [PCnd]
-- A shared middle endpoint is overlap, while adjacency is zero.
example : PBlk 3 0 1 1 * PBlk 3 2 0 0 ≠ 0 := by
  apply PBlk_mul_nonzero <;> omega
example : PBlk 3 0 0 0 * PBlk 3 1 0 0 = 0 := by
  apply PBlk_mul_disjoint_zero <;> omega
example : (PBlk 3 0 1 1 * PBlk 3 2 0 0) (0 : Fin 3) (0 : Fin 3) = 0 := by
  rw [PBlk_mul_entry]
  · have h : ¬ PMulWit 0 1 1 2 0 0 0 0 := by
      rintro ⟨u,v,hu,hv,hr,hj,hk⟩
      omega
    exact if_neg h
  · omega
example : (PBlk 3 0 1 1 * PBlk 3 2 0 0) (1 : Fin 3) (0 : Fin 3) = 1 := by
  rw [PBlk_mul_entry]
  · exact if_pos ⟨1,0,by omega,by omega,rfl,rfl,rfl⟩
  · omega
#print axioms polynexus_literal
#print axioms PNZ_source
#print axioms polynexus_one
