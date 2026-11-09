import ShoeRelabel
-- The sole semantic mutation replaces the constant sample by distinct colors.
-- A noninjective code would identify them; the source experiment cannot.
example : Shoe.HasMatch (fun k : ℕ => k) 2 := by
  exact ⟨0,0,by omega,by omega,by change 0 = 1; omega⟩
