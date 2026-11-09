import ShoeColorControls
-- Semantic mutation: dropping injectivity would turn the distinct sequence
-- into a constant sequence with a first match. This claimed original match
-- must fail, at its asserted color equality 0 = 1.
example : Shoe.HasMatch (fun k : ℕ => k) 2 := by
  exact ⟨0,0,by omega,by omega,by omega⟩
