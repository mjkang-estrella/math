import ShoeControls

/- Intentional semantic mutation: a repeated LEFT color at times 0 and 2
is asserted to cause a match even though the sole RIGHT shoe has color 1.
The claimed color equality 0=1 must fail in the kernel elaborator. -/
example : Shoe.FirstMatch (fun n : ℕ => if n = 1 then 1 else 0) 2 := by
  constructor
  · exact ⟨1, 0, by omega, by omega, rfl⟩
  · rintro ⟨a,b,ha,hb,he⟩
    omega
