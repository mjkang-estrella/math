import ShoeRelabel
example : Shoe.HasMatch (fun _ : ℕ => (0 : ℕ)) 2 := by
  exact ⟨0,0,by omega,by omega,rfl⟩
example : ¬ Shoe.HasMatch (fun k : ℕ => k) 2 := by
  rintro ⟨a,b,_,_,h⟩
  change 2*a = 2*b+1 at h
  omega
