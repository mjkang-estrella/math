import ZeckBase
#check @Finsupp.update_apply
#check @Finsupp.update
example (a : Pos) (i : ℕ) : (a.update 3 7) i = if i = 3 then 7 else a i := by
  simp [Finsupp.update_apply]
example (a : Pos) (i : ℕ) : (a.update 3 7) 3 = 7 := by
  simp [Finsupp.update_apply]
