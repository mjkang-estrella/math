import InfiniteFamily
example : Riordan.h 6 = (if (7:ℕ) ∈ ([1,9,13] : List ℕ) then 1 else 0) := by
  have hh : Riordan.h 6 = 1 := by simpa using Riordan.h_even 3
  norm_num at *
