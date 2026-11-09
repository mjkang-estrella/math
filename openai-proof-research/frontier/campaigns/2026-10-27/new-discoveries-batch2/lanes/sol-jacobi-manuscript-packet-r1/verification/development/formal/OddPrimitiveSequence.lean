import MidpointPrimitive

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace JacobiShifted.MidpointRational
open JacobiShifted.BinaryFiltration

/-- The canonical odd coordinate is divisible at every bidegree.
Even `j` gives zero, including the zero parameter bidegree. -/
theorem h_extracted_divisible (n i j : ℕ) :
    (2 : Midpoint.ZPoly)^sigma (i+j-1) ∣
      Midpoint.oddExtract ((Midpoint.h n).coeff (bidegree i j)).im := by
  rcases Nat.even_or_odd j with hj | hj
  · rw [Midpoint.h_even_j_im_zero n i j hj, Midpoint.oddExtract_zero]
    exact dvd_zero _
  · exact Midpoint.h_odd_extraction_divisible n i j hj

/-- Closed existence and uniqueness for the actual integral midpoint sequence.
There is no recurrence, degree support, or primitive-selection premise. -/
theorem h_odd_primitive_existsUnique (n i j : ℕ) (hn : Odd n) :
    ∃! p : QAlg,
      delta p = lift ((Midpoint.h n).coeff (bidegree i j)) ∧ tau p = -p := by
  obtain ⟨hr,hi⟩ := Midpoint.h_odd_order_coordinates n hn (bidegree i j)
  obtain ⟨A,hA⟩ := Midpoint.integral_normalForm _ hr hi
    (Midpoint.h_coefficient_re_divisible n (bidegree i j))
  rw [hA]
  exact normalForm_primitive_existsUnique _ _

/-- Any later primitive identified by its derivative and tau normalization
inherits this midpoint bound, for every `n,i,j` in the stated range. -/
theorem h_odd_primitive_midpoint (n i j : ℕ) (hn : Odd n) (p : QAlg)
    (hd : delta p = lift ((Midpoint.h n).coeff (bidegree i j)))
    (ht : tau p = -p) :
    TwoLocal (midpoint p / (2 : ℚ)^sigma (i+j-1)) := by
  obtain ⟨hr,hi⟩ := Midpoint.h_odd_order_coordinates n hn (bidegree i j)
  obtain ⟨A,hA⟩ := Midpoint.integral_normalForm _ hr hi
    (Midpoint.h_coefficient_re_divisible n (bidegree i j))
  have he : p = primitive A (Midpoint.oddExtract ((Midpoint.h n).coeff (bidegree i j)).im) :=
    primitive_unique _ _ (hd.trans (congrArg lift hA)) ht
  rw [he]
  exact primitive_midpoint_twoLocal _ _ _ (h_extracted_divisible n i j)

/-- Even `j` has midpoint exactly zero; no divisibility assumption on the real part. -/
theorem h_odd_primitive_midpoint_even (n i j : ℕ) (hn : Odd n) (hj : Even j) (p : QAlg)
    (hd : delta p = lift ((Midpoint.h n).coeff (bidegree i j)))
    (ht : tau p = -p) : midpoint p=0 := by
  obtain ⟨hr,hi⟩ := Midpoint.h_odd_order_coordinates n hn (bidegree i j)
  obtain ⟨A,hA⟩ := Midpoint.integral_normalForm _ hr hi
    (Midpoint.h_coefficient_re_divisible n (bidegree i j))
  have he : p = primitive A (Midpoint.oddExtract ((Midpoint.h n).coeff (bidegree i j)).im) :=
    primitive_unique _ _ (hd.trans (congrArg lift hA)) ht
  rw [he, primitive_midpoint, Midpoint.h_even_j_im_zero n i j hj, Midpoint.oddExtract_zero]
  simp

/-- The zero parameter bidegree really is zero in the concrete recurrence. -/
theorem h_zero_parameter (n : ℕ) : (Midpoint.h n).coeff (bidegree 0 0)=0 := by
  simpa [bidegree] using (Midpoint.h_weighted n).1

/-- Its normalized primitive is zero, rather than an excluded degree case. -/
theorem h_zero_parameter_primitive (n : ℕ) (p : QAlg)
    (hd : delta p = lift ((Midpoint.h n).coeff (bidegree 0 0)))
    (ht : tau p = -p) : p=0 := by
  apply normalized_kernel _ ht
  simpa [h_zero_parameter] using hd

/-- Single closed endpoint: the unique normalized primitive and its dyadic estimate. -/
theorem h_odd_primitive_closed (n i j : ℕ) (hn : Odd n) :
    ∃! p : QAlg,
      delta p = lift ((Midpoint.h n).coeff (bidegree i j)) ∧ tau p = -p ∧
      TwoLocal (midpoint p / (2 : ℚ)^sigma (i+j-1)) := by
  obtain ⟨p,hp,hu⟩ := h_odd_primitive_existsUnique n i j hn
  exact ⟨p, ⟨hp.1,hp.2,h_odd_primitive_midpoint n i j hn p hp.1 hp.2⟩,
    fun r hr => hu r ⟨hr.1,hr.2.1⟩⟩

end JacobiShifted.MidpointRational
