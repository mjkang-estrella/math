import ShoeColorEndpoint

namespace Shoe

/-- Coding a finite alphabet leaves every unused Nat color at exactly zero. -/
theorem finite_zeroExtension_outside (n : ℕ) (p : PMF (Fin n)) (m : ℕ) (hm : n ≤ m) :
    (p.map Fin.val) m = 0 := by
  classical
  rw [PMF.map_apply]
  have hz (a : Fin n) : ¬ m = a.val := by
    intro h
    have ha := a.isLt
    omega
  simp [hz]

theorem distinct_chronology_no_match (n : ℕ) : ¬ HasMatch (fun k : ℕ => k) n := by
  rintro ⟨a,b,_,_,h⟩
  change 2*a = 2*b+1 at h
  omega

/-- Both a singleton law and a law with a zero coordinate instantiate the
full source-defined endpoint without positive-support assumptions. -/
example : colorDiscrepancy (PMF.pure (0 : Fin 1)) 0 ≤ 255/256 :=
  countable_color_discrepancy_bound _ _

example : (PMF.map Fin.val (PMF.pure (0 : Fin 2))) 2 = 0 :=
  finite_zeroExtension_outside 2 _ 2 (by omega)

example (p : PMF (Fin 3)) :
    colorDiscrepancy p 0 = sourceDiscrepancy (p.map Fin.val) 0 :=
  finite_zeroExtension_discrepancy 3 p 0

end Shoe
