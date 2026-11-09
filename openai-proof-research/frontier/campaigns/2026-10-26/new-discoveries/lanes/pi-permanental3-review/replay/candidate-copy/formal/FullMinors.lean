import PermanentThree

namespace PermanentalThree

/-- Literal positivity of every square minor, selected in increasing row/column order. -/
def AllMinorsPositive (A : Mat3) : Prop :=
  ∀ n : ℕ, n ≤ 3 → ∀ r c : Fin n → Fin 3,
    StrictMono r → StrictMono c → 0 < (A.submatrix r c).det

theorem strictTP3_iff_allMinors (A : Mat3) : StrictTP3 A ↔ AllMinorsPositive A := by
  constructor
  · intro h n hn r c hr hc
    interval_cases n
    · simp
    · simpa [Matrix.det_unique] using h.1 (r 0) (c 0)
    · simpa only [Matrix.det_fin_two, Matrix.submatrix_apply] using
        h.2.1 (r 0) (r 1) (c 0) (c 1) (hr (by decide)) (hc (by decide))
    · have hrid : r = id := hr.eq_id
      have hcid : c = id := hc.eq_id
      simpa [hrid, hcid] using h.2.2
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      have hh := h 1 (by norm_num) (fun _ => i) (fun _ => j)
        (by intro a b hab; omega) (by intro a b hab; omega)
      simpa [Matrix.det_unique] using hh
    · intro i j k l hij hkl
      have hr : StrictMono (![i,j] : Fin 2 → Fin 3) := by
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp_all
      have hc : StrictMono (![k,l] : Fin 2 → Fin 3) := by
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp_all
      have hh := h 2 (by norm_num) ![i,j] ![k,l] hr hc
      rw [Matrix.det_fin_two] at hh
      simpa using hh
    · simpa using h 3 (by norm_num) id id strictMono_id strictMono_id

end PermanentalThree
