import Bridge
namespace AK350721
open Finset MvPolynomial
open scoped Classical

def R9 : Finset (Fin 9) := {0, 4, 6, 7}
def E9 : Finset (Fin 9) := {1, 2, 3, 5, 8}
noncomputable def m9 := degreeSet R9 E9

/-- The increasing order of minimum values forces the same order of positions. -/
theorem minima_positions {n : ℕ} (pi : Equiv.Perm (Fin n))
    {u v : Fin n} (_hu : u ∈ rlmv pi) (hv : v ∈ rlmv pi) (h : u < v) :
    pi.symm u < pi.symm v := by
  by_contra hh
  have hne : pi.symm v ≠ pi.symm u := fun he => ne_of_lt h (pi.symm.injective he).symm
  have hlt : pi.symm v < pi.symm u := lt_of_le_of_ne (le_of_not_gt hh) hne
  have hv' := (Finset.mem_filter.mp hv).2 (pi.symm u) hlt
  simp only [Equiv.apply_symm_apply] at hv'
  exact (not_lt_of_ge (le_of_lt h)) hv'

theorem last_mem {n : ℕ} (pi : Equiv.Perm (Fin (n+1))) : pi (Fin.last n) ∈ rlmv pi := by
  simp only [rlmv, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
  intro j hj
  exact False.elim (not_lt_of_ge (Fin.le_last j) hj)

theorem forced9 (pi : Equiv.Perm (Fin 9)) (hr : rlmv pi = R9) (he : excv pi = E9) :
    pi.symm 1 = 0 ∧ pi.symm 2 = 1 ∧ pi.symm 3 = 2 ∧ pi.symm 7 = 8 := by
  have ex (v : Fin 9) (h : v ∈ E9) : pi.symm v < v := by
    have := h; rw [← he] at this; exact (Finset.mem_filter.mp this).2
  have e1 := ex 1 (by decide)
  have e2 := ex 2 (by decide)
  have e3 := ex 3 (by decide)
  have i12 := pi.symm.injective.ne (show (1 : Fin 9) ≠ 2 by decide)
  have i13 := pi.symm.injective.ne (show (1 : Fin 9) ≠ 3 by decide)
  have i23 := pi.symm.injective.ne (show (2 : Fin 9) ≠ 3 by decide)
  have h1 : pi.symm 1 = 0 := by apply Fin.ext; omega
  have h2 : pi.symm 2 = 1 := by apply Fin.ext; have := Fin.val_injective.ne i12; omega
  have h3 : pi.symm 3 = 2 := by
    apply Fin.ext
    have := Fin.val_injective.ne i13
    have := Fin.val_injective.ne i23
    omega
  refine ⟨h1, h2, h3, ?_⟩
  have hl := last_mem pi
  rw [hr] at hl
  have h7 : (7 : Fin 9) ∈ rlmv pi := by rw [hr]; decide
  have hlast : pi (8 : Fin 9) ≤ 7 := by
    have : pi (8 : Fin 9) ∈ R9 := hl
    simp only [R9, mem_insert, mem_singleton] at this
    rcases this with h | h | h | h <;> omega
  by_contra hne
  have hlt : pi (8 : Fin 9) < 7 := lt_of_le_of_ne hlast (fun h => hne ((pi.eq_symm_apply.mpr h).symm))
  have hp := minima_positions pi (last_mem pi) h7 hlt
  simp only [Equiv.symm_apply_apply] at hp
  exact (not_lt_of_ge (Fin.le_last _)) hp
end AK350721
