import Characterization
namespace AK350721
open Finset MvPolynomial
open scoped Classical

theorem contributing9 :
    univ.filter (fun pi : Equiv.Perm (Fin 9) =>
      cycleGe 3 pi ∧ rlmv pi = R9 ∧ excv pi = E9) = {p0, p1, p2, p4, p5} := by
  ext pi
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hc, hr, he⟩
    have h := (characterization9 pi).mp ⟨hr, he⟩
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [p0_cycle, p1_cycle, p2_cycle, p3_cycle, p4_cycle, p5_cycle, p6_cycle, p7_cycle]
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact ⟨p0_cycle, p0_sets⟩
    · exact ⟨p1_cycle, p1_sets⟩
    · exact ⟨p2_cycle, p2_sets⟩
    · exact ⟨p4_cycle, p4_sets⟩
    · exact ⟨p5_cycle, p5_sets⟩

theorem coefficient9 : (rawSum 9 3).coeff m9 = -1 := by
  rw [m9, coeff_rawSum, contributing9]
  have h0 : p0 ∉ ({p1, p2, p4, p5} : Finset _) := by decide
  have h1 : p1 ∉ ({p2, p4, p5} : Finset _) := by decide
  have h2 : p2 ∉ ({p4, p5} : Finset _) := by decide
  have h4 : p4 ∉ ({p5} : Finset _) := by decide
  simp only [sum_insert h0, sum_insert h1, sum_insert h2, sum_insert h4,
    sum_singleton, p0_inv, p1_inv, p2_inv, p4_inv, p5_inv]
  norm_num

theorem coefficient9_normalized : (F 9 3).coeff m9 = -1 := by
  simpa [F] using coefficient9

theorem conjecture_refuted : ¬ VoRConj ∧ ¬ MathDBConj := by
  constructor
  · intro h
    have hc := (h 9 3 (by norm_num) (by norm_num)).coeff_nonneg m9
    rw [coefficient9_normalized] at hc
    norm_num at hc
  · intro h
    have hc := (h 9 3 (by norm_num) (by norm_num)).coeff_nonneg m9
    rw [coefficient9] at hc
    norm_num at hc
end AK350721
