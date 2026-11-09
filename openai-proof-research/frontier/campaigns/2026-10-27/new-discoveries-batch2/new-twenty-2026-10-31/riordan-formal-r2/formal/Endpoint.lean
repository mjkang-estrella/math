import Table
import Mathlib.Algebra.BigOperators.Fin
namespace Riordan
open Polynomial Finset
def A : Fin 15 → Fin 15 → ℤ := fun i j => entry i j

def x : Fin 15 → ℤ := ![-1,1,0,0,-1,1,0,1,1,-2,0,1,1,-1,1]
theorem entries : ∀ i j : Fin 15, entry i j = ![![0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1], ![1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], ![1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0], ![0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0], ![1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0], ![0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1], ![1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]] i j := by
  intro i
  fin_cases i
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14

theorem kernel : ∀ i : Fin 15, ∑ j : Fin 15, A i j * x j = 0 := by
  intro i
  fin_cases i <;> norm_num [A, entries, x, Fin.sum_univ_succ]
theorem odd_nonzero : x 0 ≠ 0 := by decide
-- Even source vertices are odd zero-based indices; their induced graph is null.
theorem even_independent : ∀ i j : Fin 7, entry (2*i.val+1) (2*j.val+1) = 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num
-- Odd source vertices induce exactly the smaller Riordan graph for the SAME g.
theorem odd_copy : ∀ i j : Fin 8, entry (2*i.val) (2*j.val) = entry i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num

-- Literal source conjecture: for every proper Bell-type Riordan coefficient sequence,
-- finite io-decomposability forces the odd coordinates of each zero eigenvector to vanish.
-- We specialize its universal quantifier only to the explicit polynomial g.
theorem refutation :
    g.coeff 0 = 1 ∧
    (∀ i j : Fin 7, sourceEntry (2*i.val+1) (2*j.val+1) = 0) ∧
    (∀ i j : Fin 8, sourceEntry (2*i.val) (2*j.val) = sourceEntry i j) ∧
    (∃ v : Fin 15 → ℤ, (∀ i : Fin 15, ∑ j : Fin 15,
      (sourceEntry i j : ℤ) * v j = 0) ∧ v 0 ≠ 0) := by
  refine ⟨by norm_num [g_coeff, gc], ?_, ?_, x, ?_, odd_nonzero⟩
  · simpa only [← entry_source] using even_independent
  · simpa only [← entry_source] using odd_copy
  · simpa only [← entry_source, A] using kernel

-- Literal binary Riordan matrix B(z*g,z*g), symmetrized as Definition 2.2.
noncomputable def bell (p : Polynomial ℕ) (i j : ℕ) : ℕ :=
  if i = j then 0 else ((X*p)^(min i j + 1)).coeff (max i j) % 2

theorem bell_source (i j : ℕ) : bell g i j = sourceEntry i j := by
  by_cases h : i = j
  · simp [bell, sourceEntry, h]
  · have hm : min i j + 1 ≤ max i j := by omega
    simp only [bell, sourceEntry, h, ite_false, mul_pow, coeff_X_pow_mul', hm, ite_true]
    congr 2

def xR : Fin 15 → ℝ := fun i => x i

theorem kernelR : ∀ i : Fin 15, ∑ j : Fin 15, (entry i j : ℝ) * xR j = 0 := by
  intro i
  fin_cases i <;> norm_num [entries, xR, x, Fin.sum_univ_succ]

def SourceConjecture : Prop := ∀ (p : Polynomial ℕ) (n : ℕ), p.coeff 0 % 2 = 1 →
  (∀ i j : Fin (n/2), bell p (2*i.val+1) (2*j.val+1) = 0) →
  (∀ i j : Fin ((n+1)/2), bell p (2*i.val) (2*j.val) = bell p i j) →
  ∀ v : Fin n → ℝ, (∃ k, v k ≠ 0) →
  (∀ i : Fin n, ∑ j : Fin n, (bell p i j : ℝ) * v j = 0) →
  ∀ i : Fin ((n+1)/2), v ⟨2*i.val, by omega⟩ = 0

theorem source_conjecture_false : ¬ SourceConjecture := by
  intro H
  have hp : g.coeff 0 % 2 = 1 := by norm_num [g_coeff, gc]
  have he : ∀ i j : Fin (15/2), bell g (2*i.val+1) (2*j.val+1) = 0 := by
    simpa only [bell_source, ← entry_source] using even_independent
  have ho : ∀ i j : Fin ((15+1)/2), bell g (2*i.val) (2*j.val) = bell g i j := by
    simpa only [bell_source, ← entry_source] using odd_copy
  have hv : ∃ k, xR k ≠ 0 := ⟨0, by norm_num [xR, x]⟩
  have hk : ∀ i : Fin 15, ∑ j : Fin 15, (bell g i j : ℝ) * xR j = 0 := by
    simpa only [bell_source, ← entry_source] using kernelR
  have bad := H g 15 hp he ho xR hv hk (0 : Fin 8)
  norm_num [xR, x] at bad

#print axioms source_conjecture_false
end Riordan
