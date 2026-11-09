from pathlib import Path
D=Path(__file__).resolve().parents[1];p=D/'formal/Riordan.lean';s=p.read_text().replace('import Mathlib.Data.Fin.VecNotation','import Mathlib.Data.Fin.VecNotation\nimport Mathlib.Data.Real.Basic');s=s.split('#print axioms refutation')[0]
s+='''
-- Literal binary Riordan matrix B(z*g,z*g), symmetrized as Definition 2.2.
noncomputable def bell (p : Polynomial ℕ) (i j : ℕ) : ℕ :=
  if i = j then 0 else ((X*p)^(min i j + 1)).coeff (max i j) % 2

theorem bell_source (i j : ℕ) : bell g i j = sourceEntry i j := by
  by_cases h : i = j
  · simp [bell, sourceEntry, h]
  · have hm : min i j + 1 ≤ max i j := by omega
    simp only [bell, sourceEntry, h, if_false, mul_pow, coeff_X_pow_mul', hm, if_true]
    congr 2 <;> omega

def xR : Fin 15 → ℝ := fun i => x i

theorem kernelR : ∀ i : Fin 15, ∑ j : Fin 15, (entry i j : ℝ) * xR j = 0 := by
  intro i
  fin_cases i <;> norm_num [entries, xR, x, Fin.sum_univ_succ]

def SourceConjecture : Prop := ∀ (p : Polynomial ℕ) (n : ℕ), p.coeff 0 % 2 = 1 →
  (∀ i j : Fin (n/2), bell p (2*i.val+1) (2*j.val+1) = 0) →
  (∀ i j : Fin ((n+1)/2), bell p (2*i.val) (2*j.val) = bell p i j) →
  ∀ v : Fin n → ℝ, (∃ k, v k ≠ 0) →
  (∀ i, ∑ j : Fin n, (bell p i j : ℝ) * v j = 0) →
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
''';p.write_text(s)
