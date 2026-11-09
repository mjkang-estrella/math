import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];p=D/'formal/Riordan.lean';s=p.read_text().split('end Riordan')[0];s=s.replace('import Mathlib.Tactic\n','import Mathlib.Tactic\n')
a=[[int(n==0) for n in range(14)]];gc=[int(n in [0,1,3,6,7,8,12,13]) for n in range(14)]
for k in range(1,15):a.append([sum(gc[i]*a[k-1][n-i] for i in range(n+1)) for n in range(14)])
for k in range(15):
 for n in range(15-k):
  if n>13:continue
  names=', '.join(f'pc_{k-1}_{i}' for i in range(n+1)) if k else ''
  s+=f'theorem pc_{k}_{n} : pc {k} {n} = {a[k][n]} := by\n  norm_num [pc, sum_range_succ, gc'+(', '+names if names else '')+']\n'
s+='''
-- The coefficient formula is Definition 2.2, in zero-based vertex indices:
-- [z^(i-j-1)] g^(j+1), reduced modulo 2.
def entry (i j : ℕ) : ℕ :=
  if i = j then 0 else pc (min i j + 1) (max i j - min i j - 1) % 2
noncomputable def sourceEntry (i j : ℕ) : ℕ :=
  if i = j then 0 else (g ^ (min i j + 1)).coeff (max i j - min i j - 1) % 2
theorem entry_source (i j : ℕ) : entry i j = sourceEntry i j := by
  simp only [entry, sourceEntry, pc_coeff]

def A : Fin 15 → Fin 15 → ℤ := fun i j => entry i j

def x : Fin 15 → ℤ := ![-1,1,0,0,-1,1,0,1,1,-2,0,1,1,-1,1]
'''
names=', '.join(f'pc_{k}_{n}' for k in range(15) for n in range(min(14,15-k)))
s+='theorem entries : ∀ i j : Fin 15, entry i j = '+str(json.loads((D/'outputs/riordan-witness.json').read_text())['A']).replace('[[','![![').replace('], [','], ![').replace(']]',']]')+' i j := by\n  intro i j\n  fin_cases i <;> fin_cases j <;> norm_num [entry, '+names+']\n'
s+='''
theorem kernel : ∀ i : Fin 15, ∑ j : Fin 15, A i j * x j = 0 := by
  intro i
  fin_cases i <;> norm_num [A, entries, x, Fin.sum_univ_succ]
theorem odd_nonzero : x 0 ≠ 0 := by decide
-- Even source vertices are odd zero-based indices; their induced graph is null.
theorem even_independent : ∀ i j : Fin 7, entry (2*i.val+1) (2*j.val+1) = 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [entry, PCNAMES]
-- Odd source vertices induce exactly the smaller Riordan graph for the SAME g.
theorem odd_copy : ∀ i j : Fin 8, entry (2*i.val) (2*j.val) = entry i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [entry, PCNAMES]

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
  · simpa only [← entry_source] using kernel
#print axioms refutation
end Riordan
'''.replace('PCNAMES',names)
p.write_text(s)
