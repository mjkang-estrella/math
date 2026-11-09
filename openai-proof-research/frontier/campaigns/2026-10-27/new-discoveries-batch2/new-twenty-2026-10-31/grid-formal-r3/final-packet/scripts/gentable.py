from pathlib import Path
p=Path(__file__).resolve().parent.parent
f=[lambda i,j:(i,j),lambda i,j:(1-i,j),lambda i,j:(i,1-j),lambda i,j:(1-i,1-j),lambda i,j:(j,i),lambda i,j:(1-j,i),lambda i,j:(j,1-i),lambda i,j:(1-j,1-i)]
pts=[(0,0),(0,1),(1,0),(1,1)]
perms=[tuple(fn(*x) for x in pts) for fn in f]
table=[[perms.index(tuple(fn(*fm(*x)) for x in pts)) for fm in f] for fn in f]
s='  !['+',\n    '.join('!['+','.join(map(str,row))+']' for row in table)+']\n'
s+='''theorem symTable_closed : ∀ h : Fin 10, ∀ i ∈ subIndices h, ∀ j ∈ subIndices h,
    symTable i j ∈ subIndices h := by decide
theorem symTable_one : ∀ h : Fin 10, (0 : Fin 8) ∈ subIndices h := by decide
theorem symTable_inv : ∀ h : Fin 10, ∀ i ∈ subIndices h,
    ∃ j ∈ subIndices h, symTable i j = 0 ∧ symTable j i = 0 := by decide
theorem sym8_mul (k : ℕ) (hk : k = 2 ∨ k = 3) (i j : Fin 8) :
    sym8 k i * sym8 k j = sym8 k (symTable i j) := by
  rcases hk with rfl | rfl
  all_goals
    fin_cases i <;> fin_cases j <;> ext x
    obtain ⟨a,b⟩ := x
    fin_cases a <;> fin_cases b <;> rfl
def explicitSubgroup (k : ℕ) (hk : k = 2 ∨ k = 3) (h : Fin 10) :
    Subgroup (G k k ≃g G k k) where
  carrier := {g | ∃ i ∈ subIndices h, g = sym8 k i}
  one_mem' := ⟨0, symTable_one h, rfl⟩
  mul_mem' := by
    rintro g f ⟨i,hi,rfl⟩ ⟨j,hj,rfl⟩
    exact ⟨symTable i j, symTable_closed h i hi j hj, sym8_mul k hk i j⟩
  inv_mem' := by
    rintro g ⟨i,hi,rfl⟩
    obtain ⟨j,hj,hij,_⟩ := symTable_inv h i hi
    refine ⟨j,hj, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    rw [sym8_mul k hk, hij]
    rfl
end Grid343536
'''
(p/'src/GridExceptionalSubgroups.lean').open('a').write(s)
