import pathlib,re,math,json
lane=pathlib.Path(__file__).resolve().parent.parent
seed=list(map(int,re.search(r'def seed20 : List ℕ := \[(.*?)\]',(lane/'StackSortFinal.lean').read_text()).group(1).split(',')))
g=seed[:]
for n in range(21,131):
 g.append(4*g[-1]+sum(math.comb(n-1,i)*g[i]*g[n-1-i] for i in range(1,n-1)))
assert str(g[130])==re.search(r'def lower130 : ℕ := (\d+)',(lane/'StackSortCertificate.lean').read_text()).group(1)
(lane/'lower-table.json').write_text(json.dumps(g,indent=2)+'\n')
s='''import StackSortInj2Lower
namespace StackSort
open BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 0
/-- Literal bottom-up data; every entry is checked against the recursion below. -/
def lowerTable : List ℕ := ['''+','.join(map(str,g))+''']
def tableValue (n : ℕ) : ℕ := lowerTable[n]!
def evalRhs (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  4 * f (n-1) + ∑ i ∈ Finset.Icc 1 (n-2),
    ((n-1).factorial / (i.factorial * (n-1-i).factorial)) * f i * f (n-1-i)
theorem rootRhs_eq_evalRhs (f : ℕ → ℕ) {n : ℕ} (hn : 2 ≤ n) :
    rootRhs f n = evalRhs f n := by
  unfold rootRhs evalRhs
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.choose_eq_factorial_div_factorial (by have := (Finset.mem_Icc.mp hi).2; omega)]
end StackSort
'''
(lane/'StackSortInj2Table.lean').write_text(s)
for j in range(6):
 start=21+20*j;end=min(131,start+20)
 prev='StackSortInj2Table' if j==0 else f'StackSortInj2Rows{j-1}'
 s=f'import {prev}\nnamespace StackSort\nset_option maxRecDepth 10000\nset_option maxHeartbeats 0\n'
 for n in range(start,end):
  s+=f'theorem lower_row_{n} : tableValue {n} = evalRhs tableValue {n} := by decide\n'
 s+='end StackSort\n'
 (lane/f'StackSortInj2Rows{j}.lean').write_text(s)
print('generated rows 21..130; G130 matches frozen lower130')
