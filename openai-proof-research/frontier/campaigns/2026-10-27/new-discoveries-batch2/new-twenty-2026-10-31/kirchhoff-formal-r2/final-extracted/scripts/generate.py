from pathlib import Path
import json
from fractions import Fraction as F
D=Path(__file__).resolve().parents[1];data=json.loads((D/'inputs/kirchhoff-formal-r1/outputs/exact-independent.json').read_text())
def mat(a):return '!!['+';\n'.join(', '.join('('+str(x)+')' for x in row) for row in a)+']'
def mul(a,b):return [[sum((F(a[i][k])*F(b[k][j]) for k in range(11)),F(0)) for j in range(11)] for i in range(11)]
s='import Basic\nnamespace Kirchhoff\nopen Matrix\nset_option maxRecDepth 100000\nset_option maxHeartbeats 8000000\n'
for alpha,name in [('0','Zero'),('1','One')]:
 v=data['variants'][alpha];s+=f'def L{name} : Mat 11 := {mat(v["L"])}\n'
 for key,label in [('mp_inverse','MP'),('group_inverse','GI')]:
  a=v['L'];x=v[key];p=mul(a,x);q=mul(x,a)
  for nm,val in [(label+name,x),('P'+label+name,p),('Q'+label+name,q)]:s+=f'def {nm} : Mat 11 := {mat(val)}\n'
  N=label+name
  for i,eq in enumerate([f'L{name} * {N} = P{N}',f'{N} * L{name} = Q{N}',f'P{N} * L{name} = L{name}',f'Q{N} * {N} = {N}']):s+=f'theorem cert{N}{i} : {eq} := by decide +kernel\n'
  if label=='MP':
   s+=f'theorem symP{N} : (P{N}).transpose = P{N} := by decide +kernel\ntheorem symQ{N} : (Q{N}).transpose = Q{N} := by decide +kernel\n'
   s+=f'theorem valid{N} : Penrose L{name} {N} := by\n unfold Penrose\n rw [cert{N}0, cert{N}1]\n exact ⟨cert{N}2, cert{N}3, symP{N}, symQ{N}⟩\n'
  else:
   s+=f'theorem pq{N} : P{N} = Q{N} := by decide +kernel\ntheorem valid{N} : GroupInverse L{name} {N} := by\n unfold GroupInverse\n rw [cert{N}0, cert{N}1]\n exact ⟨cert{N}2, cert{N}3, pq{N}⟩\n'
s+='def pairIndex {n : ℕ} (X : Mat n) : ℚ := ∑ i, ∑ j, if i < j then X i i + X j j - X i j - X j i else 0\ndef spectralIndex {n : ℕ} (X : Mat n) : ℚ := n * Matrix.trace X\n'
for nm,expr,val in [('mp0','pairIndex MPZero','370/3'),('mp1','pairIndex MPOne','515538204/7137235'),('gi0','spectralIndex GIZero','370/3'),('gi1','spectralIndex GIOne','1696684/14035')]:s+=f'theorem {nm} : {expr} = {val} := by decide +kernel\n'
s+='end Kirchhoff\n';(D/'formal/Certificates.lean').write_text(s)
