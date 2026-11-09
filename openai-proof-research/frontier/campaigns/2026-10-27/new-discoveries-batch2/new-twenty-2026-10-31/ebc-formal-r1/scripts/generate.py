import pathlib
from collections import deque
from fractions import Fraction
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ebc-formal-r1')
adj=lambda x:[(x+j)%32 for j in [1,7,9,-1,-7,-9]]
d=[-1]*32;s=[0]*32;d[0]=0;s[0]=1;q=deque([0])
while q:
 x=q.popleft()
 for y in adj(x):
  if d[y]<0:d[y]=d[x]+1;q.append(y)
  if d[y]==d[x]+1:s[y]+=s[x]
def D(a,b):return d[(b-a)%32]
def S(a,b):return s[(b-a)%32]
def term(u,v,x,y):
 if x==y:return 0
 return ((S(x,u)*S(v,y) if D(x,u)+1+D(v,y)==D(x,y) else 0)+(S(x,v)*S(u,y) if D(x,v)+1+D(u,y)==D(x,y) else 0))*(103320//S(x,y))
rows={e:[sum(term(0,e,x,y) for y in range(32)) for x in range(32)] for e in [1,9]}
assert sum(rows[1])==15169*168 and sum(rows[9])==15172*168
out='''import Definitions
namespace EBC337062
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Source-zero BFS distance and multiplicity data, computed independently in this lane. -/
'''
for name,arr in [('distance0',d),('count0',s)]:
 out+=f'def {name} (x : ℕ) : ℕ :=\n  match x with\n'
 for i,v in enumerate(arr):out+=f'  | {i} => {v}\n'
 out+='  | _ => 0\n\n'
out+='''def tabDist (x y : ℕ) : ℕ := distance0 ((y + 32 - x) % 32)
def tabCount (x y : ℕ) : ℕ := count0 ((y + 32 - x) % 32)
/-- Oriented splitting numerator. This is arithmetic, not yet identified with paths. -/
def oriented (x y u v : ℕ) : ℕ :=
  if tabDist x u + 1 + tabDist v y = tabDist x y then
    tabCount x u * tabCount v y else 0

def scaledTerm (x y u v : ℕ) : ℕ :=
  if x = y then 0 else
    (oriented x y u v + oriented x y v u) * (103320 / tabCount x y)
def scaledRow (u v x : ℕ) : ℕ :=
  ((List.range 32).map (fun y => scaledTerm x y u v)).sum

'''
for e in [1,9]:
 for x,r in enumerate(rows[e]):out+=f'theorem row_{e}_{x} : scaledRow 0 {e} {x} = {r} := by decide\n'
 out+=f'\ntheorem scaled_total_{e} : ((List.range 32).map (scaledRow 0 {e})).sum = {sum(rows[e])} := by\n  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons,\n    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, '
 out+=', '.join(f'row_{e}_{x}' for x in range(32))+']\n  norm_num\n\n'
out+='''theorem fractions_differ : (15169 / 615 : ℚ) ≠ 15172 / 615 := by norm_num
end EBC337062
'''
(L/'src/Arithmetic.lean').write_text(out)
(L/'logs/independent-arithmetic.txt').write_text(f'distance={d}\ncounts={s}\nrows={rows}\n')
p=L/'src/Arithmetic.lean'
a=p.read_text().replace('end EBC337062','')
a+='''def rationalTerm (x y u v : ℕ) : ℚ :=
  if x = y then 0 else
    ((oriented x y u v + oriented x y v u : ℕ) : ℚ) / tabCount x y
def rationalRow (u v x : ℕ) : ℚ :=
  ((List.range 32).map (fun y => rationalTerm x y u v)).sum
'''
for e in [1,9]:
 for x,r in enumerate(rows[e]):a+=f'theorem rational_row_{e}_{x} : rationalRow 0 {e} {x} = ({r} : ℚ) / 103320 := by decide\n'
 a+=f'\ntheorem rational_total_{e} : ((List.range 32).map (rationalRow 0 {e})).sum = ({15169 if e==1 else 15172} : ℚ) / 615 := by\n  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons,\n    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, '
 a+=', '.join(f'rational_row_{e}_{x}' for x in range(32))+']\n  norm_num\n\n'
a+='end EBC337062\n';p.write_text(a)
