from pathlib import Path
from fractions import Fraction as F
import csv,itertools,math,json
L=Path(__file__).resolve().parent
rows=list(csv.reader((L/'witness-table.csv').open()))[1:]
V={tuple(map(int,r[0])):tuple(map(int,r[1:])) for r in rows}
assert len(rows)==len(V)==729
edges=list(itertools.combinations(range(4),2));count=0
for s,v in V.items():
 assert min(v)>=0 and sum(v)==48
 for k,(i,j) in enumerate(edges):
  if s[k]<2:
   t=list(s);t[k]+=1;w=V[tuple(t)]
   assert w[i]>=v[i] and w[j]<=v[j]
 for p in itertools.permutations(range(4)):
  M=[[1]*4 for _ in range(4)]
  for (i,j),a in zip(edges,s):M[p[i]][p[j]]=a;M[p[j]][p[i]]=2-a
  w=V[tuple(M[i][j] for i,j in edges)]
  assert all(w[p[i]]==v[i] for i in range(4))
  count+=1
coeff=[F(0)]*5
for s in itertools.product(range(3),repeat=4):
 a=4-s.count(1);b=s.count(1);v=V[s[0],2,2,s[1],s[2],s[3]]
 for j in range(b+1):coeff[a+j]+=F(v[0]+v[1],48)*math.comb(b,j)*(-2)**j
assert coeff==[F(1,4),F(15,4),-F(17,2),F(185,24),-F(11,4)]
N=32
t=sum((F(math.comb(N,k),2**N)*max(1-F(2*k,N),0) for k in range(N+1)),F(0))
assert t==F(math.comb(32,16),2**33)
answer=sum(c*t**j for j,c in enumerate(coeff))
assert answer<F(1,2)
P=[[F(1,2),F(1,2),F(1),F(1)],[F(1,2)]*4,[F(0),F(1,2),F(1,2),F(1,2)],[F(0),F(1,2),F(1,2),F(1,2)]]
assert all(P[i][j]>=P[i+1][j] for i in range(3) for j in range(4))
assert all(P[i][j]<=P[i][j+1] for i in range(4) for j in range(3))
report={'PASS':True,'states':729,'permutation_checks':count,'table_denominator':48,'N':N,'t':str(t),'top2':str(answer),'margin':str(F(1,2)-answer),'polynomial':list(map(str,coeff)),'method':'integer table enumeration and stdlib Fraction; independent of LP, quotient, scipy, and witness-best.json'}
(L/'finite-verification.json').write_text(json.dumps(report,indent=2));print(json.dumps(report))
