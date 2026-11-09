import csv,itertools,math,json
from fractions import Fraction as F
from pathlib import Path
L=Path(__file__).resolve().parent
edges=list(itertools.combinations(range(4),2));T={}
for r in csv.DictReader((L/'frozen/witness-table.csv').open()):
 s=tuple(map(int,r['state_12_13_14_23_24_34']));assert s not in T
 T[s]=tuple(int(r['w'+str(i+1)]) for i in range(4))
assert set(T)==set(itertools.product(range(3),repeat=6))
ns=nn=0
for s,w in T.items():
 assert min(w)>=0 and sum(w)==48
 for p in itertools.permutations(range(4)):
  a=[None]*6
  for k,(i,j) in enumerate(edges):
   u,v=p[i],p[j];z=s[k]
   if u>v:u,v,z=v,u,2-z
   a[edges.index((u,v))]=z
  assert all(T[tuple(a)][p[i]]==w[i] for i in range(4));ns+=1
 for k,(i,j) in enumerate(edges):
  if s[k]<2:
   a=list(s);a[k]+=1;v=T[tuple(a)]
   assert v[i]>=w[i] and v[j]<=w[j];nn+=1
t=sum((F(math.comb(32,k),2**32)*max(1-F(k,16),0) for k in range(33)),F(0))
assert t==F(math.comb(32,16),2**33)
mass=F(0);poly=[F(0)]*5;terms=0
for a in itertools.product(range(3),repeat=4):
 s=(a[0],2,2,a[1],a[2],a[3]);v=F(sum(T[s][:2]),48)
 weight=math.prod(t if z!=1 else 1-2*t for z in a)
 mass+=v*weight;terms+=1
 c=[v]
 for z in a:
  d=[F(0)]*(len(c)+1)
  for k,x in enumerate(c):
   if z==1:d[k]+=x;d[k+1]-=2*x
   else:d[k+1]+=x
  c=d
 for k,x in enumerate(c):poly[k]+=x
assert mass==F(644305742079015272838458033019501771781,1361129467683753853853498429727072845824)<F(1,2)
assert poly==list(map(F,['1/4','15/4','-17/2','185/24','-11/4']))
P=[[F(1,2),F(1,2),1,1],[F(1,2)]*4,[0,F(1,2),F(1,2),F(1,2)],[0,F(1,2),F(1,2),F(1,2)]]
assert all(P[i][j]+P[j][i]==1 for i in range(4) for j in range(4))
assert all(P[i][j]<=P[i][j+1] for i in range(4) for j in range(3))
assert all(P[i][j]>=P[i+1][j] for i in range(3) for j in range(4))
# Independent finite check of source digraph rules, including parallel-arc exception.
opts=[]
for i in range(4):opts.append([(a,b) for a in range(i+1) for b in range(a,i+1) if a!=b or a in (0,i)])
mins=[]
for g in itertools.product(*opts):mins.append(sum(j<2 for pair in g for j in pair))
assert min(mins)==4
out={'states':len(T),'permutations':ns,'neighbors':nn,'t':str(t),'polynomial':list(map(str,poly)),'mass':str(mass),'gap':str(F(1,2)-mass),'terms':terms,'source_digraphs':len(mins),'minimum_top2_indegree':min(mins),'matrix_doubly_monotonic':True,'result':'PASS'}
(L/'independent-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
