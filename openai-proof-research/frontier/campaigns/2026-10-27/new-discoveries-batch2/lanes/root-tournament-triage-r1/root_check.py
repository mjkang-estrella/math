"""Root independent rational check, using only the frozen CSV."""
import csv,json,itertools,math
from fractions import Fraction as Q
from pathlib import Path
D=Path(__file__).resolve().parent
rows=list(csv.reader((D/'witness-table.csv').open()))
assert rows[0]==['state_12_13_14_23_24_34','w1','w2','w3','w4']
table={}
for r in rows[1:]:
 s=tuple(map(int,r[0]));w=tuple(map(int,r[1:]))
 assert len(s)==6 and len(w)==4 and s not in table
 assert all(x in [0,1,2] for x in s)
 assert min(w)>=0 and sum(w)==48
 table[s]=w
assert set(table)==set(itertools.product(range(3),repeat=6))
edges=list(itertools.combinations(range(4),2));idx={e:k for k,e in enumerate(edges)}
sym=mono=0
for s,w in table.items():
 for p in itertools.permutations(range(4)):
  u=[-1]*6
  for k,(i,j) in enumerate(edges):
   a,b=p[i],p[j]
   u[idx[tuple(sorted((a,b)))]]=s[k] if a<b else 2-s[k]
  v=table[tuple(u)]
  assert all(v[p[i]]==w[i] for i in range(4));sym+=1
 for k,(i,j) in enumerate(edges):
  if s[k]<2:
   u=list(s);u[k]+=1;v=table[tuple(u)]
   assert v[i]>=w[i] and v[j]<=w[j];mono+=1
t=sum((Q(math.comb(32,k),2**32)*max(Q(1)-Q(k,16),Q(0)) for k in range(33)),Q(0))
assert t==Q(math.comb(32,16),2**33)==Q(300540195,4294967296)
weights=[t,1-2*t,t];S=Q(0)
for a,b,c,d in itertools.product(range(3),repeat=4):
 s=(a,2,2,b,c,d)
 S+=Q(sum(table[s][:2]),48)*weights[a]*weights[b]*weights[c]*weights[d]
assert S==Q(644305742079015272838458033019501771781,1361129467683753853853498429727072845824)
assert S<Q(1,2)
out={'status':'PASS','states':len(table),'permutation_checks':sym,'directed_neighbor_checks':mono,'binomial_t':str(t),'top_two_mass':str(S),'strict_gap':str(Q(1,2)-S),'scope':'Root independent finite checks; continuous interpolation and conditional honesty require ordinary argument, novelty not certified.'}
(D/'root-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
