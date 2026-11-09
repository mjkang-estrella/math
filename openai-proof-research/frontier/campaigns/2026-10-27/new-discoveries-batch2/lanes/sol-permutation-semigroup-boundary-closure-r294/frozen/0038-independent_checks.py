from pathlib import Path
import json
from fractions import Fraction as Q
from itertools import permutations
L=Path(__file__).resolve().parent
r=json.loads((L/'checks-result.json').read_text());n=0
for z in r['valid']:
 a,b,c=z['triple'];A=z['apery'];N=max(A)+a+5
 d=[False]*(N+1);d[0]=True
 for j in range(1,N+1):d[j]=any(j>=g and d[j-g] for g in (a,b,c))
 assert A==[next(j for j in range(i,N+1,a) if d[j]) for i in range(a)]
 assert all(d[j]==(j>=A[j%a]) for j in range(N+1))
 p=[j for j in range(1,z['cutoff']+1) if d[j]]
 assert p[:3]==[a,b,c]
 assert all(len({j%3 for j in p[i:i+3]})==3 for i in range(0,len(p)-2,3))
 assert z['families'];n+=1
s=json.loads((L/'chambers-result-8.json').read_text());area=Q(0);tested=0
for raw in s['polygons']:
 p=[tuple(map(Q,v)) for v in raw]
 area+=abs(sum(x[0]*y[1]-x[1]*y[0] for x,y in zip(p,p[1:]+p[:1])))/2
 center=tuple(sum(v[j] for v in p)/len(p) for j in range(2))
 def value(f,q):return f[0]+f[1]*q[0]+f[2]*q[1]
 for f in s['hyperplanes']:
  vs=[value(f,v) for v in p];assert not min(vs)<0<max(vs)
 vals=sorted((value(f,center),f) for f in s['forms'] if value(f,center)<=8)
 assert len(set(v for v,f in vals))==len(vals)
 for R in permutations(range(3)):
  seq=[sum(f[j]*R[j] for j in range(3))%3 for v,f in vals]
  assert any(len(set(seq[i:i+3]))<3 for i in range(0,len(seq)-2,3));tested+=1
assert area==Q(1,2)
out=dict(apery_certificates_recomputed=n,chamber_residue_cases=tested,total_polygon_area=str(area),status='PASS',limitation='Polygon generator provides coverage construction; this check verifies area and no hyperplane crossing, not independent planar union computation.')
(L/'independent-result.json').write_text(json.dumps(out,indent=2));print(out)
