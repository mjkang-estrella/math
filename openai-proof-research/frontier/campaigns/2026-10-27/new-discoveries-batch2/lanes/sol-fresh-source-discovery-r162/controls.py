from pathlib import Path
import json,itertools,hashlib,re
from checks import adj,saturation,connected
L=Path(__file__).resolve().parent
ts=json.loads((L/'triangle-checks.json').read_text());out=[]
for rec in ts:
 k=rec['k'];es=[]
 for j,t in enumerate(rec['triples']):
  es += [(k+3*j+z,t[z]) for z in range(3)]
  es += [(k+3*j+u,k+3*j+v) for u,v in itertools.combinations(range(3),2)]
 a=adj(4*k,es);assert all(x.bit_count()==3 for x in a)
 if k<=4:assert saturation(a)==rec['s']
 out.append(dict(name=rec['name'],connected=connected(a),generic_crosscheck=k<=4))
def cycles(p):
 seen=set();c=0
 for u in range(len(p)):
  if u in seen:continue
  c+=1
  while u not in seen:seen.add(u);u=p[u]
 return c
es=[(0,1),(0,4),(1,2),(1,5),(1,6),(2,3),(3,4),(3,5),(4,6),(5,6)]
a=adj(7,es);co=[0]*8
for p in itertools.permutations(range(7)):
 if all(p[u]==u or a[u]>>p[u]&1 for u in range(7)):co[cycles(p)]+=1
assert co[1:]==[2,10,26,25,27,10,1]
cube=adj(8,[(u,u^(1<<b)) for u in range(8) for b in range(3) if u<(u^(1<<b))]);assert saturation(cube)==3
(L/'controls.json').write_text(json.dumps(dict(triangle=out,cube=dict(i=2,s=3,delta=3,perfect_matching_size=4),public_stirling_vector=co[1:],scope='Bounded method controls and reproduction of earlier public calculation; zero credit'),indent=2)+'\n')
print('triangle controls',len(out),'generic crosschecks',sum(x['generic_crosscheck'] for x in out),'public vector',co[1:])
