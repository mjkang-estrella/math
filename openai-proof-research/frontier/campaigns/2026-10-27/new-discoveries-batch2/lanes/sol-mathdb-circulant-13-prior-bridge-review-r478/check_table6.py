"""Local audit of KHS Table 6, not the circulant endpoint certificate.
Arc deletion uses only binary necessary constraints, hence is sound for all extensions.
"""
import json,pathlib,itertools
O=pathlib.Path(__file__).resolve().parent
V=[(i,j) for i in range(3) for j in range(-4,18)]
E={u:[] for u in V}
for u in V:
 for v in V:
  d=abs(u[0]-v[0])+abs(u[1]-v[1])
  if 1<=d<=3:E[u].append((v,d))
def propagate(seed):
 D={v:set(range(12)) for v in V}
 for v,a in seed.items():D[v]={a}
 changed=True
 while changed:
  changed=False
  for u in V:
   for v,d in E[u]:
    S={a for a in D[u] if any(abs(a-b)>=4-d and (d!=1 or abs(a-b)<=9) for b in D[v])}
    if not S:return None
    if S!=D[u]:D[u]=S;changed=True
 return D
cases=[(3,5,7,9),(3,7,5,9),(3,9,5,7),(7,9,3,5),(5,9,3,7),(5,7,3,9)]
results=[]
for k,(top,bot,left,right) in enumerate(cases,1):
 seed={(1,0):0,(0,0):top,(2,0):bot,(1,-1):left,(1,1):right}
 D=propagate(seed)
 r={'case':k,'contradiction':D is None}
 if k in (3,6):
  assert D is not None
  p=12 if k==3 else 4
  # All cells of an entire period and both starting/returning crosses forced.
  target={(i,j) for i in range(3) for j in range(-1,p+1)}|{(1,p+1)}
  assert all(len(D[v])==1 for v in target)
  a,b=( -3,7) if k==3 else (-5,-3)
  assert all(next(iter(D[i,j]))==(top+a*i+b*j)%12 for i,j in target)
  assert all(D[i,j]==D[i,j+p] for i,j in seed)
  r.update(period=p,forced=[[i,j,next(iter(D[i,j]))] for i,j in sorted(target)])
 else:
  if D is not None:
   split=(2,1) if k==2 else (0,-1)
   r['split']=[*split];r['split_domain']=sorted(D[split])
   r['branch_contradictions']=[propagate(dict(seed,**{} ) | {split:a}) is None for a in sorted(D[split])]
   assert all(r['branch_contradictions'])
 results.append(r)
# Table 5 completeness: 24 permutations / horizontal and vertical reflections.
reps=set()
for t,b,l,r in itertools.permutations([3,5,7,9]):
 reps.add(min((t,b,l,r),(b,t,l,r),(t,b,r,l),(b,t,r,l)))
assert reps=={min((t,b,l,r),(b,t,l,r),(t,b,r,l),(b,t,r,l)) for t,b,l,r in cases}
(O/'table6-results.json').write_text(json.dumps({'status':'PASS','cases':results,'neighborhood_orbits':len(reps)},indent=2)+'\n')
print('PASS: all six neighborhood orbits; four contradictions; two forced repeat crosses and complete periods')
