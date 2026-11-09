import random,time,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(122);rows=[]
def invariant(a,b,c,d,q):
 def vec(x):return (1,0) if x==q else (x,1)
 def det(x,y):x=vec(x);y=vec(y);return (x[0]*y[1]-x[1]*y[0])%q
 return det(a,c)*det(b,d)*pow(det(a,d)*det(b,c)%q,-1,q)%q
for q in [11,13,17,101,103,107,109]:
 start=time.monotonic();nodes=0;path=[q,0,1];used={q,0,1};colors=set();deadline=start+8
 def dfs():
  global nodes
  nodes+=1
  if nodes%1000==0 and time.monotonic()>deadline:return False
  if len(path)==q+1:return True
  choices=[x for x in range(q+1) if x not in used];rng.shuffle(choices)
  for d in choices:
   z=invariant(*path[-3:],d,q)
   if z in colors:continue
   path.append(d);used.add(d);colors.add(z)
   if dfs():return True
   colors.remove(z);used.remove(d);path.pop()
   if time.monotonic()>deadline:return False
  return False
 ok=dfs();row={'q':q,'success':ok,'nodes':nodes,'wall':time.monotonic()-start,'permutation_projective_infinity_is_q':path if ok else None}
 if ok:
  assert sorted(path)==list(range(q+1));assert len({invariant(*path[i:i+4],q) for i in range(q-2)})==q-2
 rows.append(row);print(row,flush=True)
(D/'outputs/sequencing.json').write_text(json.dumps(rows,indent=2))
