import pathlib,json,itertools,time
D=pathlib.Path(__file__).resolve().parents[1]
def surface(m,n,shift):
 def v(i,j):
  assert 0<=j<=n
  if j==n:i,j=-i+shift,0
  return j*m+i%m
 faces={tuple(sorted(t)) for i in range(m) for j in range(n) for t in [(v(i,j),v(i+1,j),v(i,j+1)),(v(i+1,j),v(i,j+1),v(i+1,j+1))]}
 # Use triangular grid with diagonal (1,-1); R preserves it.
 if len(faces)!=2*m*n or any(len(set(t))!=3 for t in faces):return None
 inc={}
 for f in faces:
  for e in itertools.combinations(f,2):inc.setdefault(e,[]).append(f)
 if any(len(z)!=2 for z in inc.values()):return None
 # Propagate a tentative simplicial automorphism from one oriented face.
 faces=sorted(faces);src=faces[0];orbit=set()
 for target in faces:
  for p in itertools.permutations(target):
   mp=dict(zip(src,p));rev=dict(zip(p,src));todo=[src];seen=set();ok=True
   while todo and ok:
    f=todo.pop()
    if f in seen:continue
    seen.add(f)
    for e in itertools.combinations(f,2):
     other=next(z for z in inc[e] if z!=f);out=next(x for x in other if x not in e)
     me=tuple(sorted(mp[x] for x in e));mf=tuple(sorted(mp[x] for x in f))
     if me not in inc or mf not in inc[me]:ok=False;break
     mo=next(z for z in inc[me] if z!=mf);y=next(x for x in mo if x not in me)
     if out in mp and mp[out]!=y or y in rev and rev[y]!=out:ok=False;break
     mp[out]=y;rev[y]=out;todo.append(other)
   if ok and len(mp)==m*n:orbit.add(target);break
 return {'vertices':m*n,'faces':len(faces),'base_face_orbit_size':len(orbit),'face_transitive':len(orbit)==len(faces)}
out=[]
for m,n in [(4,4),(5,6),(7,8),(17,41),(23,31)]:
 for shift in [0,1]:
  r=surface(m,n,shift)
  if r:out.append({'m':m,'n':n,'shift':shift,**r})
print(json.dumps({'cases':len(out),'face_transitive_cases':[r for r in out if r['face_transitive']],'orbit_sizes':sorted(set((r['faces'],r['base_face_orbit_size']) for r in out))}),flush=True)
(D/'outputs/klein-grid-search.json').write_text(json.dumps(out,indent=2))
