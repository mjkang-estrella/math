from pathlib import Path,PurePosixPath
import json,hashlib,zipfile,stat,itertools
r=Path(__file__).resolve().parent.parent
# Unique fresh extraction; no archived script is executed.
z=r/'middle-source.zip'; target=r/'safe-extraction'; target.mkdir(exist_ok=False)
rows=[]
with zipfile.ZipFile(z) as f:
 names=f.namelist();assert len(set(names))==len(names)
 for info in f.infolist():
  p=PurePosixPath(info.filename)
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in info.filename
  assert not stat.S_ISLNK(info.external_attr>>16)
  out=target.joinpath(*p.parts); assert out.resolve().is_relative_to(target.resolve())
  if info.is_dir():out.mkdir(parents=True,exist_ok=True);continue
  data=f.read(info);out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(data)
  assert out.read_bytes()==data
  rows.append({'member':info.filename,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)})
(r/'receipts/safe-extraction.json').write_text(json.dumps({'pass':True,'archive_sha256':hashlib.sha256(z.read_bytes()).hexdigest(),'members':rows,'executed':False},indent=2)+'\n')
# Independent literal construction, all subsets through first feasible size.
e=[(0,1),(0,6),(1,6),(2,3),(2,7),(3,7),(4,6),(4,7),(5,6),(5,7),(6,7)]
a=[set() for _ in range(8)]
for u,v in e:a[u].add(v);a[v].add(u)
m=[set() for _ in range(19)]
for i,(u,v) in enumerate(e):
 for w in (u,v):m[w].add(8+i);m[8+i].add(w)
 for j,f in enumerate(e):
  if i!=j and set((u,v))&set(f):m[8+i].add(8+j)
def good(adj,S,empty):
 allv=set(range(len(adj))); covered=set(S)
 for v in S:covered.update(adj[v])
 if covered!=allv:return False
 rem=allv-set(S)
 if not rem:return empty
 seen={next(iter(rem))}; todo=list(seen)
 while todo:
  for v in adj[todo.pop()]&rem-seen:seen.add(v);todo.append(v)
 return seen==rem
def minimum(adj,empty):
 for k in range(len(adj)+1):
  witnesses=[list(s) for s in itertools.combinations(range(len(adj)),k) if good(adj,set(s),empty)]
  if witnesses:return {'value':k,'minimizers':witnesses}
result={str(c):{'G8':minimum(a,c),'middle':minimum(m,c)} for c in [True,False]}
for c in result.values():
 assert c['G8']['value']==c['middle']['value']==4
 assert len(c['G8']['minimizers'])==8 and len(c['middle']['minimizers'])==2
assert sum(map(len,m))//2==48
(r/'receipts/witness-check.json').write_text(json.dumps({'pass':True,'middle_order':19,'middle_edges':48,'results':result,'full_classification_rerun':False},indent=2)+'\n')
print('Safe extraction and independent witness checks PASS')
