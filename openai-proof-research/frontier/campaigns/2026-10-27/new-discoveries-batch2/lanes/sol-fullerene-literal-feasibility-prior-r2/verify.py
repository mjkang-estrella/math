from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import json,hashlib,datetime
L=Path(__file__).parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def sub(a,b):return [x-y for x,y in zip(a,b)]
def cross(a,b):return [a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]]
freeze=json.loads((L/'freeze.json').read_text())
for r in freeze:assert h(Path(r['original']))==r['sha256']==h(L/r['copy']),r['original']
lib=json.loads((L/'mathlib-tree-bindings.json').read_text());M=Path(lib['root'])
assert (M/'.git/HEAD').read_text().strip()==lib['claimed_commit']
assert {str(p.relative_to(M)) for p in (M/'Mathlib').rglob('*.lean')}=={r['path'] for r in lib['files']}
for r in lib['files']:assert h(M/r['path'])==r['sha256'],r['path']
for file in ['mathlib-selected.json','mathlib-extra.json']:
 for r in json.loads((L/file).read_text()):assert h(L/'mathlib'/r['path'])==r['sha256']
cert=json.loads((L/'rational-realizations.json').read_text());results={}
S=L/'frozen/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-fullerene-heat-trace-breadth-depth-r286'
for name,c in cert.items():
 q=[[F(x) for x in p] for p in c['dual_vertices']];p=[[F(x) for x in v] for v in c['primal_vertices']];faces=c['dual_facets'];inc=c['primal_facets']
 assert len(q)==32 and len(p)==60 and len(set(map(tuple,q)))==32 and len(set(map(tuple,p)))==60
 assert all(sum(v[k] for v in q)==0 for k in range(3))
 assert any(dot(cross(sub(q[b],q[a]),sub(q[d],q[a])),sub(q[e],q[a])) for a,b,d,e in combinations(range(32),4))
 actual=[];triple_points=set()
 for tri in combinations(range(32),3):
  a,b,d=[q[i] for i in tri];normal=cross(sub(b,a),sub(d,a))
  if any(normal):
   ds=[dot(normal,sub(v,a)) for v in q]
   if min(ds)>=0 or max(ds)<=0:
    assert {i for i,x in enumerate(ds) if x==0}==set(tri);actual.append(tri)
  det=dot(a,cross(b,d))
  if det:
   bc,ca,ab=cross(b,d),cross(d,a),cross(a,b)
   v=[(bc[k]+ca[k]+ab[k])/det for k in range(3)]
   if all(dot(n,v)<=1 for n in q):triple_points.add(tuple(v))
 assert set(actual)=={tuple(sorted(f)) for f in faces}
 assert faces==json.loads((S/'graph-certificates.json').read_text())[name]['faces']
 assert triple_points==set(map(tuple,p))
 assert inc==[[j for j,v in enumerate(p) if dot(n,v)==1] for n in q]
 assert all(dot(n,v)<=1 for n in q for v in p)
 for j,f in enumerate(faces):
  assert {i for i,n in enumerate(q) if dot(n,p[j])==1}==set(f)
  assert dot(q[f[0]],cross(q[f[1]],q[f[2]]))!=0
 edges={tuple(sorted(e)) for e in json.loads((S/f'{name}-edges.json').read_text())}
 assert edges=={(i,j) for i,j in combinations(range(32),2) if len(set(inc[i])&set(inc[j]))==2}
 pedges={tuple(sorted(set(inc[i])&set(inc[j]))) for i,j in edges}
 assert len(pedges)==90
 assert all(sum(v in e for e in pedges)==3 for v in range(60))
 assert sorted(map(len,inc))==[5]*12+[6]*20
 for ids in inc:
  a,b,d=[p[i] for i in ids[:3]]
  assert any(any(cross(sub(p[j],a),sub(p[k],a))) for j,k in combinations(ids[1:],2))
  es=[e for e in pedges if set(e)<=set(ids)]
  assert len(es)==len(ids) and all(sum(i in e for e in es)==2 for i in ids)
  seen={ids[0]}
  for _ in ids:seen|={v for e in es if set(e)&seen for v in e}
  assert seen==set(ids)
 results[name]={'supporting_triangles':len(actual),'feasible_triple_vertices':len(triple_points),'primal_edges':len(pedges),'simple_cubic':True,'facet_cycles_5_6':True}
manifest=json.loads((L/'MANIFEST.json').read_text())
assert {str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p not in [L/'MANIFEST.json',L/'verification-receipt.json']}==set(manifest)
for path,d in manifest.items():assert h(L/path)==d['sha256'] and (L/path).stat().st_size==d['bytes'],path
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':h(L/'MANIFEST.json'),'files':len(manifest),'scientific_original_copy_bindings':len(freeze),'pinned_mathlib_files':len(lib['files']),'realizations':results,'Lean_executed':False,'counts_changed':False}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt))
