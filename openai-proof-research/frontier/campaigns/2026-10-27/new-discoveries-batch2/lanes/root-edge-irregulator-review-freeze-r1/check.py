import hashlib,json,itertools,datetime
from pathlib import Path
here=Path(__file__).resolve().parent
src=here.parent/'sol-fresh-source-discovery-r70'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
frozen={str(p.relative_to(src)):sha(p) for p in sorted(src.rglob('*')) if p.is_file() and '__pycache__' not in p.parts}
prov=json.loads((src/'provenance.json').read_text())
manifest=next(v for k,v in prov.items() if isinstance(v,dict) and 'PROOF.md' in v)
mismatches=[p for p,h in manifest.items() if sha(src/p)!=h]
assert set(mismatches)<= {'finalize.log','finalize-guard.json'},mismatches
diamond=[(0,1),(0,2),(0,3),(1,2),(1,3)]
local=0
for epsilon in (0,1):
 for bits in range(32):
  edges=[e for j,e in enumerate(diamond) if bits>>j&1]
  deg=[0]*4; deg[2]=epsilon
  for u,v in edges: deg[u]+=1;deg[v]+=1
  if all(deg[u]!=deg[v] for u,v in edges): assert 5-len(edges)>=2
  local+=1
def graph(t):
 edges=[]
 for i in range(t):
  a,b,c,d,x,y=range(1+6*i,7+6*i)
  edges += [(a,b),(a,c),(a,d),(b,c),(b,d),(c,x),(x,y),(y,0)]
 return edges
def good(edges,n):
 deg=[0]*n
 for u,v in edges: deg[u]+=1;deg[v]+=1
 return all(deg[u]!=deg[v] for u,v in edges)
E=graph(2);best=16;minimizers=0
for bits in range(1<<16):
 kept=[e for j,e in enumerate(E) if bits>>j&1]
 removed=16-len(kept)
 if removed>best: continue
 if good(kept,13):
  if removed<best: best=removed;minimizers=0
  minimizers+=1
assert best==6
for t in range(2,101):
 E=graph(t);assert len(E)==len(set(E))==8*t
 assert good([e for j,e in enumerate(E) if j%8 not in (0,2,6)],6*t+1)
 seen={0}
 while True:
  new=seen|{v for u,v in E if u in seen}|{u for u,v in E if v in seen}
  if new==seen: break
  seen=new
 assert len(seen)==6*t+1
assert all(sha(src/p)==h for p,h in frozen.items())
(here/'review-freeze.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_lane':str(src),'files':frozen},indent=2)+'\n')
result={'status':'PASS','local_diamond_states':local,'literal_t2_all_subsets':65536,'minimum':best,'minimizers':minimizers,'upper_connectivity_t_range':[2,100],'manifest_entries':len(manifest),'manifest_mismatches':mismatches,'frozen_files':len(frozen),'scope':'Independent exact corroboration; ordinary all-t proof read separately. No formal or novelty PASS.'}
(here/'root-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
