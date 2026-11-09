from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'MANIFEST.json').read_text())
assert 'MANIFEST.json' not in m and 'verification-receipt.json' not in m
assert set(m)=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']}
for f,x in m.items():assert h(L/f)==x['sha256'] and (L/f).stat().st_size==x['bytes'],f
b=json.loads((L/'source-bindings.json').read_text())['bindings']
for x in b:
 p=Path(x['copy'] if x['kind']=='administrative snapshot' else x['path']);assert h(p)==x['sha256'],str(p)
cached_bodies=json.loads((L/'cached-body-screen.json').read_text())
for x in cached_bodies:assert h(Path(x['path']))==x['sha256']
for line in (L/'access.jsonl').read_text().splitlines():
 x=json.loads(line)
 if 'sha256' in x:
  name='current-target.xml' if 'id_list=' in x['url'] else 'primary-successors.xml'
  assert h(L/name)==x['sha256']
d=json.loads((L/'diagnostics.json').read_text())
for v in d:
 p=v['p'];A=v['A'];N=len(A);r=v['r'];cert=v['incidence_certificate']
 if cert:
  assert all(sum(c*((mask>>i)&1) for mask,c in cert['rows'])%p==0 for i in range(N))
  rhs=[sum(c*(-sum(A[i][j] for i in range(N) if mask>>i&1)//p) for mask,c in cert['rows'])%p for j in range(r)]
  assert rhs==cert['rhs'] and any(rhs)
 poly=v['polynomial_certificate']
 if poly:
  S=poly['multiplier_mask'];j=poly['coordinate'];mom=[0]*N;val=0;num=0
  for mask in range(1,1<<N):
   if mask&S!=S:continue
   sums=[sum(A[i][k] for i in range(N) if mask>>i&1) for k in range(r)]
   if any(x%p for x in sums):continue
   num+=1;c=(-1)**mask.bit_count()
   for i in range(N):mom[i]+=c*((mask>>i)&1)
   val+=c*(sums[j]//p)
  assert all(x%p==0 for x in mom) and val%p==poly['carry_pairing'] and val%p and num==poly['number_rows']
receipt={'status':'PASS','at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':h(L/'MANIFEST.json'),'manifest_files':len(m),'source_bindings_verified':len(b),'cached_body_hashes_verified':len(cached_bodies),'incidence_and_polynomial_certificates':'independently recomputed from integer vectors','scope':'artifact integrity and exact finite certificates only; no universal theorem or novelty approval','separate_guarded_verification':True}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
