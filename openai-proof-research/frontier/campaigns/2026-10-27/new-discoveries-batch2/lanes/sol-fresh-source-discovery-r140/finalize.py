import json,hashlib,datetime,sys
from pathlib import Path
L=Path(__file__).resolve().parent;B=L.parents[1];R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def rec(f):
 b=f.read_bytes();return dict(bytes=len(b),sha256=sha(b))
def save(n,j):(L/n).write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
utc=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
excluded={'finalmanifest.json','manifest-verification.json'}
if len(sys.argv)==1 or sys.argv[1]=='seal':
 http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
 deps={}
 for f in [R/'AGENTS.md',B/'AGENTS.md',L.parent/'sol-fresh-source-discovery-r137/history-receipt.json',L.parent/'sol-fresh-source-discovery-r137/registry-delta-receipt.json',L.parent/'sol-fresh-source-discovery-r133/history-aliases.jsonl.gz',L.parent/'root-frank-attenuation-exclusion-r1/DECISION.md',L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',R/'sources/upstream.json']:
  deps[str(f)]=rec(f)
 assert deps[str(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')]['sha256']=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
 h=json.loads((L/'history-expanded.json').read_text());d=json.loads((L/'registry-relevant-tree-delta.json').read_text())
 bindings=[]
 for x in d['changed']:
  n={'Blueprint/D5/S3/Topology/SphereOrthogonalityCover.md':'omega-topology.md','Blueprint/D5/S3/Topology/SphereBrouwerObstruction.md':'omega-brouwer.md','Library/Topology/feldmanwilce2026spherecovers.md':'omega-library.md'}[x['path']]
  b=(L/'sources'/n).read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==x['new'];bindings.append(dict(path=x['path'],local=n,git_blob_sha1=blob,sha256=sha(b)))
 assert (L/'sources/bellec.pdf').read_bytes()==(L/'sources/bellec-v5.pdf').read_bytes()
 for r in http:
  if 'sha256' in r:assert rec(L/'sources'/r['name'])==dict(bytes=r['bytes'],sha256=r['sha256'])
 save('provenance.json',dict(lane=str(L),sealed_utc=utc(),status='UNRESOLVED; zero nominees',credit=0,counts=dict(additional=9,total=39,next=40),target='Bellec–Fritz arXiv2412.15179v5 Conjecture5.1',http=http,sources={str(f.relative_to(L)):rec(f) for f in sorted((L/'sources').iterdir())},dependencies=deps,history=dict(complete_unique_bodies=h['complete_bodies'],paths=h['paths'],matching_paths=len(h['hits']),missing=h['missing'],new_or_changed=len(h['new_or_changed']),cutoff=None,scope_limits=h['limits']),registry_markdown_blob_bindings=bindings,registry_limits=d['limits'],guard=dict(AS_MiB=512,group_RSS_MiB=512,CPU_seconds=210,wall_seconds=230,sampling_nominal_ms=40,environment=dict(OPENBLAS_NUM_THREADS=1,OMP_NUM_THREADS=1,PYTHONDONTWRITEBYTECODE=1),failure_preserved='checks-first-failure.log',sampling_limits='40ms sampled process-group RSS/CPU can miss short peaks and escaped processes; RLIMIT_AS and CPU are per-process too.'),access_limits=['publisher403: full published body unread','v6 abs/PDF404 despite metadata comment','unused author/publications404','source text extraction typography limitations','initial shell output truncation not used for absence','initial OpenBLAS import allocation failure','ordinary Omega comparison300-file cap; narrowed tree closure only','retained historic semantic/format gaps','no worldwide priority claim'],gates=dict(full_source_resolution=False,published_body_comparison=False,ordinary_proof=False,prior_art='bounded only',Lean='not authorized or attempted',paper='not authorized or attempted')))
 scientific={str(f.relative_to(L)):rec(f) for f in sorted(L.rglob('*')) if f.is_file() and f.name not in excluded|{'scientific-freeze.json','context-NEXT.md'}}
 save('scientific-freeze.json',dict(utc=utc(),files=scientific,mutable_planning_snapshot_excluded='context-NEXT.md',limits='Freezes local bytes, not mathematical validity. Original external NEXT may change.'))
 files={str(f.relative_to(L)):rec(f) for f in sorted(L.rglob('*')) if f.is_file() and f.name not in excluded}
 save('finalmanifest.json',dict(utc=utc(),algorithm='sha256',files=files,excluded_self_and_receipt=sorted(excluded),contract='Complete lane regular-file inventory except this manifest and its generated verification receipt; all writes remain within lane.'))
j=json.loads((L/'finalmanifest.json').read_text());actual={str(f.relative_to(L)):rec(f) for f in sorted(L.rglob('*')) if f.is_file() and f.name not in excluded}
assert actual==j['files'];assert not any(f.is_symlink() for f in L.rglob('*'))
s=json.loads((L/'scientific-freeze.json').read_text())
for n,r in s['files'].items():assert rec(L/n)==r
assert 'context-NEXT.md' not in s['files'];assert 'context-NEXT.md' in actual
assert not (L/'PROOF.md').exists()
v=dict(utc=utc(),status='PASS',manifest_sha256=sha((L/'finalmanifest.json').read_bytes()),manifest_entries=len(actual),scientific_entries=len(s['files']),inventory_exact=True,all_hashes_verified=True,symlinks=False,mutable_NEXT_separate=True)
save('manifest-verification.json',v);print(json.dumps(v))
