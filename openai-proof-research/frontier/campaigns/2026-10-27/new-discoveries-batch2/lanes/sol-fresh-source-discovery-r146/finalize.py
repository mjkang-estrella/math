import json,hashlib,datetime,sys
from pathlib import Path
L=Path(__file__).resolve().parent;B=L.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def rec(p):
 b=p.read_bytes();return dict(path=str(p.relative_to(L)),bytes=len(b),sha256=sha(b))
def save(n,j):(L/n).write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
if len(sys.argv)==1:
 guard=B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
 assert sha(guard.read_bytes())=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
 http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
 for r in http:
  if 'sha256' in r:assert sha((L/'sources'/r['name']).read_bytes())==r['sha256']
 # Context is explicitly separate from scientific evidence.
 science=[p for p in L.rglob('*') if p.is_file() and (p.parts[-2]=='sources' or p.name in {'PROOF.md','checks.py','checks.json','chronology.json'})]
 save('scientific-freeze.json',dict(utc=utc(),status='EXCLUDED_PRIOR_FULL_PUBLIC_PROOF',files=[rec(p) for p in sorted(science)],exclusions='Mutable NEXT operational context, context snapshots, lexical history and generated final manifests are outside this scientific freeze.'))
 save('provenance.json',dict(lane=str(L),completed_utc=utc(),status='EXCLUDED',eligible_discoveries=0,counts_unchanged=dict(additional=9,total=39,next=40),source=dict(id='2607.03582v1',authors=['Matthieu Fradelizi','Auttawich Manui','Mark Meyer','Cheikh Saliou Ndiaye'],target='Conjecture 5, printed p39; full planar symmetric convex-body equality classification for every finite p>1'),prior=dict(author='Kenta Kitamura',repository='https://github.com/KitaKen1/lp-rogers-shephard-conjectures-lean',revision='c646c668c0568b8533bf5534abcf02aab4d2df72',commit_utc='2026-08-16T01:38:11Z',body_checked=True,own_kernel_replay=False),http=http,guard=dict(path=str(guard),sha256=sha(guard.read_bytes()),AS_bytes=512*1024**2,sampled_group_RSS_bytes=512*1024**2,CPU_seconds=210,wall_seconds=230,sampling_ms=40,OPENBLAS_NUM_THREADS=1,OMP_NUM_THREADS=1,PYTHONDONTWRITEBYTECODE=1,caps_raised=False,sampling_limit='Unsampled RSS transients not excluded'),context=[rec(L/('context-'+n)) for n in ['ledger.json','prior-campaign-context.json','NEXT.md']],history_receipts=[rec(p) for p in sorted(L.glob('history-*.json'))],registry=dict(omega_fixed='490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c',openai_fixed='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',both_latest_compare_lists_capped_300=True,semantic_clearance=False,head_chasing=False),limits=['Jin-Yuan publisher PDF 403, body unread','No independent review of own ordinary proof','No transitive kernel replay of public proof','Two malformed-ref 404 calls preserved','Current registry full semantic coverage not closed','No worldwide novelty claim'],actions=dict(children=False,git=False,shared_edits=False,public_actions=False,browser_tabs=False,authored_lean=False,manuscript=False)))
 exclude={'finalmanifest.json','manifest-verification.json'}
 paths=sorted(p for p in L.rglob('*') if p.is_file() and p.name not in exclude)
 save('finalmanifest.json',dict(utc=utc(),files=[rec(p) for p in paths],exclusions=sorted(exclude),scope='All lane payload files, including separate mutable-context snapshots; no self-hash.'))
j=json.loads((L/'finalmanifest.json').read_bytes());errors=[]
for r in j['files']:
 p=L/r['path']
 if not p.is_file() or rec(p)!=r:errors.append(r['path'])
science=json.loads((L/'scientific-freeze.json').read_bytes())
for r in science['files']:
 if rec(L/r['path'])!=r:errors.append('science:'+r['path'])
assert not errors,errors
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in j['exclusions']}
assert actual=={r['path'] for r in j['files']}
save('manifest-verification.json',dict(utc=utc(),status='PASS',payload_files=len(j['files']),science_files=len(science['files']),manifest_sha256=sha((L/'finalmanifest.json').read_bytes()),errors=errors))
print('PASS',len(j['files']),'manifest payloads;',len(science['files']),'scientific files')
